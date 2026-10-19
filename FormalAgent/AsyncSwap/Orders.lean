import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# AsyncSwap order escrow accounting

Model of the order book in `protocol/src/AsyncSwap.sol` and
`protocol/src/libraries/AsyncFiller.sol` at e230f5b, restricted to the input leg: what the
hook escrows when an order is opened and what leaves escrow on fill or cancel.

* `AsyncFiller.OrderInfo` is `{amountIn, amountOutMin}` (AsyncFiller.sol:26-29). A slot with
  `amountIn = 0` is an absent order; `delete` writes `{0, 0}`.
* `create` mirrors `_beforeSwap` + `_createOrder` (AsyncSwap.sol:271-327): the whole
  `amountTaken` is taken as 6909 claims (`take(..., true)`, :288), the guard is
  `amountIn != 0 && amountOutMin != 0` (:307), and the collision walk (:320-323) only lands on a
  slot with `amountIn == 0`.
* `fill` mirrors `AsyncFiller.fill` (:94-130): reverts on `amountIn == 0` (:108), deletes the
  record (:113), burns `amountIn` of input claims and pays exactly `amountIn` to the filler
  (:127-128). v1 is full-fill only, so there is no partial-fill rounding on the input leg.
* `cancel` mirrors `AsyncFiller.cancel` (:136-155): same guard, delete, and pays exactly
  `amountIn` back to `order.owner` (:151-152).
* `updatePrice` mirrors `AsyncFiller.updatePrice` (:71-85): only `amountOutMin` changes.

Authorization checks are left out: every transition is allowed to any caller, so the
accounting theorems hold for a superset of the reachable behaviours.

Modelling assumptions. An order id determines its input currency: the id preimage
(`AsyncOrderLibrary.orderId`, AsyncOrder.sol:47-49) contains the pool id and `zeroForOne`, and
the input currency is `zeroForOne ? currency0 : currency1` of that pool (AsyncFiller.sol:110,
146). We take keccak as injective, so `inp : Id → Cur` is a fixed function. Amounts are `Nat`;
`uint256` overflow in the counters is not modelled (the PoolManager's own accounting would
revert first).
-/

namespace AsyncSwap.Orders

/-- `AsyncFiller.OrderInfo`. -/
structure OrderInfo where
  amountIn : Nat
  amountOutMin : Nat

/-- One pool manager's view of the hook's escrow. `live` is the set of open order ids (ghost);
`deposited`, `filled`, `refunded` are ghost counters per input currency. -/
structure State (Id Cur : Type) where
  orders : Id → OrderInfo
  live : Finset Id
  deposited : Cur → Nat
  filled : Cur → Nat
  refunded : Cur → Nat

variable {Id Cur : Type} [DecidableEq Id] [DecidableEq Cur]

/-- Empty book after deployment. -/
def init : State Id Cur :=
  { orders := fun _ => ⟨0, 0⟩, live := ∅, deposited := fun _ => 0, filled := fun _ => 0,
    refunded := fun _ => 0 }

/-- Open order at `id` (AsyncSwap.sol:288, :307, :320-325). -/
def create (inp : Id → Cur) (s : State Id Cur) (id : Id) (amountIn amountOutMin : Nat) :
    Option (State Id Cur) :=
  if amountIn ≠ 0 ∧ amountOutMin ≠ 0 ∧ (s.orders id).amountIn = 0 then
    some { s with
      orders := Function.update s.orders id ⟨amountIn, amountOutMin⟩
      live := insert id s.live
      deposited := Function.update s.deposited (inp id) (s.deposited (inp id) + amountIn) }
  else none

/-- Fill the order at `id` in full (AsyncFiller.sol:108, :113, :127-128). -/
def fill (inp : Id → Cur) (s : State Id Cur) (id : Id) : Option (State Id Cur) :=
  if (s.orders id).amountIn ≠ 0 then
    some { s with
      orders := Function.update s.orders id ⟨0, 0⟩
      live := s.live.erase id
      filled := Function.update s.filled (inp id) (s.filled (inp id) + (s.orders id).amountIn) }
  else none

/-- Cancel the order at `id` (AsyncFiller.sol:144, :147, :151-152). -/
def cancel (inp : Id → Cur) (s : State Id Cur) (id : Id) : Option (State Id Cur) :=
  if (s.orders id).amountIn ≠ 0 then
    some { s with
      orders := Function.update s.orders id ⟨0, 0⟩
      live := s.live.erase id
      refunded :=
        Function.update s.refunded (inp id) (s.refunded (inp id) + (s.orders id).amountIn) }
  else none

/-- Change the limit price of the order at `id` (AsyncFiller.sol:79-83). -/
def updatePrice (s : State Id Cur) (id : Id) (newAmountOutMin : Nat) : Option (State Id Cur) :=
  if newAmountOutMin ≠ 0 ∧ (s.orders id).amountIn ≠ 0 then
    some { s with
      orders := Function.update s.orders id ⟨(s.orders id).amountIn, newAmountOutMin⟩ }
  else none

/-- Input of currency `c` still escrowed for open orders. -/
def openAmt (inp : Id → Cur) (s : State Id Cur) (c : Cur) : Nat :=
  ∑ i ∈ s.live, if inp i = c then (s.orders i).amountIn else 0

/-- Paid out of escrow in currency `c`: to fillers plus back to makers. -/
def paidOut (s : State Id Cur) (c : Cur) : Nat := s.filled c + s.refunded c

/-- The ghost set `live` is exactly the set of non-empty slots. -/
def WF (s : State Id Cur) : Prop := ∀ i, i ∈ s.live ↔ (s.orders i).amountIn ≠ 0

/-- Escrow conservation: for every input currency, deposited = filled + refunded + open. -/
def Inv (inp : Id → Cur) (s : State Id Cur) : Prop :=
  WF s ∧ ∀ c, s.deposited c = s.filled c + s.refunded c + openAmt inp s c

/-- A single step of the order book. -/
inductive Step (inp : Id → Cur) : State Id Cur → State Id Cur → Prop
  | create (s s' : State Id Cur) (id : Id) (a b : Nat) :
      create inp s id a b = some s' → Step inp s s'
  | fill (s s' : State Id Cur) (id : Id) : fill inp s id = some s' → Step inp s s'
  | cancel (s s' : State Id Cur) (id : Id) : cancel inp s id = some s' → Step inp s s'
  | updatePrice (s s' : State Id Cur) (id : Id) (p : Nat) :
      updatePrice s id p = some s' → Step inp s s'

/-- Summing over a set that avoids `id` does not see an update at `id`. -/
private theorem sum_update_of_not_mem (inp : Id → Cur) (c : Cur) (t : Finset Id)
    (f : Id → OrderInfo) (id : Id) (v : OrderInfo) (h : id ∉ t) :
    (∑ i ∈ t, if inp i = c then (Function.update f id v i).amountIn else 0) =
      ∑ i ∈ t, if inp i = c then (f i).amountIn else 0 := by
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ id := fun e => h (e ▸ hi)
  simp only [Function.update_apply, hne, if_false]

omit [DecidableEq Id] in
theorem init_inv(inp : Id → Cur) : Inv inp (init : State Id Cur) := by
  refine ⟨fun i => ?_, fun c => ?_⟩
  · simp [init]
  · simp [init, openAmt]

theorem create_inv (inp : Id → Cur) (s s' : State Id Cur) (id : Id) (a b : Nat)
    (hI : Inv inp s) (h : create inp s id a b = some s') : Inv inp s' := by
  obtain ⟨hwf, hc⟩ := hI
  unfold create at h
  split_ifs at h with hg
  obtain ⟨ha, -, h0⟩ := hg
  cases h
  have hnot : id ∉ s.live := fun hm => (hwf id).1 hm h0
  refine ⟨fun i => ?_, fun c => ?_⟩
  · by_cases hi : i = id
    · subst hi; simp [ha]
    · simp [Function.update_apply, hi, hwf i]
  · have hs := hc c
    simp only [openAmt] at hs ⊢
    rw [Finset.sum_insert hnot, sum_update_of_not_mem inp c s.live s.orders id _ hnot]
    simp only [Function.update_apply, if_true]
    by_cases hic : inp id = c
    · subst hic; simp only [if_true]; omega
    · have : c ≠ inp id := fun e => hic e.symm
      simp only [hic, this, if_false]; omega

/-- Shared step for `fill` and `cancel`: removing `id` from the book. -/
private theorem openAmt_erase (inp : Id → Cur) (s : State Id Cur) (id : Id) (c : Cur)
    (hm : id ∈ s.live) :
    openAmt inp s c =
      (if inp id = c then (s.orders id).amountIn else 0) +
        ∑ i ∈ s.live.erase id,
          if inp i = c then (Function.update s.orders id ⟨0, 0⟩ i).amountIn else 0 := by
  rw [sum_update_of_not_mem inp c _ s.orders id _ (Finset.notMem_erase id s.live)]
  exact (Finset.add_sum_erase s.live _ hm).symm

theorem fill_inv (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (hI : Inv inp s) (h : fill inp s id = some s') : Inv inp s' := by
  obtain ⟨hwf, hc⟩ := hI
  unfold fill at h
  split_ifs at h with hg
  cases h
  have hm : id ∈ s.live := (hwf id).2 hg
  refine ⟨fun i => ?_, fun c => ?_⟩
  · by_cases hi : i = id
    · subst hi; simp
    · simp [Function.update_apply, hi, hwf i]
  · have hs := hc c
    have he := openAmt_erase inp s id c hm
    simp only [openAmt] at hs he ⊢
    simp only [Function.update_apply] at he ⊢
    by_cases hic : inp id = c
    · subst hic; simp only [if_true] at he ⊢; omega
    · have : c ≠ inp id := fun e => hic e.symm
      simp only [hic, this, if_false] at he ⊢; omega

theorem cancel_inv (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (hI : Inv inp s) (h : cancel inp s id = some s') : Inv inp s' := by
  obtain ⟨hwf, hc⟩ := hI
  unfold cancel at h
  split_ifs at h with hg
  cases h
  have hm : id ∈ s.live := (hwf id).2 hg
  refine ⟨fun i => ?_, fun c => ?_⟩
  · by_cases hi : i = id
    · subst hi; simp
    · simp [Function.update_apply, hi, hwf i]
  · have hs := hc c
    have he := openAmt_erase inp s id c hm
    simp only [openAmt] at hs he ⊢
    simp only [Function.update_apply] at he ⊢
    by_cases hic : inp id = c
    · subst hic; simp only [if_true] at he ⊢; omega
    · have : c ≠ inp id := fun e => hic e.symm
      simp only [hic, this, if_false] at he ⊢; omega

theorem updatePrice_inv (inp : Id → Cur) (s s' : State Id Cur) (id : Id) (p : Nat)
    (hI : Inv inp s) (h : updatePrice s id p = some s') : Inv inp s' := by
  obtain ⟨hwf, hc⟩ := hI
  unfold updatePrice at h
  split_ifs at h with hg
  cases h
  have hsame : ∀ i, ((Function.update s.orders id ⟨(s.orders id).amountIn, p⟩) i).amountIn =
      (s.orders i).amountIn := by
    intro i
    by_cases hi : i = id
    · subst hi; simp
    · simp [Function.update_apply, hi]
  refine ⟨fun i => ?_, fun c => ?_⟩
  · simp only [hsame]; exact hwf i
  · simp only [openAmt, hsame]; exact hc c

theorem step_inv (inp : Id → Cur) {s s' : State Id Cur} (hI : Inv inp s) (h : Step inp s s') :
    Inv inp s' := by
  cases h with
  | create id a b h => exact create_inv inp s s' id a b hI h
  | fill id h => exact fill_inv inp s s' id hI h
  | cancel id h => exact cancel_inv inp s s' id hI h
  | updatePrice id p h => exact updatePrice_inv inp s s' id p hI h

/-- Every state reachable from deployment satisfies escrow conservation. -/
theorem reachable_inv (inp : Id → Cur) {s : State Id Cur}
    (h : Relation.ReflTransGen (Step inp) init s) : Inv inp s := by
  induction h with
  | refl => exact init_inv inp
  | tail _ hstep ih => exact step_inv inp ih hstep

/-- Headline: in every reachable state and every input currency,
deposited = filled + refunded + still open. -/
theorem escrow_conservation (inp : Id → Cur) {s : State Id Cur}
    (h : Relation.ReflTransGen (Step inp) init s) (c : Cur) :
    s.deposited c = s.filled c + s.refunded c + openAmt inp s c :=
  (reachable_inv inp h).2 c

/-- No sequence of fills, cancels and price updates pays out more input than was deposited. -/
theorem paidOut_le_deposited (inp : Id → Cur) {s : State Id Cur}
    (h : Relation.ReflTransGen (Step inp) init s) (c : Cur) :
    paidOut s c ≤ s.deposited c := by
  have := escrow_conservation inp h c
  unfold paidOut; omega

/-- Per order: a fill or cancel moves exactly the stored `amountIn` out of escrow. -/
theorem fill_pays_amountIn (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (h : fill inp s id = some s') :
    s'.filled (inp id) = s.filled (inp id) + (s.orders id).amountIn := by
  unfold fill at h
  split_ifs at h
  cases h
  simp

theorem cancel_pays_amountIn (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (h : cancel inp s id = some s') :
    s'.refunded (inp id) = s.refunded (inp id) + (s.orders id).amountIn := by
  unfold cancel at h
  split_ifs at h
  cases h
  simp

/-- No double spend: once an order is filled, it can be neither filled nor cancelled again. -/
theorem fill_then_fill_none (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (h : fill inp s id = some s') : fill inp s' id = none ∧ cancel inp s' id = none := by
  unfold fill at h
  split_ifs at h
  cases h
  simp [fill, cancel]

/-- No double refund: once an order is cancelled, it can be neither filled nor cancelled again. -/
theorem cancel_then_none (inp : Id → Cur) (s s' : State Id Cur) (id : Id)
    (h : cancel inp s id = some s') : fill inp s' id = none ∧ cancel inp s' id = none := by
  unfold cancel at h
  split_ifs at h
  cases h
  simp [fill, cancel]

end AsyncSwap.Orders
