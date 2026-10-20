import ProtocolProofs.Audit.UpdatePrice

/-
# Audit: updatePrice front-running a fill, and the native-output debit (swarm issue #19)

Builds on the order book of `ProtocolProofs.Audit.UpdatePrice` (#17) and adds the fill path of
`protocol/src` at e230f5b.

* `calculatePoolFee(_, a) = (a / 997) * 3 + ((a % 997) * 3) / 997` (AsyncSwap.sol:223-227).
* `AsyncFiller.fill` (AsyncFiller.sol:94-130): `NotAuthorizedExecutor` unless
  `isExecutor[order.owner][msg.sender]`, `OrderNotFound` if `amountIn == 0`, then `delete` the
  record and, for native output only, `settle` `amountOutMin + fee` out of the hook's ETH
  (line 119). ERC20 output was already credited to the hook by the Router (`settleFor`).
  The executor check is the boolean `isExec`; PM deltas beyond the native pull are not modelled.
* `AsyncSwap.executeOrder` (AsyncSwap.sol:233-254): for native output it reads the live
  `amountOutMin` (through `this.asyncOrderInfo`, the same storage slot), adds the pool fee,
  reverts with `UnaccountedNativeOutput` if the transient `PENDING_NATIVE_DEPOSIT` is smaller,
  and decrements it by that sum; then it calls `fill` with `fee = calculatePoolFee(amountOutMin)`.
* `Router.fillOrder` (Router.sol:141-165) with its callback branch (Router.sol:256-277). It reads
  the live price `amountOutMin + fee` twice, once before forwarding ETH and once in the callback;
  nothing between the two reads can write the order (the ETH send runs only the hook's
  `receive`, AsyncSwap.sol:414-419), so the model reads it once. Native output: `msg.value` must
  equal the live price and is added to `PENDING_NATIVE_DEPOSIT` by `receive`. ERC20 output:
  `msg.value == 0` and the Router pulls exactly the live price from the filler. Both then
  require `livePrice <= maxPrice` (Router.sol:267).

A transaction is atomic, so a maker's `updatePrice` can only land before or after a fill,
never inside it; the front-run is `updatePrice` followed by `fillOrder` on the new state.
-/

namespace ProtocolProofs.Audit.UpdatePriceFill

open ProtocolProofs.Audit.UpdatePrice

/-- `AsyncSwap.calculatePoolFee` (AsyncSwap.sol:223-227). -/
def poolFee (a : Nat) : Nat := (a / 997) * 3 + ((a % 997) * 3) / 997

/-- What a fill costs at the current state: the maker's live net price plus the pool fee
(Router.sol:156-157, 261-262; AsyncSwap.sol:244-245). -/
def livePrice (s : Orders) (id : Nat) : Nat := (s id).amountOutMin + poolFee (s id).amountOutMin

/-- `AsyncFiller.fill` (AsyncFiller.sol:94-130): the new order book and the native ETH it
settles out of the hook (zero for ERC20 output, which is pre-settled). -/
def fill (isExec : Bool) (id : Nat) (native : Bool) (fee : Nat) (s : Orders) :
    Option (Orders × Nat) :=
  if isExec = true ∧ (s id).amountIn ≠ 0 then
    some (fun j => if j = id then ⟨0, 0⟩ else s j,
      if native then (s id).amountOutMin + fee else 0)
  else none

/-- `AsyncSwap.executeOrder` (AsyncSwap.sol:233-254): returns the new pending-deposit ledger,
the new order book and the native amount `fill` pulled. -/
def executeOrder (isExec : Bool) (id : Nat) (native : Bool) (pending : Nat) (s : Orders) :
    Option (Nat × Orders × Nat) :=
  if native then
    if pending < livePrice s id then none
    else (fill isExec id true (poolFee (s id).amountOutMin) s).map
      fun r => (pending - livePrice s id, r.1, r.2)
  else (fill isExec id false (poolFee (s id).amountOutMin) s).map fun r => (pending, r.1, r.2)

/-- `Router.fillOrder` and its `FillOrder` callback branch (Router.sol:141-165, 256-277):
returns the new pending-deposit ledger, the new order book and what the filler paid in total
(the ETH sent, or the ERC20 pulled by `safeTransferFrom`). -/
def fillOrder (isExec : Bool) (id : Nat) (native : Bool) (maxPrice msgValue pending : Nat)
    (s : Orders) : Option (Nat × Orders × Nat) :=
  if native then
    if msgValue = livePrice s id ∧ livePrice s id ≤ maxPrice then
      (executeOrder isExec id true (pending + msgValue) s).map fun r => (r.1, r.2.1, msgValue)
    else none
  else
    if msgValue = 0 ∧ livePrice s id ≤ maxPrice then
      (executeOrder isExec id false pending s).map fun r => (r.1, r.2.1, livePrice s id)
    else none

/-! ### updatePrice -/

variable (oid : OrderKey → Nat)

/-- Direct path: only `order.owner` can update (AsyncFiller.sol:78). -/
theorem updatePrice_onlyMaker (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') : caller = o.owner :=
  (updatePrice_auth oid caller o n s s' h).1

/-- A zero limit is rejected (AsyncFiller.sol:79). -/
theorem updatePrice_rejects_zero (caller : Nat) (o : OrderKey) (s : Orders) :
    updatePrice oid caller o 0 s = none := by
  simp [updatePrice]

/-- A filled, cancelled or never-created order is rejected (AsyncFiller.sol:81). -/
theorem updatePrice_rejects_closed (caller : Nat) (o : OrderKey) (n : Nat) (s : Orders)
    (hc : (s (oid o)).amountIn = 0) : updatePrice oid caller o n s = none := by
  simp [updatePrice, hc]

/-- The update never changes any order's `amountIn`. -/
theorem updatePrice_preserves_amountIn (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') (id : Nat) :
    (s' id).amountIn = (s id).amountIn :=
  (updatePrice_preserves_escrow oid caller o n s s' h).1 id

/-! ### Native output: the ledger debit is what `fill` pulls -/

/-- For native output, `executeOrder` lowers `PENDING_NATIVE_DEPOSIT` by exactly the ETH that
`fill` settles, and that is the live price `amountOutMin + calculatePoolFee(amountOutMin)`. -/
theorem executeOrder_native_debit_eq_pull (isExec : Bool) (id pending : Nat) (s : Orders)
    (p' : Nat) (s' : Orders) (pulled : Nat)
    (h : executeOrder isExec id true pending s = some (p', s', pulled)) :
    p' + pulled = pending ∧ pulled = livePrice s id := by
  simp only [executeOrder, if_true] at h
  split at h
  · simp at h
  · rename_i hlt
    simp only [fill, if_true] at h
    split at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -, h3⟩ := h
      simp only [livePrice] at hlt h1 h3 ⊢
      omega
    · simp at h

/-! ### Router fills: the front-run is bounded -/

/-- Every successful Router fill charges the filler exactly the live price at execution, and
never more than `maxPrice`. -/
theorem fillOrder_paid_le_maxPrice (isExec : Bool) (id : Nat) (native : Bool)
    (maxPrice msgValue pending : Nat) (s : Orders) (p' : Nat) (s' : Orders) (paid : Nat)
    (h : fillOrder isExec id native maxPrice msgValue pending s = some (p', s', paid)) :
    paid = livePrice s id ∧ paid ≤ maxPrice := by
  unfold fillOrder at h
  cases native
  · simp only [Bool.false_eq_true, if_false] at h
    split at h
    · rename_i hg
      cases he : executeOrder isExec id false pending s with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.2.2.symm, h.2.2 ▸ hg.2⟩
    · simp at h
  · simp only [if_true] at h
    split at h
    · rename_i hg
      cases he : executeOrder isExec id true (pending + msgValue) s with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.2.2 ▸ hg.1, h.2.2 ▸ hg.1 ▸ hg.2⟩
    · simp at h

/-- A native Router fill leaves the pending-deposit ledger where it found it: the filler's
deposit is consumed in full, nothing is stranded and no earlier deposit is drawn. -/
theorem fillOrder_native_pending_restored (isExec : Bool) (id maxPrice msgValue pending : Nat)
    (s : Orders) (p' : Nat) (s' : Orders) (paid : Nat)
    (h : fillOrder isExec id true maxPrice msgValue pending s = some (p', s', paid)) :
    p' = pending := by
  simp only [fillOrder, if_true] at h
  split at h
  · rename_i hg
    cases he : executeOrder isExec id true (pending + msgValue) s with
    | none => simp [he] at h
    | some r =>
      obtain ⟨q, t, pulled⟩ := r
      simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hd, hpl⟩ := executeOrder_native_debit_eq_pull isExec id _ s q t pulled he
      have hq : q = p' := h.1
      omega
  · simp at h

/-- The front-run of lee-audit H-01: the maker reprices, then the filler's `fillOrder` lands on
the new state. Whatever the new price, a fill that goes through costs the filler at most the
`maxPrice` they chose; for native output it costs exactly the `msg.value` they sent; and the
input they receive is still the order's original `amountIn`. -/
theorem frontrun_bounded (caller : Nat) (o : OrderKey) (n : Nat) (s s₁ : Orders)
    (hup : updatePrice oid caller o n s = some s₁) (isExec : Bool) (native : Bool)
    (maxPrice msgValue pending : Nat) (p' : Nat) (s' : Orders) (paid : Nat)
    (h : fillOrder isExec (oid o) native maxPrice msgValue pending s₁ = some (p', s', paid)) :
    paid ≤ maxPrice ∧ paid = livePrice s₁ (oid o) ∧ (native = true → paid = msgValue) ∧
      (s₁ (oid o)).amountIn = (s (oid o)).amountIn := by
  obtain ⟨hp, hm⟩ := fillOrder_paid_le_maxPrice isExec (oid o) native maxPrice msgValue pending
    s₁ p' s' paid h
  refine ⟨hm, hp, fun hn => ?_, updatePrice_preserves_amountIn oid caller o n s s₁ hup _⟩
  subst hn
  simp only [fillOrder, if_true] at h
  split at h
  · cases he : executeOrder isExec (oid o) true (pending + msgValue) s₁ with
    | none => simp [he] at h
    | some r =>
      simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  · simp at h

end ProtocolProofs.Audit.UpdatePriceFill
