import ProtocolProofs.Audit.UpdatePriceFill

/-
# Audit: native ETH sent to the Router is never stranded (swarm issue #21, H-05 fix)

Tracks the raw ETH balances of the Router and the hook, and the hook's transient
`PENDING_NATIVE_DEPOSIT`, across every Router entry point of `protocol/src` at e230f5b.

* `Router.swap` (Router.sol:109-130): native input requires `msg.value == order.amountIn`
  (line 121), ERC20 input requires `msg.value == 0` (line 123). In the callback the Router
  settles `amountIn` to the PoolManager with `CurrencySettler.settle` (Router.sol:254), whose
  native branch is `manager.settle{value: amount}()` from the Router's own balance
  (CurrencySettler.sol:21-22). The hook takes the maker's input as ERC-6909 claims, not ETH.
* `Router.fillOrder` (Router.sol:141-165, 256-277): native output requires
  `msg.value == amountOutMin + calculatePoolFee(amountOutMin)` read live (lines 156-158) and
  forwards all of `msg.value` to the hook (line 159), whose `receive` adds it to
  `PENDING_NATIVE_DEPOSIT` (AsyncSwap.sol:413-418); `executeOrder` then settles the live price
  out of the hook. ERC20 output requires `msg.value == 0` (line 162). The order book, fee and
  `executeOrder` are those of `ProtocolProofs.Audit.UpdatePriceFill` (#19).
* `swapWithSig`, `cancelWithSig`, `cancelOrder` (Router.sol:173, 191, 211) are not `payable`,
  so the compiler-inserted check reverts on any nonzero `msg.value`. Their callbacks move no ETH
  through the Router or the hook (input is ERC20 via Permit2, `swapWithSig` rejects native input
  at line 175; a cancel returns ERC-6909 claims).
* The Router has no `receive` or `fallback`, so a plain ETH transfer to it reverts.
  Forced sends (`selfdestruct`, coinbase) are outside the model.

Success of the PoolManager calls is assumed; the model asks what the ETH balances are *if* the
transaction goes through.
-/

namespace ProtocolProofs.Audit.RouterNative

open ProtocolProofs.Audit.UpdatePrice
open ProtocolProofs.Audit.UpdatePriceFill

/-- Raw ETH of the Router and the hook, and the hook's transient pending-deposit ledger. -/
structure Eth where
  router : Nat
  hook : Nat
  pending : Nat

/-- `Router.swap` (Router.sol:109-130, 234-255): the `msg.value` check, then the Router
settles `amountIn` of native input to the PoolManager from its own balance. -/
def swap (nativeIn : Bool) (amountIn msgValue : Nat) (e : Eth) : Option Eth :=
  if nativeIn then
    if msgValue = amountIn then some { e with router := e.router + msgValue - amountIn }
    else none
  else
    if msgValue = 0 then some { e with router := e.router + msgValue } else none

/-- `Router.fillOrder` (Router.sol:141-165, 256-277): native output forwards `msg.value`
from the Router to the hook (`receive` credits the ledger), then `executeOrder` pulls the live
price out of the hook. ERC20 output takes no ETH. -/
def fillOrder (isExec : Bool) (id : Nat) (native : Bool) (maxPrice msgValue : Nat)
    (e : Eth) (s : Orders) : Option (Eth × Orders) :=
  if native then
    if msgValue = livePrice s id ∧ livePrice s id ≤ maxPrice then
      (executeOrder isExec id true (e.pending + msgValue) s).map fun r =>
        ({ router := e.router + msgValue - msgValue, hook := e.hook + msgValue - r.2.2,
           pending := r.1 }, r.2.1)
    else none
  else
    if msgValue = 0 ∧ livePrice s id ≤ maxPrice then
      (executeOrder isExec id false e.pending s).map fun r =>
        ({ e with router := e.router + msgValue }, r.2.1)
    else none

/-- Every way to send ETH into the Router. -/
inductive Call where
  | swap (nativeIn : Bool) (amountIn msgValue : Nat)
  | fillOrder (isExec : Bool) (id : Nat) (native : Bool) (maxPrice msgValue : Nat)
  /-- `swapWithSig`, `cancelWithSig`, `cancelOrder`: non-payable. -/
  | nonPayable (msgValue : Nat)
  /-- A plain transfer: the Router has no `receive`/`fallback`. -/
  | plainSend (msgValue : Nat)

/-- One successful Router call. The order-book effect of non-payable calls is irrelevant
here, so they keep `s`. -/
def step (c : Call) (e : Eth) (s : Orders) : Option (Eth × Orders) :=
  match c with
  | .swap nativeIn amountIn msgValue => (swap nativeIn amountIn msgValue e).map (·, s)
  | .fillOrder isExec id native maxPrice msgValue => fillOrder isExec id native maxPrice msgValue e s
  | .nonPayable msgValue => if msgValue = 0 then some (e, s) else none
  | .plainSend _ => none

/-- Native input: a successful `swap` took exactly `amountIn` and the Router passed all of it
to the PoolManager. ERC20 input: no ETH was sent. Nothing else moved. -/
theorem swap_native_exact (nativeIn : Bool) (amountIn msgValue : Nat) (e e' : Eth)
    (h : swap nativeIn amountIn msgValue e = some e') :
    (if nativeIn then msgValue = amountIn else msgValue = 0) ∧
      e'.router = e.router ∧ e'.hook = e.hook ∧ e'.pending = e.pending := by
  unfold swap at h
  cases nativeIn
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hv, by simp [hv], rfl, rfl⟩
    · simp at h
  · simp only [if_true] at h ⊢
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hv, by dsimp only; omega, rfl, rfl⟩
    · simp at h

/-- Native output: a successful `fillOrder` took exactly the live price plus fee, the Router
forwarded all of it, the hook paid all of it to the maker's settlement, and the pending ledger
is back where it was. ERC20 output: no ETH was sent and no ETH moved. -/
theorem fillOrder_native_exact (isExec : Bool) (id : Nat) (native : Bool) (maxPrice msgValue : Nat)
    (e e' : Eth) (s s' : Orders)
    (h : fillOrder isExec id native maxPrice msgValue e s = some (e', s')) :
    (if native then msgValue = livePrice s id else msgValue = 0) ∧
      e'.router = e.router ∧ e'.hook = e.hook ∧ e'.pending = e.pending := by
  unfold fillOrder at h
  cases native
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    split at h
    · rename_i hg
      cases he : executeOrder isExec id false e.pending s with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨hg.1, ?_, rfl, rfl⟩
        simp only [hg.1, Nat.add_zero]
    · simp at h
  · simp only [if_true] at h ⊢
    split at h
    · rename_i hg
      cases he : executeOrder isExec id true (e.pending + msgValue) s with
      | none => simp [he] at h
      | some r =>
        obtain ⟨q, t, pulled⟩ := r
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨hd, hpl⟩ := executeOrder_native_debit_eq_pull isExec id _ s q t pulled he
        refine ⟨hg.1, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · simp at h

/-- No Router call strands ETH: after any successful call the Router's and the hook's raw ETH
balances and the hook's pending-deposit ledger are what they were before. Every wei a caller
sends is passed on to the PoolManager in the same transaction. -/
theorem router_no_stranded_eth (c : Call) (e e' : Eth) (s s' : Orders)
    (h : step c e s = some (e', s')) :
    e'.router = e.router ∧ e'.hook = e.hook ∧ e'.pending = e.pending := by
  cases c with
  | swap nativeIn amountIn msgValue =>
    simp only [step] at h
    cases hs : swap nativeIn amountIn msgValue e with
    | none => simp [hs] at h
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (swap_native_exact nativeIn amountIn msgValue e x hs).2
  | fillOrder isExec id native maxPrice msgValue =>
    exact (fillOrder_native_exact isExec id native maxPrice msgValue e e' s s' h).2
  | nonPayable msgValue =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · simp at h
  | plainSend _ => simp [step] at h

end ProtocolProofs.Audit.RouterNative
