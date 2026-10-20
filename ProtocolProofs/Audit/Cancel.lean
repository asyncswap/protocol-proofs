import ProtocolProofs.Audit.UpdatePriceFill

/-
# Audit: cancel refunds exactly the escrow to the owner, once (swarm issue #29)

Builds on the order book of `ProtocolProofs.Audit.UpdatePrice` (#17) and the `fill` of
`ProtocolProofs.Audit.UpdatePriceFill` (#19), and adds the cancel paths of `protocol/src` at
e230f5b.

* `AsyncFiller.cancel` (AsyncFiller.sol:136-155): `NotAuthorizedExecutor` unless
  `executor == order.owner || isExecutor[order.owner][executor]` (line 139), `OrderNotFound` if
  `orders[id].amountIn == 0` (line 144), then `delete orders[id]` (line 147), burn the hook's
  6909 claim of `amountIn` and `take` the same `amountIn` of the input currency to `order.owner`
  (lines 151-152). The executor flag is the boolean `isExec`. The model returns the new order
  book together with the one transfer out: recipient and amount. The currency is
  `order.zeroForOne ? currency0 : currency1`, and both `zeroForOne` and the pool key are part of
  the id preimage, so it is the currency the order escrowed.
* `AsyncSwap.cancelOrder` (AsyncSwap.sol:265-268): `id = order.orderId()`, then the library call
  with `executor = msg.sender`. Anyone may call the hook directly; the library check is the
  only gate.
* `Router.cancelOrder` (Router.sol:211-217) requires `msg.sender == order.owner`, then reaches
  the hook through the `Cancel` callback (Router.sol:278-279) with the Router as executor.
* `Router.cancelWithSig` (Router.sol:191-202) checks deadline, an unused per-owner nonce and the
  owner's EIP-712 signature (the boolean `sigOk`), then the same callback. The nonce map is
  outside the model.

The id is the abstract `oid` of #17; keccak collision resistance is the hypothesis
`∀ a b, oid a = oid b → a = b`, used only where stated.
-/

namespace ProtocolProofs.Audit.Cancel

open ProtocolProofs.Audit.UpdatePrice ProtocolProofs.Audit.UpdatePriceFill

variable (oid : OrderKey → Nat)

/-- `AsyncFiller.cancel` (AsyncFiller.sol:136-155): the new order book, who receives the
refund, and how much. -/
def cancel (isExec : Bool) (executor : Nat) (o : OrderKey) (s : Orders) :
    Option (Orders × Nat × Nat) :=
  if (executor = o.owner ∨ isExec = true) ∧ (s (oid o)).amountIn ≠ 0 then
    some (fun j => if j = oid o then ⟨0, 0⟩ else s j, o.owner, (s (oid o)).amountIn)
  else none

/-- `AsyncSwap.cancelOrder` (AsyncSwap.sol:265-268): the hook's caller is the executor. -/
def hookCancelOrder (isExec : Bool) (msgSender : Nat) (o : OrderKey) (s : Orders) :
    Option (Orders × Nat × Nat) :=
  cancel oid isExec msgSender o s

/-- `Router.cancelOrder` (Router.sol:211-217, 278-279): the maker calls the Router, which is the
hook's caller. -/
def routerCancelOrder (isExec : Bool) (router caller : Nat) (o : OrderKey) (s : Orders) :
    Option (Orders × Nat × Nat) :=
  if caller = o.owner then hookCancelOrder oid isExec router o s else none

/-- `Router.cancelWithSig` (Router.sol:191-202, 278-279): a relayer submits the maker's
signature; the Router is the hook's caller. -/
def routerCancelWithSig (sigOk isExec : Bool) (router : Nat) (o : OrderKey) (s : Orders) :
    Option (Orders × Nat × Nat) :=
  if sigOk = true then hookCancelOrder oid isExec router o s else none

/-- Unfold a successful `cancel` into its guard and its result. -/
theorem cancel_some {isExec : Bool} {executor : Nat} {o : OrderKey} {s s' : Orders}
    {to amt : Nat} (h : cancel oid isExec executor o s = some (s', to, amt)) :
    ((executor = o.owner ∨ isExec = true) ∧ (s (oid o)).amountIn ≠ 0) ∧
      s' = (fun j => if j = oid o then ⟨0, 0⟩ else s j) ∧ to = o.owner ∧
      amt = (s (oid o)).amountIn := by
  simp only [cancel] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hg, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · simp at h

/-- The refund goes to `order.owner`, whoever the executor is, and is exactly the escrowed
`amountIn` of the record, which is not zero. -/
theorem cancel_refunds_owner_exact (isExec : Bool) (executor : Nat) (o : OrderKey)
    (s s' : Orders) (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt)) :
    to = o.owner ∧ amt = (s (oid o)).amountIn ∧ amt ≠ 0 := by
  obtain ⟨⟨-, hne⟩, -, hto, hamt⟩ := cancel_some oid h
  exact ⟨hto, hamt, hamt ▸ hne⟩

/-- Only the maker or an executor the maker authorised can cancel. -/
theorem cancel_auth (isExec : Bool) (executor : Nat) (o : OrderKey) (s s' : Orders)
    (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt)) :
    executor = o.owner ∨ isExec = true :=
  (cancel_some oid h).1.1

/-- The record is deleted and no other order changes. -/
theorem cancel_deletes_order (isExec : Bool) (executor : Nat) (o : OrderKey) (s s' : Orders)
    (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt)) :
    s' (oid o) = ⟨0, 0⟩ ∧ ∀ j, j ≠ oid o → s' j = s j := by
  obtain ⟨-, hs, -, -⟩ := cancel_some oid h
  subst hs
  exact ⟨by simp, fun j hj => by simp [hj]⟩

/-- Nobody else is paid: with keccak collision-free, every order key that hashes to the
deleted record names the refund recipient as its owner. -/
theorem cancel_refund_to_record_owner (hinj : ∀ a b, oid a = oid b → a = b) (isExec : Bool)
    (executor : Nat) (o : OrderKey) (s s' : Orders) (to amt : Nat)
    (h : cancel oid isExec executor o s = some (s', to, amt)) (k : OrderKey)
    (hk : oid k = oid o) : k.owner = to := by
  rw [hinj k o hk, (cancel_refunds_owner_exact oid isExec executor o s s' to amt h).1]

/-- A cancelled, filled or never-created order cannot be cancelled. -/
theorem cancel_rejects_closed (isExec : Bool) (executor : Nat) (o : OrderKey) (s : Orders)
    (hc : (s (oid o)).amountIn = 0) : cancel oid isExec executor o s = none := by
  simp [cancel, hc]

/-- No double refund: after a cancel, no second cancel of any order key with the same id
succeeds, whoever calls it. -/
theorem no_double_cancel (isExec : Bool) (executor : Nat) (o : OrderKey) (s s' : Orders)
    (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt)) (isExec' : Bool)
    (executor' : Nat) (k : OrderKey) (hk : oid k = oid o) :
    cancel oid isExec' executor' k s' = none := by
  apply cancel_rejects_closed
  rw [hk, (cancel_deletes_order oid isExec executor o s s' to amt h).1]

/-- No cancel after a fill: `fill` deletes the record, so the maker cannot reclaim input the
filler already received. -/
theorem no_cancel_after_fill (isExecF : Bool) (o : OrderKey) (native : Bool) (fee : Nat)
    (s s' : Orders) (pulled : Nat) (hf : fill isExecF (oid o) native fee s = some (s', pulled))
    (isExec : Bool) (executor : Nat) (k : OrderKey) (hk : oid k = oid o) :
    cancel oid isExec executor k s' = none := by
  apply cancel_rejects_closed
  rw [hk]
  simp only [fill] at hf
  split at hf
  · simp only [Option.some.injEq, Prod.mk.injEq] at hf
    rw [← hf.1]
    simp
  · simp at hf

/-- No fill after a cancel: the filler cannot pay for input that was already refunded. -/
theorem no_fill_after_cancel (isExec : Bool) (executor : Nat) (o : OrderKey) (s s' : Orders)
    (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt)) (isExecF : Bool)
    (native : Bool) (fee : Nat) : fill isExecF (oid o) native fee s' = none := by
  have hd := (cancel_deletes_order oid isExec executor o s s' to amt h).1
  simp [fill, hd]

/-- Nor through any entry point that reaches `fill`: `executeOrder` and `Router.fillOrder`
revert after a cancel. -/
theorem no_fillOrder_after_cancel (isExec : Bool) (executor : Nat) (o : OrderKey)
    (s s' : Orders) (to amt : Nat) (h : cancel oid isExec executor o s = some (s', to, amt))
    (isExecF native : Bool) (maxPrice msgValue pending : Nat) :
    executeOrder isExecF (oid o) native pending s' = none ∧
      fillOrder isExecF (oid o) native maxPrice msgValue pending s' = none := by
  have hf := no_fill_after_cancel oid isExec executor o s s' to amt h isExecF
  have he : executeOrder isExecF (oid o) native pending s' = none := by
    cases native <;> simp [executeOrder, hf]
  refine ⟨he, ?_⟩
  have he' : ∀ p, executeOrder isExecF (oid o) native p s' = none := fun p => by
    cases native <;> simp [executeOrder, hf]
  cases native <;> simp [fillOrder, he']

/-! ### Entry points -/

/-- Through the Router's direct path only the maker can cancel, and the refund still goes to
the maker. -/
theorem routerCancelOrder_onlyMaker (isExec : Bool) (router caller : Nat) (o : OrderKey)
    (s s' : Orders) (to amt : Nat)
    (h : routerCancelOrder oid isExec router caller o s = some (s', to, amt)) :
    caller = o.owner ∧ cancel oid isExec router o s = some (s', to, amt) := by
  simp only [routerCancelOrder, hookCancelOrder] at h
  split at h
  · rename_i hg
    exact ⟨hg, h⟩
  · simp at h

/-- The relayed path needs the maker's signature and then has exactly the effect of `cancel`:
a relayer cannot redirect the refund to itself. -/
theorem routerCancelWithSig_refunds_owner (sigOk isExec : Bool) (router : Nat) (o : OrderKey)
    (s s' : Orders) (to amt : Nat)
    (h : routerCancelWithSig oid sigOk isExec router o s = some (s', to, amt)) :
    sigOk = true ∧ to = o.owner ∧ amt = (s (oid o)).amountIn := by
  simp only [routerCancelWithSig, hookCancelOrder] at h
  split at h
  · rename_i hg
    obtain ⟨hto, hamt, -⟩ := cancel_refunds_owner_exact oid isExec router o s s' to amt h
    exact ⟨hg, hto, hamt⟩
  · simp at h

/-- Calling the hook directly: a caller who is neither the maker nor an executor the maker
authorised is refused. -/
theorem hookCancelOrder_stranger_reverts (msgSender : Nat) (o : OrderKey) (s : Orders)
    (hne : msgSender ≠ o.owner) : hookCancelOrder oid false msgSender o s = none := by
  simp [hookCancelOrder, cancel, hne]

end ProtocolProofs.Audit.Cancel
