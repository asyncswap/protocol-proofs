/-
# Audit: updatePrice gating and escrow immutability (swarm issue #17)

Model of the order book of one AsyncSwap pool and the two price-update entry points of
`protocol/src/AsyncSwap.sol` at e230f5b.

* An order lives at `orders[id]` as `OrderInfo { amountIn, amountOutMin }`
  (AsyncFiller.sol:26-29). `fill` and `cancel` `delete` the record (AsyncFiller.sol:113,147),
  so a filled or cancelled order is one with `amountIn == 0`, and that is also how every path
  tests for "open" (AsyncFiller.sol:81,108,144; AsyncSwap.sol:320).
* `id = keccak256(abi.encode(block.chainid, poolId, owner, zeroForOne, salt))`
  (AsyncOrder.sol:47-49). It reads only those fields of the `AsyncOrder` calldata; the
  calldata `amountIn`, `amountOutMin` and `sqrtPrice` are never read by `updatePrice`. The
  model keeps the five addressing fields as `OrderKey` (chain id folded into `pool`) and the
  hash as an abstract `oid`; collision resistance of keccak is the hypothesis
  `∀ a b, oid a = oid b → a = b`, used only where stated.
* `updatePrice(order, n)` (AsyncSwap.sol:258-261) calls `AsyncFiller.updatePrice` with
  `caller = msg.sender` (AsyncFiller.sol:71-85): `NotOrderOwner` unless
  `caller == order.owner`, then `ZeroAmount` if `n == 0`, then `OrderNotFound` if
  `orders[id].amountIn == 0`, then `orders[id].amountOutMin = n`.
* `updatePriceWithSig` (AsyncSwap.sol:361-379) runs `_verify` (AsyncSwap.sol:395-405) for
  `order.owner` and then the same library call with `caller = order.owner`. The signature
  check is the boolean `sigOk`: whether `SignatureChecker` accepted a signature by
  `order.owner` over `hashUpdatePrice(order, id, amountIn, n, nonce, deadline)` within the
  deadline and with an unused nonce. The nonce map is outside this model.

A reverted call is `none`. Addresses, ids and amounts are naturals.
-/

namespace ProtocolProofs.Audit.UpdatePrice

/-- The fields `AsyncOrderLibrary.orderId` hashes (AsyncOrder.sol:48). -/
structure OrderKey where
  pool : Nat
  owner : Nat
  zeroForOne : Bool
  salt : Nat
  deriving DecidableEq, Repr

/-- `AsyncFiller.OrderInfo` (AsyncFiller.sol:26-29). -/
structure Info where
  amountIn : Nat
  amountOutMin : Nat
  deriving DecidableEq, Repr

/-- `State.orders` of one pool (AsyncFiller.sol:33). -/
abbrev Orders := Nat → Info

variable (oid : OrderKey → Nat)

/-- `AsyncFiller.updatePrice` (AsyncFiller.sol:71-85), reached from `AsyncSwap.updatePrice`
(AsyncSwap.sol:258-261) with `caller = msg.sender`. -/
def updatePrice (caller : Nat) (o : OrderKey) (n : Nat) (s : Orders) : Option Orders :=
  if caller = o.owner ∧ n ≠ 0 ∧ (s (oid o)).amountIn ≠ 0 then
    some fun id => if id = oid o then { s id with amountOutMin := n } else s id
  else none

/-- `AsyncSwap.updatePriceWithSig` (AsyncSwap.sol:361-379): the maker's signature, then the
library call with `caller = order.owner`. -/
def updatePriceWithSig (sigOk : Bool) (o : OrderKey) (n : Nat) (s : Orders) : Option Orders :=
  if sigOk = true then updatePrice oid o.owner o n s else none

/-- Only the maker named in the order can update it, and never to a zero limit. Executors
get no power here: unlike `fill` and `cancel`, `isExecutor` is not consulted. -/
theorem updatePrice_auth (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') : caller = o.owner ∧ n ≠ 0 := by
  simp only [updatePrice] at h
  split at h
  · rename_i hg
    exact ⟨hg.1, hg.2.1⟩
  · simp at h

/-- The update reverts on a filled, cancelled or never-created order. -/
theorem updatePrice_requires_open (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') : (s (oid o)).amountIn ≠ 0 := by
  simp only [updatePrice] at h
  split at h
  · rename_i hg
    exact hg.2.2
  · simp at h

/-- No escrow moves: every order keeps its `amountIn`, every other order is untouched, and
the addressed order gets exactly the new limit. -/
theorem updatePrice_preserves_escrow (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') :
    (∀ id, (s' id).amountIn = (s id).amountIn) ∧
    (∀ id, id ≠ oid o → s' id = s id) ∧
    (s' (oid o)).amountOutMin = n := by
  simp only [updatePrice] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun id => ?_, fun id hid => ?_, ?_⟩
    · by_cases hid : id = oid o <;> simp [hid]
    · simp [hid]
    · simp
  · simp at h

/-- A closed order stays closed: the update writes no record whose `amountIn` is `0`, so it
cannot resurrect a filled or cancelled order, nor create one. -/
theorem updatePrice_no_resurrect (caller : Nat) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePrice oid caller o n s = some s') (id : Nat) (hc : (s id).amountIn = 0) :
    s' id = s id := by
  obtain ⟨-, hother, -⟩ := updatePrice_preserves_escrow oid caller o n s s' h
  by_cases hid : id = oid o
  · subst hid
    exact absurd hc (updatePrice_requires_open oid caller o n s s' h)
  · exact hother id hid

/-- No foreign order: if a record changes, every order key hashing to it is owned by the
caller, so a forged or stale `AsyncOrder` struct cannot reach another maker's order (assuming
keccak is collision-free). -/
theorem updatePrice_only_own_orders (hinj : ∀ a b, oid a = oid b → a = b) (caller : Nat)
    (o : OrderKey) (n : Nat) (s s' : Orders) (h : updatePrice oid caller o n s = some s')
    (id : Nat) (hch : s' id ≠ s id) (k : OrderKey) (hk : oid k = id) : k.owner = caller := by
  obtain ⟨-, hother, -⟩ := updatePrice_preserves_escrow oid caller o n s s' h
  have hid : id = oid o := Classical.byContradiction fun hne => hch (hother id hne)
  rw [hinj k o (hk.trans hid),(updatePrice_auth oid caller o n s s' h).1]

/-- The signed path needs the maker's signature and then has exactly the effect of the maker
calling `updatePrice` directly, so all of the above carries over. -/
theorem updatePriceWithSig_auth (sigOk : Bool) (o : OrderKey) (n : Nat) (s s' : Orders)
    (h : updatePriceWithSig oid sigOk o n s = some s') :
    sigOk = true ∧ updatePrice oid o.owner o n s = some s' := by
  simp only [updatePriceWithSig] at h
  split at h
  · rename_i hg
    exact ⟨hg, h⟩
  · simp at h

end ProtocolProofs.Audit.UpdatePrice
