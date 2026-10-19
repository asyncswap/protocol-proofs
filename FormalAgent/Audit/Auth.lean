/-
Access-control model of asyncswap/protocol at e230f5b (swarm issue #5).

Covers every state-changing entry point of `AsyncSwap.sol` and `FeeVault.sol` that touches
an order, an executor grant, a nonce, the owner, or funds held by the hook or the vault.
Amount arithmetic, the native-deposit ledger and the PoolManager deltas are not modelled
here; only who may call what, and where the money goes.

Abstractions (each one is a standing assumption of this file):
* `keccak256` of the orderId preimage is injective, so an order id *is* its preimage
  `(chainid, poolId, owner, zeroForOne, salt)` (AsyncOrder.sol:48). The chain id is fixed.
* `asyncOrders[poolId].orders[id]` is flattened to one map on ids; the id already carries
  the pool, and every Solidity path reads the map at `order.key.toId()`, the pool in the id.
* `SignatureChecker.isValidSignatureNow` is an opaque oracle `V signer msg sig`. EIP-712
  domain separation and unforgeability are outside the model; the theorems say a successful
  signed call carried a signature `V` accepts for the maker over exactly that message.
* The v4 PoolManager calls `unlockCallback` only on the address that called `unlock`
  (PoolManager.unlock). This is how the vault's callback is reached; see `vaultStep`.
-/

namespace FormalAgent.Audit.Auth

abbrev Addr := Nat
abbrev PoolId := Nat
abbrev Currency := Nat

/-- Order id preimage, AsyncOrder.sol:48 (`orderId`). -/
structure OrderId where
  pool : PoolId
  owner : Addr
  zeroForOne : Bool
  salt : Nat
  deriving DecidableEq

/-- `AsyncFiller.OrderInfo`, AsyncFiller.sol:26. An absent order reads as zeros. -/
structure OrderInfo where
  amountIn : Nat
  amountOutMin : Nat

def OrderInfo.empty : OrderInfo := ⟨0, 0⟩

/-- Messages a maker signs (OrderSignatures.sol): `SetExecutor` and `UpdatePrice`. -/
inductive Msg where
  | setExecutor (pool : PoolId) (maker executor : Addr) (allow : Bool) (nonce deadline : Nat)
  | updatePrice (id : OrderId) (amountIn newAmountOutMin nonce deadline : Nat)

/-- The hook's storage that access control reads or writes. -/
structure State where
  owner : Addr
  pendingOwner : Addr
  /-- `asyncOrders[pool].isExecutor[maker][executor]`, AsyncFiller.sol:34. -/
  isExecutor : PoolId → Addr → Addr → Bool
  orders : OrderId → OrderInfo
  /-- `nonceUsed[maker][nonce]`, AsyncSwap.sol:52. -/
  nonceUsed : Addr → Nat → Bool

/-- Money leaving the hook or the vault: `(currency or order, recipient, amount)`. -/
structure Payout where
  recipient : Addr
  amount : Nat

/-- Entry points of `AsyncSwap`. `sender` is always `msg.sender` of the hook, except for
`createOrder`, where it is the `sender` argument the PoolManager passes to `beforeSwap`
(the swap caller), AsyncSwap.sol:271. -/
inductive Call where
  /-- `_beforeSwap` → `_createOrder`, AsyncSwap.sol:271-327. `salt` is the free slot the
  collision walk lands on. -/
  | createOrder (sender user executor : Addr) (pool : PoolId) (zeroForOne : Bool)
      (salt amountIn amountOutMin : Nat)
  /-- `executeOrder`, AsyncSwap.sol:233 → `AsyncFiller.fill`, AsyncFiller.sol:95. -/
  | executeOrder (sender : Addr) (order : OrderId) (filler : Addr)
  /-- `updatePrice`, AsyncSwap.sol:258 → `AsyncFiller.updatePrice`, AsyncFiller.sol:71. -/
  | updatePrice (sender : Addr) (order : OrderId) (newAmountOutMin : Nat)
  /-- `updatePriceWithSig`, AsyncSwap.sol:361. -/
  | updatePriceWithSig (order : OrderId) (newAmountOutMin nonce deadline sig : Nat)
  /-- `cancelOrder`, AsyncSwap.sol:265 → `AsyncFiller.cancel`, AsyncFiller.sol:142. -/
  | cancelOrder (sender : Addr) (order : OrderId)
  /-- `setExecutor`, AsyncSwap.sol:332. -/
  | setExecutor (sender : Addr) (pool : PoolId) (executor : Addr) (allow : Bool)
  /-- `setExecutorWithSig`, AsyncSwap.sol:339. -/
  | setExecutorWithSig (pool : PoolId) (maker executor : Addr) (allow : Bool)
      (nonce deadline sig : Nat)
  /-- `invalidateNonce`, AsyncSwap.sol:382. -/
  | invalidateNonce (sender : Addr) (nonce : Nat)
  /-- `transferOwnership`, AsyncSwap.sol:135. -/
  | transferOwnership (sender newOwner : Addr)
  /-- `acceptOwnership`, AsyncSwap.sol:142. -/
  | acceptOwnership (sender : Addr)
  /-- `sweep`, AsyncSwap.sol:154. `balance` is `currency.balanceOfSelf()`. -/
  | sweep (sender : Addr) (currency : Currency) (to : Addr) (balance : Nat)

section
variable (V : Addr → Msg → Nat → Bool) (now : Nat)

def setOrder (s : State) (id : OrderId) (info : OrderInfo) : State :=
  { s with orders := fun x => if x = id then info else s.orders x }

def setExec (s : State) (pool : PoolId) (maker executor : Addr) (allow : Bool) : State :=
  { s with isExecutor := fun p m e =>
      if p = pool ∧ m = maker ∧ e = executor then allow else s.isExecutor p m e }

def burnNonce (s : State) (maker : Addr) (nonce : Nat) : State :=
  { s with nonceUsed := fun m n => if m = maker ∧ n = nonce then true else s.nonceUsed m n }

/-- `_verify`, AsyncSwap.sol:395: deadline, unused nonce, valid signature; burns the nonce. -/
def verify (s : State) (maker : Addr) (m : Msg) (nonce deadline sig : Nat) : Option State :=
  if now ≤ deadline ∧ s.nonceUsed maker nonce = false ∧ V maker m sig = true then
    some (burnNonce s maker nonce)
  else none

/-- One call on the hook. Returns the new state and the payouts it makes. -/
def step (s : State) : Call → Option (State × List Payout)
  | .createOrder sender user executor pool zeroForOne salt amountIn amountOutMin =>
    let id : OrderId := ⟨pool, user, zeroForOne, salt⟩
    if sender = executor ∧ s.isExecutor pool user executor = true ∧ amountIn ≠ 0 ∧
        amountOutMin ≠ 0 ∧ (s.orders id).amountIn = 0 then
      some (setOrder s id ⟨amountIn, amountOutMin⟩, [])
    else none
  | .executeOrder sender o filler =>
    let info := s.orders o
    if s.isExecutor o.pool o.owner sender = true ∧ info.amountIn ≠ 0 then
      -- maker gets the net minimum (AsyncFiller.sol:121), filler gets the input (:129)
      some (setOrder s o OrderInfo.empty,
        [⟨o.owner, info.amountOutMin⟩, ⟨filler, info.amountIn⟩])
    else none
  | .updatePrice sender o newMin =>
    if sender = o.owner ∧ newMin ≠ 0 ∧ (s.orders o).amountIn ≠ 0 then
      some (setOrder s o ⟨(s.orders o).amountIn, newMin⟩, [])
    else none
  | .updatePriceWithSig o newMin nonce deadline sig =>
    let amountIn := (s.orders o).amountIn
    match verify V now s o.owner (.updatePrice o amountIn newMin nonce deadline) nonce deadline sig with
    | none => none
    | some s1 =>
      if newMin ≠ 0 ∧ (s1.orders o).amountIn ≠ 0 then
        some (setOrder s1 o ⟨(s1.orders o).amountIn, newMin⟩, [])
      else none
  | .cancelOrder sender o =>
    let info := s.orders o
    if (sender = o.owner ∨ s.isExecutor o.pool o.owner sender = true) ∧ info.amountIn ≠ 0 then
      some (setOrder s o OrderInfo.empty, [⟨o.owner, info.amountIn⟩])
    else none
  | .setExecutor sender pool executor allow =>
    some (setExec s pool sender executor allow, [])
  | .setExecutorWithSig pool maker executor allow nonce deadline sig =>
    match verify V now s maker (.setExecutor pool maker executor allow nonce deadline) nonce deadline sig with
    | none => none
    | some s1 => some (setExec s1 pool maker executor allow, [])
  | .invalidateNonce sender nonce =>
    if s.nonceUsed sender nonce = false then some (burnNonce s sender nonce, []) else none
  | .transferOwnership sender newOwner =>
    if sender = s.owner ∧ newOwner ≠ 0 then some ({ s with pendingOwner := newOwner }, [])
    else none
  | .acceptOwnership sender =>
    if sender = s.pendingOwner then some ({ s with owner := sender, pendingOwner := 0 }, [])
    else none
  | .sweep sender _ to balance =>
    if sender = s.owner ∧ to ≠ 0 then some (s, [⟨to, balance⟩]) else none

/-! ## One authorisation theorem per entry point -/

theorem createOrder_auth {s s' ps} {sender user executor pool zfo salt aIn aOut}
    (h : step V now s (.createOrder sender user executor pool zfo salt aIn aOut) = some (s', ps)) :
    sender = executor ∧ s.isExecutor pool user executor = true := by
  simp only [step] at h
  split at h
  · rename_i hg; exact ⟨hg.1, hg.2.1⟩
  · simp at h

/-- Only an executor the maker authorised can fill, and the maker is the one paid. -/
theorem executeOrder_auth {s s' ps} {sender o filler}
    (h : step V now s (.executeOrder sender o filler) = some (s', ps)) :
    s.isExecutor o.pool o.owner sender = true ∧
      ps = [⟨o.owner, (s.orders o).amountOutMin⟩, ⟨filler, (s.orders o).amountIn⟩] := by
  simp only [step] at h
  split at h
  · rename_i hg; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨hg.1, h.2.symm⟩
  · simp at h

theorem updatePrice_auth {s s' ps} {sender o n}
    (h : step V now s (.updatePrice sender o n) = some (s', ps)) : sender = o.owner := by
  simp only [step] at h
  split at h
  · rename_i hg; exact hg.1
  · simp at h

theorem verify_auth {s s1 maker m nonce deadline sig}
    (h : verify V now s maker m nonce deadline sig = some s1) :
    now ≤ deadline ∧ s.nonceUsed maker nonce = false ∧ V maker m sig = true ∧
      s1.nonceUsed maker nonce = true := by
  simp only [verify] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h; subst h
    exact ⟨hg.1, hg.2.1, hg.2.2, by simp [burnNonce]⟩
  · simp at h

/-- A signed price update needs the order owner's signature over this exact id, open
amount and new price, under an unused nonce. -/
theorem updatePriceWithSig_auth {s s' ps} {o n nonce deadline sig}
    (h : step V now s (.updatePriceWithSig o n nonce deadline sig) = some (s', ps)) :
    V o.owner (.updatePrice o (s.orders o).amountIn n nonce deadline) sig = true ∧
      s.nonceUsed o.owner nonce = false ∧ now ≤ deadline := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i s1 hv
    have := verify_auth V now hv
    exact ⟨this.2.2.1, this.2.1, this.1⟩

/-- Cancel needs the maker or one of the maker's executors, and refunds only the maker. -/
theorem cancelOrder_auth {s s' ps} {sender o}
    (h : step V now s (.cancelOrder sender o) = some (s', ps)) :
    (sender = o.owner ∨ s.isExecutor o.pool o.owner sender = true) ∧
      ps = [⟨o.owner, (s.orders o).amountIn⟩] := by
  simp only [step] at h
  split at h
  · rename_i hg; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨hg.1, h.2.symm⟩
  · simp at h

/-- `setExecutor` writes only the caller's own row. -/
theorem setExecutor_auth {s s' ps} {sender pool e allow}
    (h : step V now s (.setExecutor sender pool e allow) = some (s', ps))
    (p : PoolId) (m x : Addr) (hne : s'.isExecutor p m x ≠ s.isExecutor p m x) : m = sender := by
  simp only [step, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [setExec] at hne
  split at hne
  · rename_i hc; exact hc.2.1
  · exact absurd rfl hne

/-- A signed grant writes only the signer's row, and only with the signer's signature. -/
theorem setExecutorWithSig_auth {s s' ps} {pool maker e allow nonce deadline sig}
    (h : step V now s (.setExecutorWithSig pool maker e allow nonce deadline sig) = some (s', ps)) :
    V maker (.setExecutor pool maker e allow nonce deadline) sig = true ∧
      ∀ p m x, s'.isExecutor p m x ≠ s.isExecutor p m x → m = maker := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i s1 hv
    have hva := verify_auth V now hv
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨hva.2.2.1, fun p m x hne => ?_⟩
    simp only [verify] at hv
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv
      simp only [setExec, burnNonce] at hne
      split at hne
      · rename_i hc; exact hc.2.1
      · exact absurd rfl hne
    · simp at hv

theorem transferOwnership_auth {s s' ps} {sender n}
    (h : step V now s (.transferOwnership sender n) = some (s', ps)) : sender = s.owner := by
  simp only [step] at h
  split at h
  · rename_i hg; exact hg.1
  · simp at h

theorem acceptOwnership_auth {s s' ps} {sender}
    (h : step V now s (.acceptOwnership sender) = some (s', ps)) :
    sender = s.pendingOwner ∧ s'.owner = sender := by
  simp only [step] at h
  split at h
  · rename_i hg; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact ⟨hg, rfl⟩
  · simp at h

theorem sweep_auth {s s' ps} {sender c to bal}
    (h : step V now s (.sweep sender c to bal) = some (s', ps)) : sender = s.owner := by
  simp only [step] at h
  split at h
  · rename_i hg; exact hg.1
  · simp at h

/-! ## The order book is only touched with the maker's consent

Whatever the call, if the record of an order owned by `m` changes, then `m` consented:
`m` is the caller, or an executor `m` had authorised before the call is the caller, or `m`
signed a message naming that order. -/

/-- The caller of a call, if it has one (`msg.sender`, or the swap caller for `createOrder`). -/
def Call.sender : Call → Option Addr
  | .createOrder s .. => some s
  | .executeOrder s .. => some s
  | .updatePrice s .. => some s
  | .updatePriceWithSig .. => none
  | .cancelOrder s .. => some s
  | .setExecutor s .. => some s
  | .setExecutorWithSig .. => none
  | .invalidateNonce s .. => some s
  | .transferOwnership s .. => some s
  | .acceptOwnership s .. => some s
  | .sweep s .. => some s

theorem setOrder_other {s : State} {id x : OrderId} {i : OrderInfo} (h : x ≠ id) :
    (setOrder s id i).orders x = s.orders x := by
  simp [setOrder, h]

/-- Any change to an order's record was made by its owner, by an executor the owner had
authorised, or under the owner's signature over that order. -/
theorem orders_change_auth {s s' ps} (c : Call) (h : step V now s c = some (s', ps))
    (id : OrderId) (hch : (s'.orders id).amountIn ≠ (s.orders id).amountIn ∨
      (s'.orders id).amountOutMin ≠ (s.orders id).amountOutMin) :
    (∃ a, c.sender = some a ∧ (a = id.owner ∨ s.isExecutor id.pool id.owner a = true)) ∨
      (∃ n nonce deadline sig, c = .updatePriceWithSig id n nonce deadline sig ∧
        V id.owner (.updatePrice id (s.orders id).amountIn n nonce deadline) sig = true) := by
  have key : ∀ {t : State} {o : OrderId} {i : OrderInfo},
      ((setOrder t o i).orders id).amountIn ≠ (t.orders id).amountIn ∨
        ((setOrder t o i).orders id).amountOutMin ≠ (t.orders id).amountOutMin → id = o := by
    intro t o i hc
    by_cases hne : id = o
    · exact hne
    · rw [setOrder_other hne] at hc
      simp at hc
  cases c with
  | createOrder sender user executor pool zfo salt aIn aOut =>
    have ha := createOrder_auth V now h
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := key hch; subst this
      exact .inl ⟨sender, rfl, .inr (ha.1 ▸ ha.2)⟩
    · simp at h
  | executeOrder sender o filler =>
    have ha := executeOrder_auth V now h
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := key hch; subst this
      exact .inl ⟨sender, rfl, .inr ha.1⟩
    · simp at h
  | updatePrice sender o n =>
    have ha := updatePrice_auth V now h
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := key hch; subst this
      exact .inl ⟨sender, rfl, .inl ha⟩
    · simp at h
  | updatePriceWithSig o n nonce deadline sig =>
    have ha := updatePriceWithSig_auth V now h
    simp only [step] at h
    split at h
    · simp at h
    · rename_i s1 hv
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        -- `verify` only burns a nonce, so `s1.orders = s.orders`
        have hs1 : s1.orders = s.orders := by
          simp only [verify] at hv
          split at hv
          · simp only [Option.some.injEq] at hv; subst hv; rfl
          · simp at hv
        rw [← hs1] at hch
        have := key hch; subst this
        exact .inr ⟨n, nonce, deadline, sig, rfl, ha.1⟩
      · simp at h
  | cancelOrder sender o =>
    have ha := cancelOrder_auth V now h
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := key hch; subst this
      exact .inl ⟨sender, rfl, ha.1⟩
    · simp at h
  | setExecutor sender pool e allow =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp [setExec] at hch
  | setExecutorWithSig pool maker e allow nonce deadline sig =>
    simp only [step] at h
    split at h
    · simp at h
    · rename_i s1 hv
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp only [verify] at hv
      split at hv
      · simp only [Option.some.injEq] at hv; subst hv
        simp [setExec, burnNonce] at hch
      · simp at hv
  | invalidateNonce sender nonce =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp [burnNonce] at hch
    · simp at h
  | transferOwnership sender n =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp at hch
    · simp at h
  | acceptOwnership sender =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp at hch
    · simp at h
  | sweep sender c to bal =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp at hch
    · simp at h

end

/-! ## FeeVault

`collect` (FeeVault.sol:27) checks `msg.sender == hook.owner()` and then calls
`poolManager.unlock`; the PoolManager calls `unlockCallback` back on the caller of
`unlock`, which is the vault itself; the callback (FeeVault.sol:34) checks
`msg.sender == poolManager` and pays the vault's whole claim balance to `recipient`.
`vaultStep` models the two external entry points; a callback is reached either directly
(any `sender`) or through the PoolManager's unlock of the vault, which only `collect` does. -/

inductive VaultCall where
  /-- `collect(currency, recipient)` from `sender`. -/
  | collect (sender : Addr) (currency : Currency) (recipient : Addr)
  /-- A direct call of `unlockCallback(abi.encode(currency, recipient))` from `sender`. -/
  | unlockCallback (sender : Addr) (currency : Currency) (recipient : Addr)

/-- `hookOwner` is `hook.owner()` (= `State.owner` of the hook), `pm` the PoolManager,
`claims` the vault's ERC-6909 balance of the currency. -/
def vaultStep (hookOwner pm claims : Nat) : VaultCall → Option (List Payout)
  | .collect sender _ recipient =>
    -- FeeVault.sol:28-30, then the PoolManager's callback with `msg.sender = pm`
    if sender = hookOwner ∧ recipient ≠ 0 then
      some (if claims = 0 then [] else [⟨recipient, claims⟩])
    else none
  | .unlockCallback sender _ recipient =>
    -- FeeVault.sol:35. Called directly, the PoolManager is not unlocked by the vault, so
    -- the `take` would revert even for `sender = pm`; we keep the weaker guard as written.
    if sender = pm then some (if claims = 0 then [] else [⟨recipient, claims⟩]) else none

/-- Fees leave the vault only on a call from the hook's current owner, or from the
PoolManager itself. -/
theorem vault_auth {hookOwner pm claims ps} (c : VaultCall)
    (h : vaultStep hookOwner pm claims c = some ps) :
    match c with
    | .collect sender _ _ => sender = hookOwner
    | .unlockCallback sender _ _ => sender = pm := by
  cases c with
  | collect sender cur r =>
    simp only [vaultStep] at h
    split at h
    · rename_i hg; exact hg.1
    · simp at h
  | unlockCallback sender cur r =>
    simp only [vaultStep] at h
    split at h
    · rename_i hg; exact hg
    · simp at h

end FormalAgent.Audit.Auth
