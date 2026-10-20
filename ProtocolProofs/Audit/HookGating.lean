/-
# Audit: BaseHook caller gate and AsyncSwap permission bits (swarm issue #22)

Model of the ten external hook callbacks of `protocol/src/BaseHook.sol` at e230f5b and of
which of them `AsyncSwap` implements.

* Every external callback in `BaseHook` (BaseHook.sol:36-207) carries `onlyPoolManager`,
  which reverts `NotPoolManager` unless `msg.sender == address(poolManager)`
  (ImmutableState.sol:15-18), and then forwards to an `internal virtual` hook `_<name>`.
  The external functions are not `virtual`, so a subclass cannot drop the modifier.
* Each default `_<name>` reverts `HookNotImplemented` (BaseHook.sol:44-46, 57-59, ...).
  `AsyncSwap` overrides exactly three: `_beforeInitialize` (AsyncSwap.sol:162),
  `_beforeAddLiquidity` (AsyncSwap.sol:190) and `_beforeSwap` (AsyncSwap.sol:271).
* `AsyncSwap.getHookPermissions` (AsyncSwap.sol:170-187) sets `beforeInitialize`,
  `beforeAddLiquidity`, `beforeSwap` and `beforeSwapReturnDelta`.
* v4 only accepts a return-delta flag together with its action flag
  (Hooks.sol:111-119, `isValidHookAddress`).

The body of an overridden callback is abstract: the model only says whether the caller gate
lets the call reach it. Addresses are naturals; there is no state.
-/

namespace ProtocolProofs.Audit.HookGating

/-- The ten external callbacks of `IHooks`, in BaseHook.sol order. -/
inductive Callback where
  | beforeInitialize
  | afterInitialize
  | beforeAddLiquidity
  | beforeRemoveLiquidity
  | afterAddLiquidity
  | afterRemoveLiquidity
  | beforeSwap
  | afterSwap
  | beforeDonate
  | afterDonate
  deriving DecidableEq, Repr

/-- `Hooks.Permissions` (Hooks.sol:49-64), field order as in the struct. -/
structure Permissions where
  beforeInitialize : Bool
  afterInitialize : Bool
  beforeAddLiquidity : Bool
  afterAddLiquidity : Bool
  beforeRemoveLiquidity : Bool
  afterRemoveLiquidity : Bool
  beforeSwap : Bool
  afterSwap : Bool
  beforeDonate : Bool
  afterDonate : Bool
  beforeSwapReturnDelta : Bool
  afterSwapReturnDelta : Bool
  afterAddLiquidityReturnDelta : Bool
  afterRemoveLiquidityReturnDelta : Bool
  deriving DecidableEq, Repr

/-- `AsyncSwap.getHookPermissions` (AsyncSwap.sol:170-187). -/
def asyncSwapPermissions : Permissions where
  beforeInitialize := true
  afterInitialize := false
  beforeAddLiquidity := true
  afterAddLiquidity := false
  beforeRemoveLiquidity := false
  afterRemoveLiquidity := false
  beforeSwap := true
  afterSwap := false
  beforeDonate := false
  afterDonate := false
  beforeSwapReturnDelta := true
  afterSwapReturnDelta := false
  afterAddLiquidityReturnDelta := false
  afterRemoveLiquidityReturnDelta := false

/-- The action flag that makes the PoolManager call a callback. -/
def Permissions.enabled (p : Permissions) : Callback → Bool
  | .beforeInitialize => p.beforeInitialize
  | .afterInitialize => p.afterInitialize
  | .beforeAddLiquidity => p.beforeAddLiquidity
  | .beforeRemoveLiquidity => p.beforeRemoveLiquidity
  | .afterAddLiquidity => p.afterAddLiquidity
  | .afterRemoveLiquidity => p.afterRemoveLiquidity
  | .beforeSwap => p.beforeSwap
  | .afterSwap => p.afterSwap
  | .beforeDonate => p.beforeDonate
  | .afterDonate => p.afterDonate

/-- The internal hooks `AsyncSwap` overrides: `_beforeInitialize` (AsyncSwap.sol:162),
`_beforeAddLiquidity` (AsyncSwap.sol:190), `_beforeSwap` (AsyncSwap.sol:271). -/
def overridden : Callback → Bool
  | .beforeInitialize => true
  | .beforeAddLiquidity => true
  | .beforeSwap => true
  | _ => false

/-- What a call to an external callback does. -/
inductive Outcome where
  /-- `onlyPoolManager` reverted (ImmutableState.sol:16). -/
  | notPoolManager
  /-- the default `_<name>` of BaseHook reverted. -/
  | hookNotImplemented
  /-- control reached AsyncSwap's override. -/
  | runsBody
  deriving DecidableEq, Repr

/-- An external callback of BaseHook on AsyncSwap: the `onlyPoolManager` check, then the
internal hook (BaseHook.sol:36-207). -/
def callback (poolManager sender : Nat) (cb : Callback) : Outcome :=
  if sender ≠ poolManager then .notPoolManager
  else if overridden cb then .runsBody
  else .hookNotImplemented

/-- Every callback reverts `NotPoolManager` for any caller but the PoolManager, so no
callback body runs on another caller's behalf. -/
theorem hook_callbacks_onlyPoolManager (poolManager sender : Nat) (cb : Callback) :
    (sender ≠ poolManager → callback poolManager sender cb = .notPoolManager) ∧
      (callback poolManager sender cb ≠ .notPoolManager → sender = poolManager) := by
  unfold callback
  by_cases h : sender = poolManager <;> simp [h]

/-- Corollary: reaching an override implies the caller is the PoolManager. -/
theorem runsBody_sender (poolManager sender : Nat) (cb : Callback)
    (h : callback poolManager sender cb = .runsBody) : sender = poolManager :=
  (hook_callbacks_onlyPoolManager poolManager sender cb).2 (by rw [h]; decide)

/-! One statement per callback: from the PoolManager, the call reaches AsyncSwap's
override or the default revert; from anyone else it reverts at the gate. -/

theorem beforeInitialize_gate (pm s : Nat) :
    callback pm s .beforeInitialize = if s = pm then .runsBody else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem afterInitialize_gate (pm s : Nat) :
    callback pm s .afterInitialize = if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem beforeAddLiquidity_gate (pm s : Nat) :
    callback pm s .beforeAddLiquidity = if s = pm then .runsBody else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem beforeRemoveLiquidity_gate (pm s : Nat) :
    callback pm s .beforeRemoveLiquidity =
      if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem afterAddLiquidity_gate (pm s : Nat) :
    callback pm s .afterAddLiquidity = if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem afterRemoveLiquidity_gate (pm s : Nat) :
    callback pm s .afterRemoveLiquidity =
      if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem beforeSwap_gate (pm s : Nat) :
    callback pm s .beforeSwap = if s = pm then .runsBody else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem afterSwap_gate (pm s : Nat) :
    callback pm s .afterSwap = if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem beforeDonate_gate (pm s : Nat) :
    callback pm s .beforeDonate = if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

theorem afterDonate_gate (pm s : Nat) :
    callback pm s .afterDonate = if s = pm then .hookNotImplemented else .notPoolManager := by
  by_cases h : s = pm <;> simp [callback, overridden, h]

/-- The permission bits match the overrides: a callback is enabled exactly when AsyncSwap
overrides it, and the only return-delta flag set, `beforeSwapReturnDelta`, sits on an
enabled and overridden action (`_beforeSwap` returns a `BeforeSwapDelta`) and passes v4's
pairing rule (Hooks.sol:111-119). -/
theorem hook_permissions_match_overrides :
    (∀ cb, asyncSwapPermissions.enabled cb = overridden cb) ∧
      (asyncSwapPermissions.beforeSwapReturnDelta = true →
        asyncSwapPermissions.beforeSwap = true ∧ overridden .beforeSwap = true) ∧
      asyncSwapPermissions.afterSwapReturnDelta = false ∧
      asyncSwapPermissions.afterAddLiquidityReturnDelta = false ∧
      asyncSwapPermissions.afterRemoveLiquidityReturnDelta = false := by
  refine ⟨fun cb => ?_, fun _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  cases cb <;> rfl

/-- Hence the PoolManager never calls into a default `HookNotImplemented` revert: every
callback it is told to call reaches an override. -/
theorem enabled_runsBody (pm : Nat) (cb : Callback)
    (h : asyncSwapPermissions.enabled cb = true) : callback pm pm cb = .runsBody := by
  rw [hook_permissions_match_overrides.1] at h
  simp [callback, h]

end ProtocolProofs.Audit.HookGating
