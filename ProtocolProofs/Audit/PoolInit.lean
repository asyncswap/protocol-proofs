/-
# Audit: pool initialize and add-liquidity gating (swarm issue #12)

Model of the two hook gates in `protocol/src/AsyncSwap.sol` at e230f5b, and of the
Uniswap v4 dispatch that decides when they run
(`protocol/dependencies/v4-core/src/libraries/Hooks.sol`).

* `AsyncSwap._beforeInitialize` (AsyncSwap.sol:162-167): reverts `NumeraireRequired` unless
  one side of the key is the numeraire, then `DynamicFeeRequired` unless
  `key.fee == LPFeeLibrary.DYNAMIC_FEE_FLAG` (`0x800000`, LPFeeLibrary.sol:15).
  Nothing else in the key is checked here; tick spacing, currency order and the hook
  address are checked by `PoolManager.initialize` (PoolManager.sol:119-126).
* `AsyncSwap._beforeAddLiquidity` (AsyncSwap.sol:190-197) reverts `UnsupportedLiquidity`
  unconditionally.
* `Hooks.beforeModifyLiquidity` (Hooks.sol:195-206) calls `beforeAddLiquidity` iff
  `liquidityDelta > 0` and the hook has the flag (AsyncSwap does, AsyncSwap.sol:173), and
  calls `beforeRemoveLiquidity` for `liquidityDelta ≤ 0` only if that flag is set (it is
  not, AsyncSwap.sol:175). The `noSelfCall` skip does not apply: AsyncSwap never calls
  `modifyLiquidity` itself.

Addresses and currencies are abstract naturals; the model has no state.
-/

namespace ProtocolProofs.Audit.PoolInit

/-- `LPFeeLibrary.DYNAMIC_FEE_FLAG` (LPFeeLibrary.sol:15). -/
def DYNAMIC_FEE_FLAG : Nat := 0x800000

/-- The fields of a v4 `PoolKey` (PoolKey.sol): currencies and hooks are addresses. -/
structure PoolKey where
  currency0 : Nat
  currency1 : Nat
  fee : Nat
  tickSpacing : Int
  hooks : Nat
  deriving DecidableEq, Repr

/-- The custom errors the two gates can raise. -/
inductive HookError where
  | NumeraireRequired
  | DynamicFeeRequired
  | UnsupportedLiquidity
  deriving DecidableEq, Repr

/-- `_beforeInitialize` (AsyncSwap.sol:162-167): `none` means it returned the selector. -/
def beforeInitialize (numeraire : Nat) (key : PoolKey) : Option HookError :=
  if !(key.currency0 == numeraire || key.currency1 == numeraire) then
    some .NumeraireRequired
  else if key.fee != DYNAMIC_FEE_FLAG then
    some .DynamicFeeRequired
  else
    none

/-- The Bool predicate of the issue: the hook accepts this key. -/
def initAccepts (numeraire : Nat) (key : PoolKey) : Bool :=
  (beforeInitialize numeraire key).isNone

/-- `_beforeAddLiquidity` (AsyncSwap.sol:190-197): every argument is ignored. -/
def beforeAddLiquidity (_key : PoolKey) (_liquidityDelta : Int) : Option HookError :=
  some .UnsupportedLiquidity

/-- `Hooks.beforeModifyLiquidity` (Hooks.sol:201-205) specialised to AsyncSwap's
permissions: `beforeAddLiquidity` is set, `beforeRemoveLiquidity` is not. `none` means the
call goes on to the pool. -/
def beforeModifyLiquidity (key : PoolKey) (liquidityDelta : Int) : Option HookError :=
  if liquidityDelta > 0 then beforeAddLiquidity key liquidityDelta else none

/-- A key is accepted exactly when it touches the numeraire and carries the dynamic-fee
flag. Nothing about tick spacing or the hook address is constrained by the hook. -/
theorem beforeInitialize_accepts_iff (numeraire : Nat) (key : PoolKey) :
    initAccepts numeraire key = true ↔
      (key.currency0 = numeraire ∨ key.currency1 = numeraire) ∧ key.fee = DYNAMIC_FEE_FLAG := by
  unfold initAccepts beforeInitialize
  by_cases h0 : key.currency0 = numeraire <;> by_cases h1 : key.currency1 = numeraire <;>
    by_cases hf : key.fee = DYNAMIC_FEE_FLAG <;> simp [h0, h1, hf]

/-- The error on rejection is the first failing check, in Solidity order. -/
theorem beforeInitialize_error (numeraire : Nat) (key : PoolKey) :
    beforeInitialize numeraire key =
      if key.currency0 ≠ numeraire ∧ key.currency1 ≠ numeraire then some .NumeraireRequired
      else if key.fee ≠ DYNAMIC_FEE_FLAG then some .DynamicFeeRequired
      else none := by
  unfold beforeInitialize
  by_cases h0 : key.currency0 = numeraire <;> by_cases h1 : key.currency1 = numeraire <;>
    by_cases hf : key.fee = DYNAMIC_FEE_FLAG <;> simp [h0, h1, hf]

/-- `_beforeAddLiquidity` reverts for every key and every parameter. -/
theorem beforeAddLiquidity_reverts (key : PoolKey) (liquidityDelta : Int) :
    beforeAddLiquidity key liquidityDelta = some .UnsupportedLiquidity := rfl

/-- Through the v4 dispatch: any `modifyLiquidity` on an AsyncSwap pool that the hook lets
through has `liquidityDelta ≤ 0`, so no liquidity can ever be added. -/
theorem modifyLiquidity_passes_only_nonpositive (key : PoolKey) (liquidityDelta : Int)
    (h : beforeModifyLiquidity key liquidityDelta = none) : liquidityDelta ≤ 0 := by
  unfold beforeModifyLiquidity beforeAddLiquidity at h
  by_cases hd : liquidityDelta > 0
  · simp [hd] at h
  · omega

/-- Pool liquidity after a sequence of `modifyLiquidity` calls, each applied only if the hook
lets it through (a revert leaves liquidity unchanged). -/
def applyAll (key : PoolKey) : Int → List Int → Int
  | l, [] => l
  | l, d :: ds =>
    match beforeModifyLiquidity key d with
    | none => applyAll key (l + d) ds
    | some _ => applyAll key l ds

/-- Starting from a fresh pool (liquidity 0), liquidity never becomes positive, so every swap
on an AsyncSwap pool goes through `_beforeSwap` against zero in-range liquidity: there is no
AMM curve to bypass the order book with. -/
theorem liquidity_never_positive (key : PoolKey) (ds : List Int) (l : Int) (hl : l ≤ 0) :
    applyAll key l ds ≤ 0 := by
  induction ds generalizing l with
  | nil => exact hl
  | cons d ds ih =>
    unfold applyAll
    split
    · rename_i h
      have := modifyLiquidity_passes_only_nonpositive key d h
      exact ih _ (by omega)
    · exact ih _ hl

theorem fresh_pool_liquidity_zero (key : PoolKey) (ds : List Int) :
    applyAll key 0 ds ≤ 0 :=
  liquidity_never_positive key ds 0 (Int.le_refl 0)

end ProtocolProofs.Audit.PoolInit
