# Formal Mind changelog

Newest first. Every merged PR adds an entry.

## 2026-10-19 — audit: fee split in `AsyncFiller.fill` is exact

**Trigger:** swarm issue #10

**What:** New `ProtocolProofs/Audit/FeeSplit.lean` models `calculatePoolFee`
(src/AsyncSwap.sol:226) and the output leg of `AsyncFiller.fill`
(src/libraries/AsyncFiller.sol:119-125) at e230f5b. Proved `fill_fee_split_exact`
(maker + vault = gross, no dust) and `fill_maker_ge_minimum` (maker gets exactly the signed
minimum), plus `poolFee_eq` (the split formula is `amount * 3 / 997` rounded down),
`poolFee_le_30bps`, `poolFee_floor_30bps` and `fillOutput_isSome` (no overflow revert below
`2^256 * 997 / 1000`). No finding: rounding goes against the protocol, never the maker.

## 2026-10-19 audit: pool initialize and add-liquidity gating

**Trigger:** swarm issue #12

**What:** New `ProtocolProofs/Audit/PoolInit.lean` (and the `ProtocolProofs` library in
`lakefile.toml`). Models `AsyncSwap._beforeInitialize` (AsyncSwap.sol:162-167),
`_beforeAddLiquidity` (AsyncSwap.sol:190-197) and the v4 dispatch in
`Hooks.beforeModifyLiquidity` (Hooks.sol:195-206) as stateless functions over an abstract
`PoolKey`.

**Proved:** `beforeInitialize_accepts_iff` (accepted iff one side is the numeraire and
`fee = 0x800000`), `beforeInitialize_error` (which error, in Solidity order),
`beforeAddLiquidity_reverts`, `modifyLiquidity_passes_only_nonpositive`,
`liquidity_never_positive` / `fresh_pool_liquidity_zero` (no sequence of `modifyLiquidity`
calls can give an AsyncSwap pool positive liquidity).

**Result:** the invariant holds; no finding. Tick spacing and the hook address are not
constrained by the hook itself (PoolManager checks them), which is noted, not a bug.
