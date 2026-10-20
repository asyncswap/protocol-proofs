# Formal Mind changelog

Newest first. Every merged PR adds an entry.

## 2026-10-20 audit: two-step ownership handover

**Trigger:** swarm issue #16

**What:** New `ProtocolProofs/Audit/Ownership.lean`. Models the `owner` / `pendingOwner`
slots of `AsyncSwap` (AsyncSwap.sol:40-43): the constructor (:120-130), `onlyOwner`
(:94-97), `transferOwnership` (:135-139) and `acceptOwnership` (:142-147). Every other
entry point is the identity on these slots (nothing else in `protocol/src` writes them).

**Proved:** `transferOwnership_onlyOwner`, `acceptOwnership_onlyPending`,
`acceptOwnership_clears_pending`, `owner_reachable_only_via_accept` (the owner changes only
by `acceptOwnership` from the pending address), `pending_set_only_by_owner`,
`reachable_owner_ne_zero` (no reachable state has `owner == address(0)`, assuming the EVM
fact that `msg.sender` is never `address(0)`).

**Result:** the invariant holds; no finding. The owner can re-nominate over a pending
nominee at any time and cannot cancel to `address(0)` (only by nominating itself); both are
by design, not bugs.

## 2026-10-19 — audit: owner sweep and FeeVault collect cannot reach maker escrow

**Trigger:** swarm issue #11

**What:** New `ProtocolProofs/Audit/OwnerPowers.lean` models, per currency, the hook's raw
balance, the hook's and the vault's ERC-6909 claims, and open-order escrow at e230f5b, with
`sweep` (src/AsyncSwap.sol:154-159), `FeeVault.collect`/`unlockCallback`
(src/FeeVault.sol:27-45), order create (src/AsyncSwap.sol:288,325), `fill` and `cancel`
(src/libraries/AsyncFiller.sol:113-127,147-152), and anyone's donations of tokens or claims.
Proved `sweep_preserves_escrow` (owner-only, pays exactly the raw balance, claims and escrow
unchanged), `collect_only_fees` (owner-only, pays exactly the vault's claims, hook balance,
claims and escrow unchanged), `step_inv`/`run_inv` (escrow ≤ hook claims after any history)
and `cancel_reachable` (every open order stays cancellable after any sweeps and collects).
No finding. The order book is abstracted to its per-currency sum of `amountIn`.
The file is imported from `ProtocolProofs.lean`; the library itself came with #14.

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
