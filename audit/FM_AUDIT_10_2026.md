# Formal Mind audit: asyncswap/protocol

- Commit: `e230f5b6b54bfb88e75e5e0eaadb04367a445769`
- Started: 2026-10-18
- Status: in progress

Each finding has a severity, the affected code, a Foundry POC that fails on the audited commit, the fix, and the Lean 4 proof that holds after the fix.

## Summary

| # | Title | Severity | POC | Fix | Proof |
| --- | --- | --- | --- | --- | --- |

## Findings

_None yet._

## Proved invariants

- **#12 Pool initialize and add-liquidity gating** (PR #14). `_beforeInitialize` accepts a key iff one currency is the numeraire and `fee = DYNAMIC_FEE_FLAG` (`beforeInitialize_accepts_iff`); `_beforeAddLiquidity` always reverts, so through v4's hook dispatch pool liquidity never goes above 0 (`liquidity_never_positive`). `ProtocolProofs/Audit/PoolInit.lean`. Tick spacing and the hook address are left to PoolManager.
