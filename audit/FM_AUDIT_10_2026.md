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
- **#11 Owner sweep and FeeVault collect cannot reach maker escrow** (PR #15). Only the owner can call `sweep` or `collect`. `sweep` pays out exactly the hook's raw token balance (`sweep_preserves_escrow`), and `collect` pays out exactly the vault's own ERC-6909 claims (`collect_only_fees`). Neither one changes the hook's claims or escrow. Escrow never exceeds the hook's claims after any history (`step_inv`, `run_inv`, `init_inv`), and every open order can still be cancelled after any number of sweeps and collects (`cancel_reachable`). `ProtocolProofs/Audit/OwnerPowers.lean`. The order book is modelled only as its per-currency sum of `amountIn`.
- **#17 updatePrice is maker-only and never touches escrow** (PR #24). Only `order.owner` can update, and only to a nonzero limit; executors have no say (`updatePrice_auth`). It reverts on filled, cancelled or never-created orders (`updatePrice_requires_open`), and it writes only the addressed order's `amountOutMin`: every `amountIn` and every other order stays as it was (`updatePrice_preserves_escrow`, `updatePrice_no_resurrect`). If keccak is collision-free, a changed record belongs to the caller (`updatePrice_only_own_orders`). `updatePriceWithSig` needs the maker's signature and then does exactly what the maker's own call does (`updatePriceWithSig_auth`). `ProtocolProofs/Audit/UpdatePrice.lean`. The signature check is a boolean, and the nonce map is not modelled.
- **#19 updatePrice front-run of a fill is bounded by maxPrice; native debit equals the fill pull** (PR #26). No finding: the front-run is lee-audit H-01 and the native overpay is H-05, and both fixes hold at the audit commit. After any maker `updatePrice`, a Router `fillOrder` that succeeds charges exactly the live price `amountOutMin + calculatePoolFee(amountOutMin)`, never more than the filler's `maxPrice` (exactly `msg.value` for native output), and the filler still receives the original `amountIn` (`frontrun_bounded`, `fillOrder_paid_le_maxPrice`). For native output `executeOrder` lowers `PENDING_NATIVE_DEPOSIT` by exactly the ETH `fill` settles (`executeOrder_native_debit_eq_pull`), so a native Router fill leaves the ledger where it found it (`fillOrder_native_pending_restored`). `ProtocolProofs/Audit/UpdatePriceFill.lean`. The Router's two live-price reads are modelled as one (only the hook's `receive` runs between them). PM deltas other than the native pull are not modelled. A filler who passes `maxPrice = type(uint256).max` turns the cap off, and an executor other than the Router gets no cap from the hook.
