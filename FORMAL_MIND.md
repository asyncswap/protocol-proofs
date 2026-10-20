# Formal Mind changelog

Newest first. Every merged PR adds an entry.

## 2026-10-20 — audit: BaseHook callbacks gated to PoolManager; permission bits match overrides

**Trigger:** swarm issue #22

**What:** New `ProtocolProofs/Audit/HookGating.lean` models the ten external callbacks of
`BaseHook` (src/BaseHook.sol:36-207), the `onlyPoolManager` modifier
(src/ImmutableState.sol:15-18), the default `HookNotImplemented` reverts, the three internal
hooks `AsyncSwap` overrides (`_beforeInitialize`, `_beforeAddLiquidity`, `_beforeSwap`;
src/AsyncSwap.sol:162, 190, 271) and `getHookPermissions` (src/AsyncSwap.sol:170-187). The
issue named `Spec/Audit/`; the audit lives under `ProtocolProofs/Audit/`. No caller type from
#5 is on `main`, so addresses are naturals as in #12's `PoolInit.lean`.

**Proved:** `hook_callbacks_onlyPoolManager` (any caller but the PoolManager reverts
`NotPoolManager`, on every callback), `runsBody_sender`, one `<callback>_gate` theorem per
callback, `hook_permissions_match_overrides` (enabled ⇔ overridden for all ten callbacks;
`beforeSwapReturnDelta` sits on the enabled, overridden `beforeSwap`; the other return-delta
flags are off, so v4's pairing rule in Hooks.sol:111-119 holds), `enabled_runsBody` (the
PoolManager never hits a default revert).

**Result:** no finding. The external callbacks are not `virtual`, so the gate cannot be
dropped by a subclass; callback bodies are abstract here (#12 covers their logic).

## 2026-10-20 — audit: native ETH sent to the Router is never stranded (H-05 fix holds)

**Trigger:** swarm issue #21

**What:** New `ProtocolProofs/Audit/RouterNative.lean` tracks the raw ETH of the Router and
the hook and the hook's transient `PENDING_NATIVE_DEPOSIT` through every Router entry point:
`swap` with its `msg.value` checks and native settle (src/Router.sol:119-124, 254;
src/libraries/CurrencySettler.sol:21-22), `fillOrder` with the live-price check and forward to
the hook (src/Router.sol:152-163) on top of #19's `executeOrder`, the non-payable
`swapWithSig`/`cancelWithSig`/`cancelOrder`, and a plain transfer (the Router has no
`receive`/`fallback`).

**Proved:** `swap_native_exact` (native input: `msg.value = amountIn`, all of it settled to the
PoolManager; ERC20 input: `msg.value = 0`), `fillOrder_native_exact` (native output:
`msg.value = amountOutMin + calculatePoolFee(amountOutMin)` live, forwarded and pulled in full,
ledger restored; ERC20 output: `msg.value = 0`), `router_no_stranded_eth` (after any successful
Router call the Router's and the hook's ETH and the pending ledger are unchanged).

**Result:** no finding; H-05 is not present at e230f5b. Forced ETH sends (`selfdestruct`,
coinbase) are outside the model; PoolManager success is assumed.

## 2026-10-20 — audit: updatePrice front-run is bounded by maxPrice; native debit equals fill pull

**Trigger:** swarm issue #19

**What:** New `ProtocolProofs/Audit/UpdatePriceFill.lean` extends the #17 order book with
`calculatePoolFee` (src/AsyncSwap.sol:223-227), `AsyncFiller.fill` (src/libraries/AsyncFiller.sol:94-130),
`executeOrder` with the transient `PENDING_NATIVE_DEPOSIT` ledger (src/AsyncSwap.sol:233-254,
414-419) and `Router.fillOrder` with its callback (src/Router.sol:141-165, 256-277). The issue
named `FormalAgent/Audit/UpdatePrice.lean`; the audit lives under `ProtocolProofs/Audit/` and
`UpdatePrice.lean` is #17's, so this is a new sibling file.

**Proved:** `updatePrice_onlyMaker`, `updatePrice_rejects_zero`, `updatePrice_rejects_closed`,
`updatePrice_preserves_amountIn`; `executeOrder_native_debit_eq_pull` (the ledger drops by
exactly the ETH `fill` settles, `amountOutMin + calculatePoolFee(amountOutMin)`);
`fillOrder_paid_le_maxPrice` (a Router fill charges exactly the live price, at most `maxPrice`);
`fillOrder_native_pending_restored` (a native Router fill leaves the ledger where it found it);
`frontrun_bounded` (after any maker `updatePrice`, a fill that succeeds costs at most `maxPrice`,
for native output exactly `msg.value`, and the filler still gets the original `amountIn`).

**Result:** no finding. The front-run is lee-audit H-01, fixed by `maxPrice`; the native
overpay is H-05, fixed by `msg.value == livePrice`; both fixes hold at e230f5b. A filler who
passes `maxPrice = type(uint256).max` opts out of the cap, and an executor other than the Router
is the maker's own choice and gets no cap from the hook.

## 2026-10-20 — audit: updatePrice gating and escrow immutability

**Trigger:** swarm issue #17

**What:** New `ProtocolProofs/Audit/UpdatePrice.lean` models one pool's order book
(`orders[id] = {amountIn, amountOutMin}`, src/libraries/AsyncFiller.sol:26-33), the order id
as an abstract hash of `(pool, owner, zeroForOne, salt)` (src/types/AsyncOrder.sol:47-49),
`updatePrice` (src/AsyncSwap.sol:258-261, src/libraries/AsyncFiller.sol:71-85) and
`updatePriceWithSig` (src/AsyncSwap.sol:361-379) with the signature check as a boolean.

**Proved:** `updatePrice_auth` (caller is `order.owner` and the new limit is nonzero;
executors have no say), `updatePrice_requires_open` (reverts unless `amountIn ≠ 0`),
`updatePrice_preserves_escrow` (every `amountIn` unchanged, other orders untouched, only
`amountOutMin` of the addressed order set), `updatePrice_no_resurrect` (a closed record
stays as it is), `updatePrice_only_own_orders` (if the hash is injective, a changed record
belongs to the caller, so a stale or forged struct cannot reach another maker's order) and
`updatePriceWithSig_auth` (needs the maker's signature, then has the same effect as the maker
calling `updatePrice`).

**Result:** the invariant holds; no finding. The calldata `amountIn`/`amountOutMin` are
never read by this path, and the nonce map is outside the model.

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
