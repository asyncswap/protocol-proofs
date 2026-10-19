# Formal Mind changelog

Newest first. Every merged PR adds an entry.

## 2026-10-19 — audit: access control on cancel/fill and FeeVault withdrawals

**Trigger:** swarm issue #5

New `FormalAgent/Audit/Auth.lean`: a call-level model of every state-changing entry point of
`AsyncSwap.sol` and `FeeVault.sol` at e230f5b, with one authorisation theorem per entry point
(`createOrder_auth`, `executeOrder_auth`, `updatePrice_auth`, `updatePriceWithSig_auth`,
`cancelOrder_auth`, `setExecutor_auth`, `setExecutorWithSig_auth`, `transferOwnership_auth`,
`acceptOwnership_auth`, `sweep_auth`, `vault_auth`) and `orders_change_auth`: any change to an
order's record was made by its owner, an executor the owner authorised, or under the owner's
signature. Cancel and fill pay the maker (`order.owner`) only. No counterexample found.
Assumptions: keccak of the orderId preimage is injective; signature validity is an opaque
oracle; the PoolManager calls `unlockCallback` back only on the caller of `unlock`.
