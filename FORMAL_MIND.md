# Formal Mind changelog

Newest first. Every merged PR adds an entry.

## 2026-10-19 — AsyncSwap order escrow conservation

**Trigger:** swarm issue #4

New `FormalAgent/AsyncSwap/Orders.lean`: a model of the input leg of the AsyncSwap order book at
e230f5b (`_beforeSwap`/`_createOrder`, `AsyncFiller.fill`, `cancel`, `updatePrice`) with ghost
counters per input currency. Proved `escrow_conservation` (deposited = filled + refunded + open,
in every reachable state and currency), `paidOut_le_deposited`, `fill_pays_amountIn`,
`cancel_pays_amountIn`, and no double fill or refund (`fill_then_fill_none`, `cancel_then_none`).
v1 is full-fill only, so the input leg has no rounding. Authorization is not modelled (every
caller allowed), and keccak is taken as injective so an order id fixes its input currency.
