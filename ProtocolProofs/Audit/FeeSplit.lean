/-
Audit #10: the protocol fee split in `AsyncFiller.fill` (asyncswap/protocol @ e230f5b).

Solidity being modelled:

* `AsyncSwap.calculatePoolFee` (src/AsyncSwap.sol:223-227)
    `return (amount / 997) * 3 + ((amount % 997) * 3) / 997;`
* `AsyncSwap.executeOrder` (src/AsyncSwap.sol:252-253) passes
    `fee = calculatePoolFee(key.fee, orders[id].amountOutMin)` into `fill`.
* `AsyncFiller.fill` (src/libraries/AsyncFiller.sol:121-127), output leg:
    `settle(hook, amountOutMin + fee)` (native; ERC20 is pre-settled by the Router with the
    same `live + calculatePoolFee(live)`, src/Router.sol:262,275),
    `take(owner, amountOutMin)`, and if `fee != 0`, `take(feeVault, fee, claims)`.

Amounts are `Nat` with explicit `uint256` bounds. Checked arithmetic: `amountOutMin + fee`
reverts on overflow in 0.8.26, which the model reflects by returning `none`.
-/

namespace ProtocolProofs.Audit.FeeSplit

/-- `2^256`, the `uint256` modulus. -/
def UINT256 : Nat := 2 ^ 256

/-- `calculatePoolFee`, transcribed from src/AsyncSwap.sol:226. -/
def poolFee (amount : Nat) : Nat :=
  (amount / 997) * 3 + ((amount % 997) * 3) / 997

/-- Outcome of the output leg of a fill: what the filler settles, what the maker receives and
what the fee vault is minted. -/
structure OutputLeg where
  gross : Nat
  maker : Nat
  vault : Nat
  deriving Repr

/-- Output leg of `AsyncFiller.fill` for a stored `amountOutMin`. `none` is a revert: the
order is missing (`amountOutMin = 0` cannot be stored, see `updatePrice`'s `ZeroAmount`), or
`amountOutMin + fee` overflows `uint256`. -/
def fillOutput (amountOutMin : Nat) : Option OutputLeg :=
  let fee := poolFee amountOutMin
  if amountOutMin < UINT256 ∧ amountOutMin + fee < UINT256 then
    some { gross := amountOutMin + fee, maker := amountOutMin,
           vault := if fee ≠ 0 then fee else 0 }
  else none

/-- The split computation never overflows an intermediate: `amount % 997 * 3` is tiny and
`amount / 997 * 3 ≤ amount`. -/
theorem poolFee_le (amount : Nat) : poolFee amount ≤ amount := by
  unfold poolFee; omega

/-- The split formula equals the single-division `amount * 3 / 997`, rounded down. -/
theorem poolFee_eq (amount : Nat) : poolFee amount = amount * 3 / 997 := by
  unfold poolFee; omega

/-- The fee is at most 30 bps of the gross the filler pays (`net + fee`). -/
theorem poolFee_le_30bps (amount : Nat) :
    poolFee amount * 1000 ≤ 3 * (amount + poolFee amount) := by
  rw [poolFee_eq]; omega

/-- ...and rounding costs the protocol less than one unit: one more unit of fee would exceed
30 bps of the resulting gross. -/
theorem poolFee_floor_30bps (amount : Nat) :
    3 * (amount + poolFee amount + 1) < (poolFee amount + 1) * 1000 := by
  rw [poolFee_eq]; omega

/-- Exactness: whatever the filler settles is split between the maker and the fee vault with
no dust, so the hook's output delta nets to zero. -/
theorem fill_fee_split_exact (m : Nat) (leg : OutputLeg) (h : fillOutput m = some leg) :
    leg.maker + leg.vault = leg.gross ∧ leg.vault = poolFee m := by
  unfold fillOutput at h
  dsimp only at h
  split at h
  · cases h
    by_cases hf : poolFee m = 0 <;> simp [hf]
  · cases h

/-- The maker is never shorted: they receive exactly the signed minimum, at least that. -/
theorem fill_maker_ge_minimum (m : Nat) (leg : OutputLeg) (h : fillOutput m = some leg) :
    m ≤ leg.maker ∧ leg.maker = m := by
  unfold fillOutput at h
  dsimp only at h
  split at h
  · cases h; exact ⟨Nat.le_refl _, rfl⟩
  · cases h

/-- The fill only reverts on overflow for amounts within 0.3% of `2^256`: every
`amountOutMin < 2^256 * 997 / 1000` fills. -/
theorem fillOutput_isSome (m : Nat) (hm : m * 1000 < UINT256 * 997) :
    (fillOutput m).isSome := by
  unfold fillOutput
  have h3 := poolFee_eq m
  rw [if_pos ⟨by omega, by omega⟩]
  rfl

end ProtocolProofs.Audit.FeeSplit
