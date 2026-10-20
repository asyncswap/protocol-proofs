/-
Audit #18: order creation never overwrites a live order; `_beforeSwap` escrows the exact input
(asyncswap/protocol @ e230f5b).

Solidity being modelled:

* `AsyncSwap._beforeSwap` (src/AsyncSwap.sol:271-299):
    `if (params.amountSpecified > 0) revert ExactInputOnly();`               (276)
    `amountTaken = uint256(-params.amountSpecified);`                       (279)
    `if (sender != hookData.executor) revert NotAuthorizedExecutor();`      (283)
    `specified.take(poolManager, address(this), amountTaken, true);`        (288)
    `_createOrder(poolId, params.zeroForOne, amountTaken, hookData);`       (289)
    `amountTaken.toInt128()` in the event (292/294) reverts unless `amountTaken < 2^127`.
* `AsyncSwap._createOrder` (src/AsyncSwap.sol:302-327):
    `if (!state.isExecutor[user][executor]) revert NotAuthorizedExecutor();` (306)
    `if (amountIn == 0 || hookData.amountOutMin == 0) revert ZeroAmount();`  (307)
    `salt = keccak256(abi.encode(block.timestamp, block.number, msg.sender, user, amountIn, amountOutMin));`
    `id = keccak256(abi.encode(block.chainid, poolId, user, zeroForOne, salt));`
    `while (state.orders[id].amountIn != 0) { salt = keccak256(abi.encode(salt)); id = ...; }`
    `state.orders[id] = OrderInfo({amountIn: amountIn, amountOutMin: amountOutMin});` (325)
* `AsyncFiller.fill` / `cancel` end in `delete self.orders[id]`
  (src/libraries/AsyncFiller.sol:113,147), putting `amountIn` back to 0.

Model. The order book of one pool is a function `Id → Info`; a slot is live iff its `amountIn`
is nonzero. keccak is abstract: `rehash : Salt → Salt` is `keccak256(abi.encode(salt))` and
`idOf : Salt → Id` is the id preimage with chain id, pool id, maker and direction fixed. The
`while` loop is run with `fuel` iterations; running out of fuel is an out-of-gas revert
(`none`), so it can never write anything. `walk_isSome` says the walk does return when some
salt on the chain within the fuel lands on a free slot (finitely many live orders).

Id reuse. A deleted slot has `amountIn = 0`, so the walk accepts it again. The base salt
depends only on block timestamp and number, `msg.sender` (the PoolManager), the maker and
the two amounts, so the same maker opening an order with identical `(amountIn, amountOutMin)`
in the same block as a cancel or fill of an identical order gets the same id
(`id_reused_after_delete`). A pending fill, or an unused `updatePriceWithSig` signature
(whose hash binds the order struct, the id and `amountIn`, src/AsyncSwap.sol:370-373), then
applies to the new order, which has the same owner, direction, `amountIn` and initial
`amountOutMin` as the one it was written for; the nonce is still single-use. No loss: the
maker gets exactly the terms they signed or offered. Informational only.
-/

namespace ProtocolProofs.Audit.OrderCreate

abbrev Id := Nat
abbrev Salt := Nat
abbrev Addr := Nat

/-- `AsyncFiller.OrderInfo` (src/libraries/AsyncFiller.sol:26-29). -/
structure Info where
  amountIn : Nat
  amountOutMin : Nat
  deriving DecidableEq

abbrev Book := Id → Info

/-- Point update of the book. -/
def upd (b : Book) (i : Id) (v : Info) : Book :=
  fun j => if j = i then v else b j

/-- `delete self.orders[id]` (src/libraries/AsyncFiller.sol:113,147). -/
def del (b : Book) (i : Id) : Book := upd b i ⟨0, 0⟩

/-- The collision walk (src/AsyncSwap.sol:320-323) with `fuel` iterations; returns the free
id and the salt it came from, or `none` when gas runs out. -/
def walk (rehash : Salt → Salt) (idOf : Salt → Id) (b : Book) : Nat → Salt → Option (Id × Salt)
  | 0, _ => none
  | fuel + 1, s =>
    if (b (idOf s)).amountIn = 0 then some (idOf s, s)
    else walk rehash idOf b fuel (rehash s)

/-- The `k`-th salt on the rehash chain. -/
def iter (rehash : Salt → Salt) : Nat → Salt → Salt
  | 0, s => s
  | k + 1, s => iter rehash k (rehash s)

/-- `_createOrder` (src/AsyncSwap.sol:302-327). `authorized` is
`state.isExecutor[user][executor]`, `salt0` the base salt. -/
def createOrder (rehash : Salt → Salt) (idOf : Salt → Id) (b : Book) (authorized : Bool)
    (amountIn amountOutMin fuel : Nat) (salt0 : Salt) : Option (Book × Id) :=
  if authorized = true ∧ amountIn ≠ 0 ∧ amountOutMin ≠ 0 then
    match walk rehash idOf b fuel salt0 with
    | some (i, _) => some (upd b i ⟨amountIn, amountOutMin⟩, i)
    | none => none
  else none

/-- `_beforeSwap` (src/AsyncSwap.sol:271-299): returns the amount taken as claims into escrow
(line 288), the new book and the new id. -/
def beforeSwap (rehash : Salt → Salt) (idOf : Salt → Id) (b : Book) (authorized : Bool)
    (sender executor : Addr) (amountSpecified : Int) (amountOutMin fuel : Nat) (salt0 : Salt) :
    Option (Nat × Book × Id) :=
  if amountSpecified ≤ 0 ∧ sender = executor ∧ (-amountSpecified).toNat < 2 ^ 127 then
    match createOrder rehash idOf b authorized (-amountSpecified).toNat amountOutMin fuel salt0 with
    | some (b', i) => some ((-amountSpecified).toNat, b', i)
    | none => none
  else none

variable {rehash : Salt → Salt} {idOf : Salt → Id}

/-- The walk only ever returns a free slot. -/
theorem walk_free {b : Book} :
    ∀ {fuel : Nat} {s : Salt} {i : Id} {s' : Salt},
      walk rehash idOf b fuel s = some (i, s') → (b i).amountIn = 0 ∧ i = idOf s'
  | 0, _, _, _, h => by simp [walk] at h
  | fuel + 1, s, i, s', h => by
    simp only [walk] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by assumption, rfl⟩
    · exact walk_free h

/-- The walk returns as soon as some salt on the rehash chain, within the fuel, is free. -/
theorem walk_isSome {b : Book} :
    ∀ {fuel : Nat} {s : Salt} (k : Nat), k < fuel →
      (b (idOf (iter rehash k s))).amountIn = 0 → (walk rehash idOf b fuel s).isSome
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | fuel + 1, s, k, hk, hfree => by
    simp only [walk]
    split
    · rfl
    · cases k with
      | zero => contradiction
      | succ k =>
        exact walk_isSome k (by omega) hfree

/-- If the base slot is free the order gets the base id. -/
theorem walk_base {b : Book} {fuel : Nat} {s : Salt} (hf : 0 < fuel)
    (hfree : (b (idOf s)).amountIn = 0) : walk rehash idOf b fuel s = some (idOf s, s) := by
  cases fuel with
  | zero => contradiction
  | succ n => simp [walk, hfree]

theorem createOrder_some {b : Book} {auth : Bool} {aIn aOut fuel : Nat} {s0 : Salt}
    {b' : Book} {i : Id} (h : createOrder rehash idOf b auth aIn aOut fuel s0 = some (b', i)) :
    auth = true ∧ aIn ≠ 0 ∧ aOut ≠ 0 ∧ (b i).amountIn = 0 ∧
      b' = upd b i ⟨aIn, aOut⟩ := by
  unfold createOrder at h
  split at h
  · rename_i hg
    split at h
    · rename_i i' s' hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hg.1, hg.2.1, hg.2.2, (walk_free hw).1, rfl⟩
    · simp at h
  · simp at h

/-- Creating an order never touches a live order: every slot with nonzero `amountIn` keeps its
`OrderInfo`. (Reverts change nothing at all.) -/
theorem createOrder_preserves_live {b : Book} {auth : Bool} {aIn aOut fuel : Nat} {s0 : Salt}
    {b' : Book} {i : Id} (h : createOrder rehash idOf b auth aIn aOut fuel s0 = some (b', i)) :
    ∀ j, (b j).amountIn ≠ 0 → b' j = b j := by
  obtain ⟨-, -, -, hfree, rfl⟩ := createOrder_some h
  intro j hj
  have : j ≠ i := fun e => hj (e ▸ hfree)
  simp [upd, this]

/-- The new slot was free and now holds exactly `(amountIn, amountOutMin)`, both nonzero;
every other slot is unchanged. -/
theorem createOrder_slot {b : Book} {auth : Bool} {aIn aOut fuel : Nat} {s0 : Salt}
    {b' : Book} {i : Id} (h : createOrder rehash idOf b auth aIn aOut fuel s0 = some (b', i)) :
    (b i).amountIn = 0 ∧ b' i = ⟨aIn, aOut⟩ ∧ aIn ≠ 0 ∧ aOut ≠ 0 ∧
      ∀ j, j ≠ i → b' j = b j := by
  obtain ⟨-, hin, hout, hfree, rfl⟩ := createOrder_some h
  refine ⟨hfree, by simp [upd], hin, hout, fun j hj => by simp [upd, hj]⟩

/-- `_beforeSwap` escrows exactly `uint256(-amountSpecified)`, and that is the new order's
`amountIn`; every live order is untouched. -/
theorem beforeSwap_escrow_eq_input {b : Book} {auth : Bool} {sender executor : Addr}
    {amt : Int} {aOut fuel : Nat} {s0 : Salt} {e : Nat} {b' : Book} {i : Id}
    (h : beforeSwap rehash idOf b auth sender executor amt aOut fuel s0 = some (e, b', i)) :
    (e : Int) = -amt ∧ 0 < e ∧ b' i = ⟨e, aOut⟩ ∧ ∀ j, (b j).amountIn ≠ 0 → b' j = b j := by
  unfold beforeSwap at h
  split at h
  · rename_i hg
    split at h
    · rename_i b'' i' hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨-, hs, hin, -, -⟩ := createOrder_slot hc
      refine ⟨by omega, by omega, hs, createOrder_preserves_live hc⟩
    · simp at h
  · simp at h

/-- Exact-output swaps (`amountSpecified > 0`) and swaps whose caller is not the declared
executor revert; so does a zero-amount swap. -/
theorem beforeSwap_exactInputOnly (b : Book) (auth : Bool) (sender executor : Addr)
    (amt : Int) (aOut fuel : Nat) (s0 : Salt) :
    (0 < amt → beforeSwap rehash idOf b auth sender executor amt aOut fuel s0 = none) ∧
    (sender ≠ executor → beforeSwap rehash idOf b auth sender executor amt aOut fuel s0 = none) ∧
    (amt = 0 → beforeSwap rehash idOf b auth sender executor amt aOut fuel s0 = none) := by
  refine ⟨fun hp => ?_, fun hne => ?_, fun hz => ?_⟩
  · unfold beforeSwap
    rw [if_neg (by omega)]
  · unfold beforeSwap
    rw [if_neg (fun hg => hne hg.2.1)]
  · subst hz
    unfold beforeSwap createOrder
    split <;> simp

/-- Id reuse is possible: after an order at the base id is deleted (filled or cancelled), an
order created from the same base salt lands on the same id. -/
theorem id_reused_after_delete {b : Book} {aIn aOut fuel : Nat} {s0 : Salt}
    (hin : aIn ≠ 0) (hout : aOut ≠ 0) (hf : 0 < fuel) :
    createOrder rehash idOf (del b (idOf s0)) true aIn aOut fuel s0 =
      some (upd (del b (idOf s0)) (idOf s0) ⟨aIn, aOut⟩, idOf s0) := by
  have hfree : (del b (idOf s0) (idOf s0)).amountIn = 0 := by simp [del, upd]
  simp [createOrder, hin, hout, walk_base hf hfree]

end ProtocolProofs.Audit.OrderCreate
