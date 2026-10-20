/-
Audit #30: executor authorization is revocable and scoped to one (pool, maker)
(asyncswap/protocol @ e230f5b).

Solidity being modelled:

* `AsyncFiller.State.isExecutor` (src/libraries/AsyncFiller.sol:34) is a per-pool map
  `owner → executor → bool`; the hook keeps one `State` per `PoolId` (`asyncOrders[poolId]`).
* `setExecutor(poolId, executor, allow)` (src/AsyncSwap.sol:332-335) writes
  `asyncOrders[poolId].isExecutor[msg.sender][executor] = allow`.
* `setExecutorWithSig(key, maker, executor, allow, nonce, deadline, signature)`
  (src/AsyncSwap.sol:339-358) runs `_verify` (src/AsyncSwap.sol:395-405): reverts if
  `block.timestamp > deadline` or `nonceUsed[maker][nonce]`, sets `nonceUsed[maker][nonce] = true`,
  then reverts unless `signature` is `maker`'s over
  `hashSetExecutor(key, maker, executor, allow, nonce, deadline)` (src/libraries/OrderSignatures.sol:87-96).
  On success it writes `asyncOrders[key.toId()].isExecutor[maker][executor] = allow`.
* `invalidateNonce(nonce)` (src/AsyncSwap.sol:382-386) burns `nonceUsed[msg.sender][nonce]`.
  `updatePriceWithSig` (src/AsyncSwap.sol:361-379) burns nonces from the same space.
* `AsyncFiller.fill` (src/libraries/AsyncFiller.sol:104) requires
  `isExecutor[order.owner][executor]` on the order's pool, with `executor = msg.sender` of
  `executeOrder` (src/AsyncSwap.sol:254).
* `AsyncFiller.cancel` (src/libraries/AsyncFiller.sol:139) requires
  `executor = order.owner ∨ isExecutor[order.owner][executor]`.
* `AsyncFiller.updatePrice` (src/libraries/AsyncFiller.sol:78) requires `caller = order.owner`
  and never reads `isExecutor`; `updatePrice` passes `msg.sender` (src/AsyncSwap.sol:259),
  `updatePriceWithSig` passes `order.owner` after `_verify` against `order.owner`.
* `_createOrder` (src/AsyncSwap.sol:306) requires `isExecutor[hookData.user][hookData.executor]`
  with `sender = hookData.executor` (src/AsyncSwap.sol:283).

Model: the signature check is an abstract predicate `signed maker g` ("`maker` signed the
`SetExecutor` struct `g`"). EIP-712 hashing is assumed collision-free, so a signature over one
struct says nothing about a struct with a different pool, executor, `allow` or nonce. A
reverting call is `none`; the nonce burn inside a reverting `_verify` is rolled back with it.
-/

namespace ProtocolProofs.Audit.Executor

abbrev Addr := Nat
abbrev Pool := Nat

/-- The fields of an EIP-712 `SetExecutor` struct (src/libraries/OrderSignatures.sol:37). -/
structure Grant where
  maker : Addr
  executor : Addr
  allow : Bool
  pool : Pool
  nonce : Nat
  deadline : Nat

structure St where
  /-- `asyncOrders[pool].isExecutor[maker][executor]`. -/
  isExec : Pool → Addr → Addr → Bool
  /-- `nonceUsed[maker][nonce]`. -/
  nonceUsed : Addr → Nat → Bool
  /-- `block.timestamp`. -/
  now : Nat

/-- An order, as far as authorization goes: its pool (`order.key.toId()`) and owner. -/
structure Order where
  pool : Pool
  owner : Addr

/-- `isExecutor[pool][maker][executor] := allow`, every other entry unchanged. -/
def setAuth (f : Pool → Addr → Addr → Bool) (p : Pool) (m e : Addr) (allow : Bool) :
    Pool → Addr → Addr → Bool :=
  fun p' m' e' => if p' = p ∧ m' = m ∧ e' = e then allow else f p' m' e'

/-- `nonceUsed[maker][nonce] := true`. -/
def burn (f : Addr → Nat → Bool) (m : Addr) (n : Nat) : Addr → Nat → Bool :=
  fun m' n' => if m' = m ∧ n' = n then true else f m' n'

/-- `setExecutor`, called by `caller`. -/
def setExecutor (s : St) (caller : Addr) (p : Pool) (e : Addr) (allow : Bool) : St :=
  { s with isExec := setAuth s.isExec p caller e allow }

/-- `setExecutorWithSig`, submitted by anyone, with `_verify` inlined. -/
def setExecutorWithSig (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s : St) (g : Grant) : Option St :=
  if s.now ≤ g.deadline ∧ s.nonceUsed g.maker g.nonce = false ∧ signed g.maker g then
    some { s with nonceUsed := burn s.nonceUsed g.maker g.nonce,
                  isExec := setAuth s.isExec g.pool g.maker g.executor g.allow }
  else none

/-- `invalidateNonce`, called by `caller`. -/
def invalidateNonce (s : St) (caller : Addr) (n : Nat) : Option St :=
  if s.nonceUsed caller n = false then
    some { s with nonceUsed := burn s.nonceUsed caller n }
  else none

/-- The authorization guard of `AsyncFiller.fill` for `executeOrder` called by `executor`. -/
def canFill (s : St) (o : Order) (executor : Addr) : Prop :=
  s.isExec o.pool o.owner executor = true

/-- The authorization guard of `AsyncFiller.cancel`. -/
def canCancel (s : St) (o : Order) (executor : Addr) : Prop :=
  executor = o.owner ∨ s.isExec o.pool o.owner executor = true

/-- The authorization guard of `AsyncFiller.updatePrice`: the effective caller is the owner. -/
def canUpdatePrice (o : Order) (caller : Addr) : Prop :=
  caller = o.owner

/-- The authorization guard of `_createOrder` for a swap by `sender` on `pool` for `user`. -/
def canCreate (s : St) (p : Pool) (user sender : Addr) : Prop :=
  s.isExec p user sender = true

theorem setAuth_self (f : Pool → Addr → Addr → Bool) (p : Pool) (m e : Addr) (allow : Bool) :
    setAuth f p m e allow p m e = allow := by
  simp only [setAuth, and_self, if_true]

theorem setAuth_other (f : Pool → Addr → Addr → Bool) (p p' : Pool) (m m' e e' : Addr)
    (allow : Bool) (h : ¬ (p' = p ∧ m' = m ∧ e' = e)) :
    setAuth f p m e allow p' m' e' = f p' m' e' := by
  simp only [setAuth, if_neg h]

/-! ### Revocation -/

/-- After `setExecutor(pool, e, false)` by the maker, `e` cannot fill that maker's orders on that
pool. -/
theorem revoke_executor_blocks_fill (s : St) (maker e : Addr) (o : Order)
    (hOwner : o.owner = maker) :
    ¬ canFill (setExecutor s maker o.pool e false) o e := by
  subst hOwner
  simp only [canFill, setExecutor, setAuth_self, Bool.false_eq_true, not_false_eq_true]

/-- After revocation, `e` cannot cancel the maker's orders on that pool unless `e` is the maker
itself (a maker may always cancel its own order, src/libraries/AsyncFiller.sol:139). -/
theorem revoke_executor_blocks_cancel (s : St) (maker e : Addr) (o : Order)
    (hOwner : o.owner = maker) (hNotMaker : e ≠ maker) :
    ¬ canCancel (setExecutor s maker o.pool e false) o e := by
  subst hOwner
  simp only [canCancel, setExecutor, setAuth_self, Bool.false_eq_true, or_false]
  exact hNotMaker

/-- No executor can ever reprice an order that is not its own: `updatePrice` never consults the
grant, so revocation is not needed to block it. -/
theorem executor_never_updates_price (o : Order) (e : Addr) (hNotMaker : e ≠ o.owner) :
    ¬ canUpdatePrice o e := hNotMaker

/-- After revocation, `e` cannot open new orders for the maker on that pool either. -/
theorem revoke_executor_blocks_create (s : St) (maker e : Addr) (p : Pool) :
    ¬ canCreate (setExecutor s maker p e false) p maker e := by
  simp only [canCreate, setExecutor, setAuth_self, Bool.false_eq_true, not_false_eq_true]

/-- A signed revocation that goes through has the same effect. -/
theorem revoke_with_sig_blocks_fill (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (g : Grant) (o : Order) (hAllow : g.allow = false)
    (hPool : o.pool = g.pool) (hOwner : o.owner = g.maker)
    (h : setExecutorWithSig signed s g = some s') :
    ¬ canFill s' o g.executor ∧ (g.executor ≠ g.maker → ¬ canCancel s' o g.executor) := by
  unfold setExecutorWithSig at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [canFill, canCancel, hPool, hOwner, setAuth_self, hAllow, Bool.false_eq_true,
      not_false_eq_true, or_false, true_and]
    exact id
  · exact absurd h (by simp)

/-! ### Scoping -/

/-- `setExecutor` by `caller` changes only the entry `(pool, caller, executor)`: no other maker's
grant and no other pool's grant moves. -/
theorem setExecutor_scoped_to_owner_pool (s : St) (caller e : Addr) (p : Pool) (allow : Bool)
    (p' : Pool) (m' e' : Addr) (h : ¬ (p' = p ∧ m' = caller ∧ e' = e)) :
    (setExecutor s caller p e allow).isExec p' m' e' = s.isExec p' m' e' :=
  setAuth_other _ _ _ _ _ _ _ _ h

/-- Corollary: a call by `caller` never makes anyone an executor for a different maker. -/
theorem setExecutor_no_cross_maker (s : St) (caller e : Addr) (p : Pool) (allow : Bool)
    (o : Order) (x : Addr) (hOther : o.owner ≠ caller) :
    canFill (setExecutor s caller p e allow) o x ↔ canFill s o x := by
  unfold canFill
  rw [setExecutor_scoped_to_owner_pool s caller e p allow o.pool o.owner x
    (fun h => hOther h.2.1)]

/-- Corollary: a grant on pool `p` never covers an order on another pool. -/
theorem setExecutor_no_cross_pool (s : St) (caller e : Addr) (p : Pool) (allow : Bool)
    (o : Order) (x : Addr) (hOther : o.pool ≠ p) :
    canFill (setExecutor s caller p e allow) o x ↔ canFill s o x := by
  unfold canFill
  rw [setExecutor_scoped_to_owner_pool s caller e p allow o.pool o.owner x
    (fun h => hOther h.1)]

/-- `setExecutorWithSig` changes only the signed entry `(g.pool, g.maker, g.executor)` and only
burns `g.maker`'s nonce `g.nonce`; it can only succeed with `g.maker`'s own signature over that
exact struct, before its deadline. -/
theorem setExecutorWithSig_scoped (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (g : Grant) (h : setExecutorWithSig signed s g = some s') :
    signed g.maker g ∧ s.now ≤ g.deadline ∧ s.nonceUsed g.maker g.nonce = false ∧
      s'.isExec g.pool g.maker g.executor = g.allow ∧
      (∀ p m e, ¬ (p = g.pool ∧ m = g.maker ∧ e = g.executor) → s'.isExec p m e = s.isExec p m e) ∧
      (∀ m n, ¬ (m = g.maker ∧ n = g.nonce) → s'.nonceUsed m n = s.nonceUsed m n) ∧
      s'.now = s.now := by
  unfold setExecutorWithSig at h
  split at h
  · rename_i hg
    obtain ⟨hd, hn, hs⟩ := hg
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hs, hd, hn, setAuth_self _ _ _ _ _, fun p m e hne => setAuth_other _ _ _ _ _ _ _ _ hne,
      fun m n hne => ?_, rfl⟩
    simp only [burn, if_neg hne]
  · exact absurd h (by simp)

/-! ### No replay -/

/-- Nonces are never un-burnt by any entry point modelled here. -/
theorem setExecutorWithSig_burns (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (g : Grant) (h : setExecutorWithSig signed s g = some s') :
    s'.nonceUsed g.maker g.nonce = true ∧ ∀ m n, s.nonceUsed m n = true → s'.nonceUsed m n = true := by
  unfold setExecutorWithSig at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨by simp only [burn, and_self, if_true], fun m n hmn => ?_⟩
    simp only [burn]
    split <;> simp only [hmn]
  · exact absurd h (by simp)

/-- Replaying a used `SetExecutor` grant (any struct with the same maker and nonce, in particular
the same signature) always reverts. -/
theorem setExecutorWithSig_no_replay (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (g g' : Grant) (h : setExecutorWithSig signed s g = some s')
    (hm : g'.maker = g.maker) (hn : g'.nonce = g.nonce) :
    setExecutorWithSig signed s' g' = none := by
  have hb := (setExecutorWithSig_burns signed s s' g h).1
  unfold setExecutorWithSig
  rw [hm, hn, hb]
  simp

/-- After the maker calls `invalidateNonce(n)`, no grant signed with nonce `n` can ever be
submitted. -/
theorem invalidateNonce_blocks_grant (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (maker : Addr) (n : Nat) (g : Grant)
    (h : invalidateNonce s maker n = some s') (hm : g.maker = maker) (hn : g.nonce = n) :
    setExecutorWithSig signed s' g = none := by
  unfold invalidateNonce at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    unfold setExecutorWithSig
    simp only [hm, hn, burn, and_self, if_true, Bool.true_eq_false, false_and, and_false,
      if_false]
  · exact absurd h (by simp)

/-! ### Whole-system revocation

Every state-changing step, by any caller. `setExecutorWithSig` and `invalidateNonce` carry their
reverts; orders, fills, cancels and price updates never write `isExecutor` or `nonceUsed`
(src/libraries/AsyncFiller.sol:71-155, src/AsyncSwap.sol:281-326), so they are `other`. -/

inductive Step where
  | setExecutor (caller : Addr) (p : Pool) (e : Addr) (allow : Bool)
  | setExecutorWithSig (g : Grant)
  | invalidateNonce (caller : Addr) (n : Nat)
  | other
  | tick (dt : Nat)

def step (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)] (s : St) : Step → Option St
  | .setExecutor c p e a => some (setExecutor s c p e a)
  | .setExecutorWithSig g => setExecutorWithSig signed s g
  | .invalidateNonce c n => invalidateNonce s c n
  | .other => some s
  | .tick dt => some { s with now := s.now + dt }

def run (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)] : St → List Step → Option St
  | s, [] => some s
  | s, a :: as => (step signed s a).bind (fun s' => run signed s' as)

/-- A step re-enables a revoked entry `(p, m, e)` only if `m` itself called `setExecutor`, or a
grant signed by `m` for exactly `(p, e, allow = true)` with a fresh nonce was submitted. -/
theorem step_reenable_needs_maker (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (s s' : St) (a : Step) (p : Pool) (m e : Addr)
    (hOff : s.isExec p m e = false) (h : step signed s a = some s') (hOn : s'.isExec p m e = true) :
    a = .setExecutor m p e true ∨
      ∃ g, a = .setExecutorWithSig g ∧ g.maker = m ∧ g.pool = p ∧ g.executor = e ∧
        g.allow = true ∧ signed m g ∧ s.nonceUsed m g.nonce = false ∧ s.now ≤ g.deadline := by
  cases a with
  | setExecutor c p' e' al =>
    simp only [step, Option.some.injEq] at h
    subst h
    by_cases hk : p = p' ∧ m = c ∧ e = e'
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      have hal : al = true := by
        have := hOn
        simp only [setExecutor, setAuth_self] at this
        exact this
      subst hal
      exact Or.inl rfl
    · rw [setExecutor_scoped_to_owner_pool s c e' p' al p m e hk, hOff] at hOn
      exact absurd hOn (by simp)
  | setExecutorWithSig g =>
    obtain ⟨hs, hd, hn, hset, hrest, -, -⟩ := setExecutorWithSig_scoped signed s s' g h
    by_cases hk : p = g.pool ∧ m = g.maker ∧ e = g.executor
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      rw [hset] at hOn
      exact Or.inr ⟨g, rfl, rfl, rfl, rfl, hOn, hs, hn, hd⟩
    · rw [hrest p m e hk, hOff] at hOn
      exact absurd hOn (by simp)
  | invalidateNonce c n =>
    simp only [step, invalidateNonce] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rw [hOff] at hOn
      exact absurd hOn (by simp)
    · exact absurd h (by simp)
  | other =>
    simp only [step, Option.some.injEq] at h
    subst h
    rw [hOff] at hOn
    exact absurd hOn (by simp)
  | tick dt =>
    simp only [step, Option.some.injEq] at h
    subst h
    rw [hOff] at hOn
    exact absurd hOn (by simp)

/-- Revocation sticks: once `(p, m, e)` is revoked, along any sequence of successful transactions
in which `m` never calls `setExecutor(p, e, true)` and no signed `SetExecutor` grant from `m` for
`(p, e, true)` is submitted, `e` still cannot fill or cancel `m`'s orders on `p`. -/
theorem revocation_sticks (signed : Addr → Grant → Prop) [∀ m g, Decidable (signed m g)]
    (as : List Step) (s s' : St) (p : Pool) (m e : Addr)
    (hOff : s.isExec p m e = false) (h : run signed s as = some s')
    (hNoDirect : Step.setExecutor m p e true ∉ as)
    (hNoSig : ∀ g, Step.setExecutorWithSig g ∈ as →
      ¬ (g.maker = m ∧ g.pool = p ∧ g.executor = e ∧ g.allow = true)) :
    s'.isExec p m e = false := by
  induction as generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact hOff
  | cons a as ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    have hOff1 : s1.isExec p m e = false := by
      cases hv : s1.isExec p m e
      · rfl
      · rcases step_reenable_needs_maker signed s s1 a p m e hOff h1 hv with hd | ⟨g, rfl, hg⟩
        · subst hd
          exact absurd (List.mem_cons_self ..) hNoDirect
        · exact absurd ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩ (hNoSig g (List.mem_cons_self ..))
    exact ih s1 hOff1 h2 (fun hm => hNoDirect (List.mem_cons_of_mem _ hm))
      (fun g hg => hNoSig g (List.mem_cons_of_mem _ hg))

end ProtocolProofs.Audit.Executor
