/-
# Audit: two-step ownership handover (swarm issue #16)

Model of the `owner` / `pendingOwner` slots of `protocol/src/AsyncSwap.sol` at e230f5b.

* `owner` (AsyncSwap.sol:40) and `pendingOwner` (AsyncSwap.sol:43) are written only in the
  constructor (AsyncSwap.sol:125-127), `transferOwnership` (AsyncSwap.sol:135-139) and
  `acceptOwnership` (AsyncSwap.sol:142-147). No other function, no `sstore` and no
  `delegatecall` in `protocol/src` touches them, so every other entry point is the identity
  on this state (`Call.other`).
* `onlyOwner` (AsyncSwap.sol:94-97) reverts `NotOwner` unless `msg.sender == owner`.
* `transferOwnership(newOwner)`: `onlyOwner`, then `ZeroAddress` if `newOwner == 0`, then
  `pendingOwner = newOwner`. The owner may overwrite or re-nominate at will.
* `acceptOwnership()`: `NotOwner` unless `msg.sender == pendingOwner`, then
  `owner = msg.sender; pendingOwner = 0`.

Addresses are naturals and `0` is `address(0)`. A reverted call is `none`. The one standing
assumption is the EVM's: `msg.sender` is never `address(0)` (no key signs for it).
-/

namespace ProtocolProofs.Audit.Ownership

/-- The two storage slots. -/
structure State where
  owner : Nat
  pending : Nat
  deriving DecidableEq, Repr

/-- The entry points, as seen by the ownership slots. -/
inductive Call where
  | transferOwnership (newOwner : Nat)
  | acceptOwnership
  /-- Any other external function: none of them writes `owner` or `pendingOwner`. -/
  | other
  deriving DecidableEq, Repr

/-- The constructor (AsyncSwap.sol:120-130): reverts `ZeroAddress` on `_owner == 0`;
`pendingOwner` keeps its default `0`. -/
def init (o : Nat) : Option State :=
  if o ≠ 0 then some { owner := o, pending := 0 } else none

/-- `transferOwnership` (AsyncSwap.sol:135-139) behind `onlyOwner` (AsyncSwap.sol:94-97). -/
def transferOwnership (sender newOwner : Nat) (s : State) : Option State :=
  if sender = s.owner ∧ newOwner ≠ 0 then some { s with pending := newOwner } else none

/-- `acceptOwnership` (AsyncSwap.sol:142-147). -/
def acceptOwnership (sender : Nat) (s : State) : Option State :=
  if sender = s.pending then some { owner := sender, pending := 0 } else none

/-- One call by `sender`. -/
def step (sender : Nat) : Call → State → Option State
  | .transferOwnership n, s => transferOwnership sender n s
  | .acceptOwnership, s => acceptOwnership sender s
  | .other, s => some s

/-- States reachable from a successful constructor call by calls from nonzero senders. -/
inductive Reachable : State → Prop where
  | init (o : Nat) (s : State) : init o = some s → Reachable s
  | step (s s' : State) (sender : Nat) (c : Call) :
      Reachable s → sender ≠ 0 → step sender c s = some s' → Reachable s'

/-- Only the current owner can nominate, the nominee is never `0`, and nothing else moves. -/
theorem transferOwnership_onlyOwner (sender n : Nat) (s s' : State)
    (h : step sender (.transferOwnership n) s = some s') :
    sender = s.owner ∧ n ≠ 0 ∧ s'.owner = s.owner ∧ s'.pending = n := by
  simp only [step, transferOwnership] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hg.1, hg.2, rfl, rfl⟩
  · simp at h

/-- Only the nominee can accept. -/
theorem acceptOwnership_onlyPending (sender : Nat) (s s' : State)
    (h : step sender .acceptOwnership s = some s') : sender = s.pending := by
  simp only [step, acceptOwnership] at h
  split at h
  · assumption
  · simp at h

/-- Accepting makes the caller owner and clears the pending slot. -/
theorem acceptOwnership_clears_pending (sender : Nat) (s s' : State)
    (h : step sender .acceptOwnership s = some s') : s'.owner = sender ∧ s'.pending = 0 := by
  simp only [step, acceptOwnership] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · simp at h

/-- The owner changes only through `acceptOwnership`, called by the address sitting in the
pending slot, which becomes the owner. -/
theorem owner_reachable_only_via_accept (sender : Nat) (c : Call) (s s' : State)
    (h : step sender c s = some s') (hne : s'.owner ≠ s.owner) :
    c = .acceptOwnership ∧ sender = s.pending ∧ s'.owner = s.pending := by
  cases c with
  | transferOwnership n =>
    exact absurd (transferOwnership_onlyOwner sender n s s' h).2.2.1 hne
  | acceptOwnership =>
    have hp := acceptOwnership_onlyPending sender s s' h
    exact ⟨rfl, hp, (acceptOwnership_clears_pending sender s s' h).1.trans hp⟩
  | other =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact absurd rfl hne

/-- The pending slot is only ever cleared, or set by the current owner through
`transferOwnership` to the nominated address. -/
theorem pending_set_only_by_owner (sender : Nat) (c : Call) (s s' : State)
    (h : step sender c s = some s') (hne : s'.pending ≠ s.pending) :
    s'.pending = 0 ∨ (c = .transferOwnership s'.pending ∧ sender = s.owner) := by
  cases c with
  | transferOwnership n =>
    obtain ⟨ho, -, -, hp⟩ := transferOwnership_onlyOwner sender n s s' h
    exact Or.inr ⟨by rw [hp], ho⟩
  | acceptOwnership => exact Or.inl (acceptOwnership_clears_pending sender s s' h).2
  | other =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact absurd rfl hne

/-- No reachable state has `owner == address(0)`. -/
theorem reachable_owner_ne_zero (s : State) (h : Reachable s) : s.owner ≠ 0 := by
  induction h with
  | init o s hi =>
    simp only [init] at hi
    split at hi
    · simp only [Option.some.injEq] at hi
      subst hi
      assumption
    · simp at hi
  | step s s' sender c _ hsender hstep ih =>
    by_cases hne : s'.owner = s.owner
    · rw [hne]; exact ih
    · obtain ⟨rfl, hp, ho⟩ := owner_reachable_only_via_accept sender c s s' hstep hne
      rw [ho, ← hp]; exact hsender

end ProtocolProofs.Audit.Ownership
