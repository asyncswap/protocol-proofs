/-
# Audit: two-step ownership transfer (swarm issue #20)

Model of the owner state of `protocol/src/AsyncSwap.sol` at e230f5b: the two storage slots
`owner` and `pendingOwner` (AsyncSwap.sol:40,43). They are written in exactly four places
(AsyncSwap.sol:127,137,145,146), all modelled here:

* the constructor (AsyncSwap.sol:120-130) reverts with `ZeroAddress` if `_owner == 0`, then
  sets `owner = _owner`; `pendingOwner` starts at its default `address(0)`;
* `transferOwnership(newOwner)` (AsyncSwap.sol:135-139) is `onlyOwner` (AsyncSwap.sol:94-97),
  reverts with `ZeroAddress` if `newOwner == 0`, then sets `pendingOwner = newOwner`;
* `acceptOwnership()` (AsyncSwap.sol:142-147) reverts with `NotOwner` unless
  `msg.sender == pendingOwner`, then sets `owner = msg.sender` and `pendingOwner = 0`.

There is no `renounceOwnership` and no other writer. Every other entry point leaves both
slots alone, which `step` folds into one `other` case. A reverted call is `none`. Addresses
are naturals, `0` is `address(0)`; `msg.sender` is never `address(0)`, which is the
hypothesis `caller ≠ 0` where it is used.
-/

namespace ProtocolProofs.Audit.Ownership

/-- The two owner slots of `AsyncSwap` (AsyncSwap.sol:40,43). -/
structure State where
  owner : Nat
  pendingOwner : Nat
  deriving DecidableEq, Repr

/-- The constructor (AsyncSwap.sol:120-130), restricted to the owner slots. -/
def init (o : Nat) : Option State :=
  if o ≠ 0 then some { owner := o, pendingOwner := 0 } else none

/-- `transferOwnership` (AsyncSwap.sol:135-139) behind `onlyOwner` (AsyncSwap.sol:94-97). -/
def transferOwnership (caller newOwner : Nat) (s : State) : Option State :=
  if caller = s.owner ∧ newOwner ≠ 0 then some { s with pendingOwner := newOwner } else none

/-- `acceptOwnership` (AsyncSwap.sol:142-147). -/
def acceptOwnership (caller : Nat) (s : State) : Option State :=
  if caller = s.pendingOwner then some { owner := caller, pendingOwner := 0 } else none

/-- One call by `caller`. `other` is any entry point that does not write the owner slots. -/
inductive Call where
  | transfer (newOwner : Nat)
  | accept
  | other

def step (caller : Nat) : Call → State → Option State
  | .transfer n, s => transferOwnership caller n s
  | .accept, s => acceptOwnership caller s
  | .other, s => some s

/-- Only the current owner can nominate. -/
theorem transferOwnership_onlyOwner (caller n : Nat) (s s' : State)
    (h : transferOwnership caller n s = some s') : caller = s.owner := by
  simp only [transferOwnership] at h
  split at h
  · rename_i hg
    exact hg.1
  · simp at h

/-- A nomination is never `address(0)`, and it changes nothing but `pendingOwner`. -/
theorem transferOwnership_nonzero (caller n : Nat) (s s' : State)
    (h : transferOwnership caller n s = some s') :
    s'.pendingOwner = n ∧ n ≠ 0 ∧ s'.owner = s.owner := by
  simp only [transferOwnership] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, hg.2, rfl⟩
  · simp at h

/-- Only the nominee can take ownership, and it becomes the owner. -/
theorem acceptOwnership_onlyPending (caller : Nat) (s s' : State)
    (h : acceptOwnership caller s = some s') : caller = s.pendingOwner ∧ s'.owner = caller := by
  simp only [acceptOwnership] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hg, rfl⟩
  · simp at h

/-- Acceptance clears the nomination, so it cannot be replayed. -/
theorem acceptOwnership_clears (caller : Nat) (s s' : State)
    (h : acceptOwnership caller s = some s') : s'.pendingOwner = 0 := by
  simp only [acceptOwnership] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · simp at h

/-- With no nomination open, nobody can accept: `msg.sender` is never `address(0)`. -/
theorem acceptOwnership_none_pending (caller : Nat) (hc : caller ≠ 0) (s : State)
    (hp : s.pendingOwner = 0) : acceptOwnership caller s = none := by
  simp only [acceptOwnership, hp, hc, if_false]

/-- The constructor never installs `address(0)` and opens no nomination. -/
theorem init_owner (o : Nat) (s : State) (h : init o = some s) :
    s.owner ≠ 0 ∧ s.pendingOwner = 0 := by
  simp only [init] at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hg, rfl⟩
  · simp at h

/-- Run a history of `(caller, call)` pairs; any revert reverts the run. -/
def run : List (Nat × Call) → State → Option State
  | [], s => some s
  | (c, k) :: rest, s => (step c k s).bind (run rest)

/-- The owner is never `address(0)` after any call by a nonzero sender. -/
theorem step_owner_nonzero (c : Nat) (hc : c ≠ 0) (k : Call) (s s' : State)
    (hs : s.owner ≠ 0) (h : step c k s = some s') : s'.owner ≠ 0 := by
  cases k with
  | transfer n => rw [(transferOwnership_nonzero c n s s' h).2.2]; exact hs
  | accept => rw [(acceptOwnership_onlyPending c s s' h).2]; exact hc
  | other =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact hs

/-- From deployment on, through any history of calls by nonzero senders, the owner is never
`address(0)`: the protocol can never lose its owner. -/
theorem run_owner_nonzero (o : Nat) (s0 : State) (h0 : init o = some s0)
    (hist : List (Nat × Call)) (hc : ∀ p ∈ hist, p.1 ≠ 0) (s : State)
    (h : run hist s0 = some s) : s.owner ≠ 0 := by
  have key : ∀ (hist : List (Nat × Call)) (t : State), (∀ p ∈ hist, p.1 ≠ 0) →
      t.owner ≠ 0 → run hist t = some s → s.owner ≠ 0 := by
    intro hist
    induction hist with
    | nil =>
      intro t _ ht h
      simp only [run, Option.some.injEq] at h
      subst h
      exact ht
    | cons p rest ih =>
      intro t hc ht h
      obtain ⟨c, k⟩ := p
      simp only [run] at h
      cases hstep : step c k t with
      | none => simp [hstep] at h
      | some t' =>
        simp only [hstep, Option.some_bind] at h
        exact ih t' (fun q hq => hc q (List.mem_cons_of_mem _ hq))
          (step_owner_nonzero c (hc (c, k) List.mem_cons_self) k t t' ht hstep) h
  exact key hist s0 hc (init_owner o s0 h0).1 h

end ProtocolProofs.Audit.Ownership
