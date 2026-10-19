/-
Audit #11: the owner's `sweep` and `FeeVault.collect` cannot reach maker escrow
(asyncswap/protocol @ e230f5b).

Solidity being modelled:

* `AsyncSwap.sweep` (src/AsyncSwap.sol:154-159), `onlyOwner`:
    `amount = currency.balanceOfSelf(); currency.transfer(to, amount);`
  It moves the hook's own ERC20 / native balance, nothing else.
* `FeeVault.collect` (src/FeeVault.sol:27-31) checks `msg.sender == hook.owner()` and unlocks;
  `unlockCallback` (src/FeeVault.sol:34-45) burns `poolManager.balanceOf(vault, id)` claims and
  takes the same amount. It moves the vault's own ERC-6909 claims, nothing else.
* Maker escrow lives as the hook's ERC-6909 claims in the PoolManager:
  `_beforeSwap` mints `amountTaken` claims to the hook (src/AsyncSwap.sol:288,
  `take(..., claims = true)`) and records the order (`_createOrder`, src/AsyncSwap.sol:325).
  `AsyncFiller.fill` deletes the order, mints `fee` claims to the vault on the output side
  and burns `amountIn` of the hook's input claims (src/libraries/AsyncFiller.sol:113,123,127).
  `AsyncFiller.cancel` deletes the order and burns `amountIn` claims
  (src/libraries/AsyncFiller.sol:147,151).

Model, per currency id:

* `raw c`         — `currency.balanceOfSelf()` of the hook (what `sweep` reads);
* `hookClaims c`  — `poolManager.balanceOf(hook, c)`;
* `vaultClaims c` — `poolManager.balanceOf(feeVault, c)` (what `collect` reads);
* `escrow c`      — sum of `amountIn` over open orders whose input currency is `c`.

The order book is abstracted to its per-currency sum: create adds the order's `amountIn`,
fill and cancel subtract it, and an existing order's `amountIn` is at most that sum. The
native-output leg of a fill (filler's ETH in through `receive`, out through `settle`,
src/AsyncSwap.sol:413-418, src/libraries/AsyncFiller.sol:119) nets to zero on `raw` within
the transaction; any overpayment left behind is a `donateRaw`. Anyone may send tokens to the
hook (`donateRaw`) or transfer ERC-6909 claims to the hook or the vault (`PoolManager.transfer`).
-/

namespace ProtocolProofs.Audit.OwnerPowers

abbrev Addr := Nat
abbrev Cur := Nat

/-- Point update of a per-currency balance. -/
def upd (f : Cur → Nat) (c : Cur) (v : Nat) : Cur → Nat :=
  fun x => if x = c then v else f x

structure St where
  owner : Addr
  raw : Cur → Nat
  hookClaims : Cur → Nat
  vaultClaims : Cur → Nat
  escrow : Cur → Nat

/-- Every open order is backed by the hook's claims. -/
def Inv (s : St) : Prop := ∀ c, s.escrow c ≤ s.hookClaims c

/-- `_beforeSwap` + `_createOrder`: mint `a` input claims to the hook, open an order of `a`. -/
def create (s : St) (c : Cur) (a : Nat) : Option St :=
  if 0 < a then
    some { s with hookClaims := upd s.hookClaims c (s.hookClaims c + a),
                  escrow := upd s.escrow c (s.escrow c + a) }
  else none

/-- `AsyncFiller.fill`: close an order of `a` in `input`, mint `fee` output claims to the vault,
burn `a` of the hook's input claims (the burn reverts if the hook holds fewer). -/
def fill (s : St) (input output : Cur) (a fee : Nat) : Option St :=
  if 0 < a ∧ a ≤ s.escrow input ∧ a ≤ s.hookClaims input then
    some { s with vaultClaims := upd s.vaultClaims output (s.vaultClaims output + fee),
                  hookClaims := upd s.hookClaims input (s.hookClaims input - a),
                  escrow := upd s.escrow input (s.escrow input - a) }
  else none

/-- `AsyncFiller.cancel`: close an order of `a`, burn `a` input claims, pay the maker. -/
def cancel (s : St) (c : Cur) (a : Nat) : Option St :=
  if 0 < a ∧ a ≤ s.escrow c ∧ a ≤ s.hookClaims c then
    some { s with hookClaims := upd s.hookClaims c (s.hookClaims c - a),
                  escrow := upd s.escrow c (s.escrow c - a) }
  else none

/-- `AsyncSwap.sweep`: the owner takes the hook's whole raw balance of `c`. -/
def sweep (s : St) (caller : Addr) (c : Cur) : Option (St × Nat) :=
  if caller = s.owner then
    some ({ s with raw := upd s.raw c 0 }, s.raw c)
  else none

/-- `FeeVault.collect` + `unlockCallback`: the owner takes all of the vault's claims of `c`. -/
def collect (s : St) (caller : Addr) (c : Cur) : Option (St × Nat) :=
  if caller = s.owner then
    some ({ s with vaultClaims := upd s.vaultClaims c 0 }, s.vaultClaims c)
  else none

inductive Step where
  | create (c : Cur) (a : Nat)
  | fill (input output : Cur) (a fee : Nat)
  | cancel (c : Cur) (a : Nat)
  | donateRaw (c : Cur) (v : Nat)
  | claimsToHook (c : Cur) (v : Nat)
  | claimsToVault (c : Cur) (v : Nat)
  | sweep (c : Cur)
  | collect (c : Cur)

/-- One transaction by `caller`. -/
def step (s : St) (caller : Addr) : Step → Option St
  | .create c a => create s c a
  | .fill i o a fee => fill s i o a fee
  | .cancel c a => cancel s c a
  | .donateRaw c v => some { s with raw := upd s.raw c (s.raw c + v) }
  | .claimsToHook c v => some { s with hookClaims := upd s.hookClaims c (s.hookClaims c + v) }
  | .claimsToVault c v => some { s with vaultClaims := upd s.vaultClaims c (s.vaultClaims c + v) }
  | .sweep c => (sweep s caller c).map Prod.fst
  | .collect c => (collect s caller c).map Prod.fst

/-- `sweep` is owner-only, pays out exactly the hook's raw balance, and leaves the hook's
claims, the vault's claims and every order's escrow untouched. -/
theorem sweep_preserves_escrow (s s' : St) (caller : Addr) (c : Cur) (amt : Nat)
    (hInv : Inv s) (h : sweep s caller c = some (s', amt)) :
    caller = s.owner ∧ amt = s.raw c ∧ s'.escrow = s.escrow ∧
      s'.hookClaims = s.hookClaims ∧ s'.vaultClaims = s.vaultClaims ∧ Inv s' := by
  unfold sweep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by assumption, rfl, rfl, rfl, rfl, hInv⟩
  · exact absurd h (by simp)

/-- `collect` is owner-only, pays out exactly the vault's fee claims, and leaves the hook's
raw balance, the hook's claims and every order's escrow untouched. -/
theorem collect_only_fees (s s' : St) (caller : Addr) (c : Cur) (amt : Nat)
    (hInv : Inv s) (h : collect s caller c = some (s', amt)) :
    caller = s.owner ∧ amt = s.vaultClaims c ∧ s'.escrow = s.escrow ∧
      s'.hookClaims = s.hookClaims ∧ s'.raw = s.raw ∧ Inv s' := by
  unfold collect at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by assumption, rfl, rfl, rfl, rfl, hInv⟩
  · exact absurd h (by simp)

/-- Every transaction, by anyone, keeps every open order backed by the hook's claims. -/
theorem step_inv (s s' : St) (caller : Addr) (st : Step)
    (hInv : Inv s) (h : step s caller st = some s') : Inv s' := by
  cases st with
  | create c a =>
    simp only [step, create] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      intro x
      simp only [upd]
      split
      · subst x; have := hInv c; omega
      · exact hInv x
    · exact absurd h (by simp)
  | fill i o a fee =>
    simp only [step, fill] at h
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h
      subst h
      intro x
      simp only [upd]
      split
      · subst x; have := hInv i; omega
      · exact hInv x
    · exact absurd h (by simp)
  | cancel c a =>
    simp only [step, cancel] at h
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h
      subst h
      intro x
      simp only [upd]
      split
      · subst x; have := hInv c; omega
      · exact hInv x
    · exact absurd h (by simp)
  | donateRaw c v =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact hInv
  | claimsToHook c v =>
    simp only [step, Option.some.injEq] at h
    subst h
    intro x
    simp only [upd]
    split
    · subst x; have := hInv c; omega
    · exact hInv x
  | claimsToVault c v =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact hInv
  | sweep c =>
    simp only [step] at h
    cases hs : sweep s caller c with
    | none => simp [hs] at h
    | some p =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      exact (sweep_preserves_escrow s p.1 caller c p.2 hInv hs).2.2.2.2.2
  | collect c =>
    simp only [step] at h
    cases hs : collect s caller c with
    | none => simp [hs] at h
    | some p =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      exact (collect_only_fees s p.1 caller c p.2 hInv hs).2.2.2.2.2

/-- Run a sequence of `(caller, step)` transactions; `none` if any of them reverts. -/
def run (s : St) : List (Addr × Step) → Option St
  | [] => some s
  | (caller, st) :: rest => (step s caller st).bind (fun s' => run s' rest)

theorem run_inv (s s' : St) (txs : List (Addr × Step)) (hInv : Inv s)
    (h : run s txs = some s') : Inv s' := by
  induction txs generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact hInv
  | cons tx rest ih =>
    obtain ⟨caller, st⟩ := tx
    simp only [run] at h
    cases hs : step s caller st with
    | none => simp [hs] at h
    | some s₁ =>
      simp only [hs, Option.some_bind] at h
      exact ih s₁ (step_inv s s₁ caller st hInv hs) h

/-- The deployed state: no orders, no claims, no balances. -/
def init (owner : Addr) : St :=
  { owner := owner, raw := fun _ => 0, hookClaims := fun _ => 0,
    vaultClaims := fun _ => 0, escrow := fun _ => 0 }

theorem init_inv (owner : Addr) : Inv (init owner) := fun _ => Nat.le_refl 0

/-- After any history, including any number of owner sweeps and collects, every open order can
still be cancelled: the hook's claims always cover it, so the burn in `cancel` cannot revert. -/
theorem cancel_reachable (owner : Addr) (txs : List (Addr × Step)) (s : St) (c : Cur) (a : Nat)
    (h : run (init owner) txs = some s) (ha : 0 < a) (hle : a ≤ s.escrow c) :
    (cancel s c a).isSome := by
  have hInv := run_inv (init owner) s txs (init_inv owner) h
  have := hInv c
  have hg : 0 < a ∧ a ≤ s.escrow c ∧ a ≤ s.hookClaims c := ⟨ha, hle, by omega⟩
  simp only [cancel, if_pos hg, Option.isSome_some]

end ProtocolProofs.Audit.OwnerPowers
