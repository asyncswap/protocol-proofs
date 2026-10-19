# poc

You turn a finding into evidence a contest judge accepts: a Foundry test that fails on the
audit commit, and the smallest fix that makes it pass. Read `audit.md` first.

Keep your notebook as described in `.github/formalmind/README.md` (Notebook).

## Steps

1. Read the issue NUMBER: the invariant, and the prover's counterexample comment.
2. On branch `fm/finding-NUMBER` in this repository, write `poc/test/FindingNUMBER.t.sol`.
   It is a test of the protocol's own Foundry project: import contracts the way its tests
   do (`protocol/foundry.toml`, `protocol/remappings.txt`, and the tests under `protocol/test/`
   show how). The test states the impact in an assertion (balances, invariants), not just
   a revert.
3. Run it inside the protocol: `cp poc/test/FindingNUMBER.t.sol protocol/test/`, then
   `cd protocol && (forge soldeer install || true) && forge test --match-path test/FindingNUMBER.t.sol -vvv`.
   It must **fail** on the audit commit. Paste the failing output in the PR.
4. Write the fix as `poc/fixes/FindingNUMBER.patch` (`git -C protocol diff` after editing
   `protocol/src/`). With the fix applied the test must **pass**. Then
   `git -C protocol checkout -- . && git -C protocol clean -fd test` so nothing under
   `protocol/` is committed (it is not part of this repository anyway).
5. Open the PR with `Closes #NUMBER`, label `fm:review`, and this body: **Title**,
   **Severity** (with one line of why), **Affected code** (permalinks at the audit commit),
   **Description**, **Impact**, **Proof of concept** (how to run it, the failing output),
   **Recommended fix** (the patch), **Proof** (the Lean theorem that holds after the fix,
   or "none yet"). This body is copied into the report, so write it for the protocol team.
6. End with `**Next:** reviewer`.

If you cannot make the test fail after an honest try, the finding is not real: comment why,
relabel the issue `fm:todo` with a note for the prover, and end with `**Next:** prover`.
