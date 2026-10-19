# Audit mode

Read this when `SWARM_MODE=audit`. It changes what the swarm is for; the rest of the README
(turns, notebook, ledger, `/ask`) still holds.

An audit looks at one frozen commit of the protocol (`AUDIT_COMMIT`, checked out read-only
under `protocol/`) and ends with one report, `REPORT_FILE` (under `audit/`, started from `.formal/templates/FM_AUDIT.md`).
Every agent works at once, each on its own item, so items must stay disjoint.

## Labels in audit mode

| Label | Meaning |
| --- | --- |
| `fm:todo` | an invariant to prove, or a suspicion to check |
| `fm:finding` | the prover found a counterexample; the POC writer takes it |
| `fm:poc` | the POC writer is on it; its branch is `fm/finding-<n>` |
| `fm:review` / `fm:approved` / `fm:changes` | as usual, for proof PRs and finding PRs alike |
| `fm:out-of-scope` | not worth proving for this audit; one line says why |

## Who does what

- **planner** reads `protocol/` at the audit commit and writes the audit's issues at once,
  not two at a time: one `fm:todo` issue per invariant worth proving and one per suspected
  weak spot (access control, rounding, reentrancy, oracle and price math, accounting that
  must sum, upgrade and init paths). Title `audit: <invariant or suspicion>`. Fill the
  queue so every agent has work. When every issue is closed, `fm:finding`-merged or
  `fm:out-of-scope`, write `<!-- fm-plan done -->` on the ledger: the audit is finished.
- **prover** tries to prove the issue's invariant in Lean 4 against the model of the code.
  If it holds, open the proof PR as usual. If it does not, and the failure is a real
  counterexample in the Solidity (not a modelling gap), comment the counterexample in
  plain words (inputs, call sequence, what breaks), relabel the issue `fm:finding`, and
  end the turn with `**Next:** poc`. A modelling gap is fixed in the model, not reported.
- **poc** turns a finding into evidence. See `poc.md`.
- **reviewer** checks a finding PR like a contest judge: is the impact real, is the
  severity right, does the POC fail on the audit commit and pass with the fix.
- **merger** merges, then adds the item to `REPORT_FILE` on `main` in the same turn:
  a row in **Summary** and a section in **Findings** (or a line in **Proved invariants**).
  Never rewrite another item's entry.
- **chief** keeps the report's header honest: `Status: in progress` until the planner wrote
  `fm-plan done` and nothing is open, then `Status: complete`, the date, and counts by
  severity.

## Severity

High: loss or lock of funds, or broken core invariant reachable by anyone. Medium: loss
under specific conditions, or a privileged role can harm users beyond its stated powers.
Low: wrong values or events without loss. Informational: everything else worth fixing.
