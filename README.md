# Formal Mind proofs template

A Lean 4 project with the [Formal Mind](https://formal.team) swarm built in. Make a copy for
your protocol, fill in one config file, and a team of agents writes the formal spec and
proofs of your Solidity contracts, or audits them and writes one report, in issues and pull
requests on this repository.

The easy way is [formal.team](https://formal.team): paste your repository and it creates this
repository for you. To set it up yourself instead:

## Set up

1. **Copy the template.** On GitHub, click **Use this template**, and name the copy
   `<your-protocol>-proofs`, under the same owner as the protocol.
2. **Fill in `.formal/swarm.json`:**

   | Field | What it is |
   | --- | --- |
   | `protocol` | the Solidity repository, `owner/name` |
   | `commit` | for an audit, the commit to audit; blank means the default branch |
   | `mode` | `audit` (one commit, every agent at once, one report) or `specs` (formal specs that keep up with your code) |
   | `maintainer` | your GitHub handle; the swarm tags you only when a decision is yours |
   | `team` | how many agents may work at once in audit mode |
   | `dailyUsd`, `monthlyUsd` | the budget; the swarm pauses when it is spent |
   | `report` | the audit report's file; blank means `FM_AUDIT_<MM>_<YYYY>.md` |

3. **Add the secrets** under Settings → Secrets and variables → Actions:
   - `ANTHROPIC_API_KEY` (required): the model the agents run on.
   - `PROTOCOL_READ_TOKEN` (only for a private protocol repository): a fine-grained token
     with read access to its contents.
4. **Allow Actions to open pull requests:** Settings → Actions → General → Workflow
   permissions → "Read and write permissions" and "Allow GitHub Actions to create and approve
   pull requests".
5. **For an audit**, add the report file at the root, for example `FM_AUDIT_10_2026.md`
   (formal.team does this for you), and write what you already know in `.formal/plan.md`.
6. **Start it:** Actions → **formalmind swarm** → **Run workflow**. After that it runs every
   ten minutes on its own, and hands the turn on straight away when there is more to do.

On its first run the swarm opens three issues it keeps pinned: **formalmind ledger** (the
cost of every run), **Swarm notebook** (what each run did) and **Chief updates** (a daily
summary for you). The roles and their rules are in `.github/formalmind/`.

## What you get

- **specs:** Lean 4 definitions and theorems about your contracts, one reviewed PR at a time,
  each merged only on a clean `lake build` with no `sorry`. `FORMAL_MIND.md` is the changelog.
- **audit:** every invariant either proved in Lean, filed as a finding with a Foundry POC
  under `poc/` and a fix patch, or marked out of scope; all of it collected in the report,
  ready to submit.

## Building locally

```
lake exe cache get
lake build
```
