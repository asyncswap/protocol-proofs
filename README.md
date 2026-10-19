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
   | `report` | the audit report's file; blank means the one in `audit/` |

3. **No secrets.** Install the [formalmind GitHub App](https://github.com/apps/formalmind) on the
   owner and set the project up at formal.team. Each run proves who it is with GitHub's OIDC
   token and gets a one-hour App token and a model session from formal.team; model calls go
   through formal.team's proxy, which charges your Formal Mind credits and stops at your
   daily budget.
4. **Self-hosting instead?** Add your own `ANTHROPIC_API_KEY` (and `PROTOCOL_READ_TOKEN` for a
   private protocol) as Actions secrets; the runs then call Anthropic directly.
5. **For an audit**, copy `.formal/templates/FM_AUDIT.md` to `audit/FM_AUDIT_<MM>_<YYYY>.md`
   (formal.team does this for you), and write what you already know in `.formal/plan.md`.
6. **Start it:** Actions → **formalmind swarm** → **Run workflow**. After that it runs every
   ten minutes on its own, and hands the turn on straight away when there is more to do.

On its first run the swarm opens three issues it keeps pinned: **formalmind ledger** (the
cost of every run), **Swarm notebook** (what each run did) and **Chief updates** (a daily
summary for you). The roles and their rules are in `.github/formalmind/`.

## What you get

- **specs:** Lean 4 definitions and theorems about your contracts, one reviewed PR at a time,
  each merged only on a clean `lake build` with no `sorry`. `FORMAL_MIND.md` is the changelog.
- **audit:** every invariant either proved in Lean, filed as a finding with a POC in the `poc/` Foundry project and a fix patch, or marked out of scope; all of it collected in the report,
  ready to submit.

## Building locally

```
lake exe cache get
lake build
```
