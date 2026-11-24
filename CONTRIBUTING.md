# Contributing to trashlean

## Branches

| Branch | Base | Purpose | Merge destination |
|---|---|---|---|
| `main` | — | Stable, fully verified releases | — |
| `dev` | `main` initially | Integration and testing | `main` |
| `feature/<topic>` | `dev` | New theorems or substantial expansions | `dev` |
| `fix/<topic>` | `dev` | Proof and build fixes | `dev` |
| `docs/<topic>` | `dev` | Exposition and rendering fixes | `dev` |
| `chore/<topic>` | `dev` | Tooling, dependency and workflow maintenance | `dev` |
| `hotfix/<topic>` | `main` | Urgent stable fixes | `main`, then synchronize into `dev` |

## Development

```sh
git fetch origin
git switch dev
git pull --ff-only origin dev
git switch -c feature/trash-0002
# Edit proofs, documentation and theorem index.
lake build
git add .
git commit -m "feat: formalize TRASH-0002"
git push -u origin feature/trash-0002
gh pr create --base dev --head feature/trash-0002
```

If dev is not yet present locally, use `git switch --track origin/dev` once.
Use a topic branch appropriate to the type of change. Do not push directly
to main. Prefer separate PRs for unrelated changes.

## Verification and promotion

- Build the complete root library, not just individual theorem modules.
- Inspect `#print axioms` for headline theorems; no sorryAx or bespoke assumptions inserted to force the result.
- Check that documentation matches the proved statements and that math renders in GitHub's preview.
- Require the complete CI workflow to succeed on the current PR revision and merge candidate before merging.
- Integrate topic changes into dev, then open a separate dev-to-main release PR.
- Promote only after the dev release candidate and release PR pass CI and review.
- Keep main and dev long-lived; remove completed topic branches. Do not force-push shared branches. Revert via a PR if necessary.

For repository administrators: configure GitHub branch protection or rulesets
on main (and preferably dev), require pull requests and the `verify` check
from the Peer review by kernel workflow, and disallow force pushes and
deletion. This policy is not a substitute for server-side enforcement.

## Mathematical standards

Each theorem must have Lean source, a human-readable exposition in docs/,
a theorem index link, and an import in Trashlean.lean. Distinguish fictional
model assumptions from mathematical consequences. Avoid unfinished proofs.

## Repository management and sample branches

The stable mathematical source, theorem exposition, README, and build configuration
on dev must start from the current main revision. Do not regenerate an existing
proof document from an older snapshot. Before committing, inspect the diff against
both the current target branch and main; verify that unchanged files have identical
Git blob IDs. Repository management documentation may be maintained separately on dev.

The following sample refs illustrate the branch naming scheme. They contain no
experimental theorem or intentional build failure:

| Sample ref | Starting branch | PR target |
|---|---|---|
| feature/sample | dev | dev |
| fix/sample | dev | dev |
| docs/sample | dev | dev |
| chore/sample | dev | dev |
| hotfix/sample | main | main |

Samples are reference branches, not active work. Create new topic branches from
the latest appropriate base, rather than stacking work onto sample refs.
Keep examples aligned with their intended base when explicitly refreshing them.

## Release and documentation checks

- Keep main as the default public stable branch; never commit or force-push directly to it.
- Keep dev as the integration branch. Avoid rewriting its history; restore files by a new commit.
- Verify the current base SHA immediately before writing a commit and use a conditional ref update.
- Inspect the full candidate tree and PR diff, not just the files intentionally edited.
- For Markdown, preserve the proven rendering conventions in the stable version.
  Use balanced dollar delimiters, braced subscripts, and standard macros; avoid
  operatorname and custom macro definitions in the GitHub preview.
- Confirm CI for the exact release candidate and its PR merge result, then review the
  rendered theorem pages. A successful Lean build alone does not certify Markdown rendering.
- Do not publish new release tags until stable CI succeeds. Do not remove existing
  releases or tags. Keep main and dev long-lived.
- Branch protection and required checks must be enforced through GitHub repository
  settings by an authorized administrator; this document does not activate them.
