# trashlean contribution policy

- Distinguish lexical transformations from semantic claims.
- Use substantial Mathlib mathematics and explicit modeling assumptions.
- Do not use sorry, admit, or custom axioms to force conclusions.
- Maintain one mathematical exposition in docs/ per theorem, and an index link in README.md.
- Keep README concise: usage, theorem index, and contribution instructions only.
- Register modules in Trashlean.lean, run lake build, and inspect headline theorem axiom dependencies.
- Report unverified builds honestly.

## Branch discipline

- Treat main as the stable release branch. Never commit directly to main or force-push main or dev.
- Fetch current refs before starting. Create feature/<topic>, fix/<topic>, docs/<topic>, or chore/<topic> from dev for ordinary work.
- Use a pull request into dev; do not merge until full CI passes for the current PR head and merge candidate.
- Promote dev to main only through a separate release pull request after review and successful full-project verification. Never skip failing checks or report pending checks as successful.
- For an urgent stable fix, branch hotfix/<topic> from main, open a PR into main, and synchronize the accepted fix back into dev.
- Keep unrelated work separate. Never rewrite shared history; use a revert PR when needed.
- Delete merged topic branches when appropriate, but retain main and dev.
- See CONTRIBUTING.md for the release and verification checklist.
