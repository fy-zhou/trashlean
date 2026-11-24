# trashlean

> Mathematically rigorous. Intellectually questionable.

Formal proofs of things nobody needed to prove.

## Usage

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/fy-zhou/trashlean.git
cd trashlean
lake update
lake exe cache get
lake build
```

Lean 4 and Mathlib are pinned to v4.19.0. Open the project in VS Code with the Lean 4 extension to inspect proofs interactively. To check a single module:

```sh
lake env lean Trashlean/Academic/Life.lean
```

## Theorem index

| ID | Theorem | Proof notes | Lean |
|---|---|---|---|
| TRASH-0001 | CCFA ≠ CCBB — The Fundamental Theorem of Academic Non-Substitution | [Mathematical exposition](docs/TRASH-0001.md) | [Life](Trashlean/Academic/Life.lean), [Statistics](Trashlean/Academic/Statistics.lean), [Schedules](Trashlean/Academic/Schedules.lean), [Joint laws](Trashlean/Academic/Joint.lean), [Linear splitting](Trashlean/Academic/Observables.lean), [Allocation](Trashlean/Academic/Allocation.lean), [Lexical algebra](Trashlean/Academic/Degeneration.lean), [Infinitesimal geometry](Trashlean/Academic/Infinitesimal.lean) |

## Contributing

Add a Lean module under `Trashlean/`, import it in `Trashlean.lean`, place a human-readable mathematical exposition in `docs/`, and update the index. Run `lake build` and inspect the axiom dependencies of the headline theorem.

[CI / kernel peer review](https://github.com/fy-zhou/trashlean/actions)

Proof of uselessness is left as an exercise to the reader.
