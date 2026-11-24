# trashlean

**Mathematically rigorous. Intellectually questionable.**

Unnecessarily sophisticated Lean 4 proofs of absolutely unnecessary theorems.

## TRASH-0001 — The Fundamental Theorem of Academic Degeneration

*An Algebraic, Categorical and Topological Obstruction to the Equivalence of CCFA and CCBB.*

[Read the formalization](Trashlean/Academic/Degeneration.lean).

CCBB (操操逼逼) is a lexical parody derived from CCFB. We formalize this
relation through a squaring operation on polynomial representations.
Revisions add an arbitrary multiple of the indeterminate X. Both operations
preserve evaluation at zero on the syntactic artifact space.

| Mathematical field | Machinery | Obstruction |
|---|---|---|
| Mathematical logic | Inductive syntax, derivation histories | Conservation across arbitrarily many edits |
| Category theory | Preorder categories, functor, isomorphisms | No categorical equivalence between CCFA and CCBB |
| Commutative algebra | Ring character, maximal ideal, quotient ring | Residues distinguish A from B-derived objects |
| Linear algebra | Linear functional, kernel, span | No finite real linear combination of B-derived profiles equals the A-profile |
| Topology | Product topology, closed hyperplane, closure | Even pointwise approximation cannot overcome the obstruction |

The model is satirical: its credit counts an invented A-origin token rather
than real research quality. Nothing here implies actual incompatibility
between academic work and personal life.

## Build

Install elan, then:

```sh
lake update
lake exe cache get
lake build
```

The toolchain and Mathlib release are pinned to v4.19.0.
Kernel verification is pending until the first successful build.

## Submission guidelines

Use interesting mathematical machinery, make assumptions explicit, and
avoid unfinished proofs or bespoke axioms that directly assert the conclusion.
Import new modules from Trashlean.lean and run the Lean build.

**Proof of uselessness is left as an exercise to the reader.**
