# trashlean

**Mathematically rigorous. Intellectually questionable.**

Unnecessarily sophisticated Lean 4 proofs of absolutely unnecessary theorems.

## TRASH-0001 — The Fundamental Theorem of Academic Degeneration

*An Algebraic, Categorical and Topological Obstruction to the Equivalence of CCFA and CCBB.*

[Part I: Categorical and algebraic obstructions](Trashlean/Academic/Degeneration.lean) · [Part II: Infinitesimal academic geometry](Trashlean/Academic/Infinitesimal.lean).

CCBB is a lexical parody derived from CCFB. We formalize this
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
than real research quality. All interpretations beyond the formal model are left to the reader.

### Part II — Infinitesimal academic geometry

Write m for the kernel of evaluation at zero. The second part studies the
actual tower of quotient rings R[X]/m^n rather than only the constant term.

* The residue field is identified using the first isomorphism theorem.
* The m-adic filtration is strict and separated; its finite jet maps jointly
  separate polynomials and admit compatible quotient transition maps.
* A compatible family of geometric-series truncations is proved not to come
  from any polynomial: the formal completion is strictly larger.
* The Zariski closed loci of CCFB and CCBB coincide, but their second jets
  differ. The former gives a nonzero nilpotent; the latter vanishes.
* Iterated degeneration has exact vanishing order 2^n. Every fixed finite
  jet eventually sees zero, whereas CCFA survives every positive-order jet.

The Zariski topology forgets multiplicity. The infinitesimal neighbourhood
does not.

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
