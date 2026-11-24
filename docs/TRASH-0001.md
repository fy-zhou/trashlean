# TRASH-0001 — The Fundamental Theorem of Academic Non-Substitution

**A study in causal certification, observational quotients, singular statistical experiments, and the impossibility of semantic substitution.**

## Abstract

A lexical resemblance between two labels is not evidence that their denotations share a mathematical structure. We distinguish a formal rewriting system from a model of academic and private events. The principal theorem is that the predicates CCFA and CCBB on complete histories are unequal, yet their intersection is nonempty. The stronger result is an observational non-identifiability theorem: every probability law on public academic logs admits mutually singular probability extensions with identical public pushforwards and opposite private-event outcomes. The associated binary decision problem has sharp randomized minimax risk 1/2.

All assumptions are fictional modeling conventions. No empirical claims concerning researchers or conference rules are made.

## 1. Two levels of interpretation

Let W be the set of words over a finite alphabet. The lexical rewrite replaces F by B, so the word CCFB is sent to CCBB. This is a morphism of words only. It neither induces a map between actual research and intimate activity nor implies any semantic inclusion.

For the semantic model, let H be the set of finite event histories. An event is either a public academic record or a private episode of consensual adult intimate activity. The latter records an interval, participants, and their consent; its validity does not depend on academic achievement.

A public event records a versioned submission, referee report or editorial decision. Write O: H → L for deletion of private events, and P: H → S for deletion of public events.

## 2. Causal certification

For a venue v and manuscript p, a certificate is a tuple consisting of a submission s, a decision d, a finite set J of referee identities, and a family of reports indexed by J. Its admissibility requires:

- matching manuscript and version identifiers;
- a submission before every report and every report before the decision;
- sufficient experimental evidence and distinct effort slots before submission;
- a quorum of at least two referees, each distinct from the author and affiliated elsewhere;
- reproducible reports with bounded scores;
- a collective score at least |J| times the decision cutoff and an accepted decision.

Define A(h) and B(h) to hold if the corresponding certificate exists for some manuscript in O(h). Define I(h) to hold if P(h) contains a valid private episode, with positive duration, at least two participants and consent of every participant.

The three predicates are the semantic interpretations of CCFA, CCFB and CCBB. A and B are not assertions about the intrinsic quality of a paper.

**Theorem 1 (semantic independence).** A ≠ I and B ≠ I. Neither B implies I nor I implies B. All four combinations of A and I are realizable.

**Proof.** Construct an explicit submission at time 4, three experiments and effort slots 0, 1, 2. Two independent reports at times 5 and 6 each score 9; the accepted decision at time 7 has quorum 2 and cutoff 8. This produces a valid A certificate (or B certificate by changing the venue). A private episode at time 10 has positive duration, two consenting participants, and no academic record. The public-only history satisfies A and not I; the private-only history satisfies I and neither A nor B. Concatenating the two gives A and I, and the empty history gives neither. In particular B and I have witnesses in both set differences. ∎

## 3. Observation as a universal quotient

Define h ~ k iff O(h) = O(k). The public restoration map r embeds public logs into histories and satisfies O ∘ r = id. It follows that the induced map H/~ → L is bijective.

**Theorem 2 (universal observation).** For every set Y and every map F: H → Y constant on observation fibers, there exists exactly one G: L → Y with F = G ∘ O.

**Proof.** Set G = F ∘ r. Since O(r(O(h))) = O(h), fiber invariance gives G(O(h)) = F(h). Any competing factorization agrees with G after applying it to r(l). ∎

Appending private episodes leaves O unchanged, so this result holds for every public observer, not just for one scoring function. It says nothing about how private life might causally affect future public records.

## 4. The sigma-algebra obstruction

Equip H and L with their discrete sigma-algebras. Let F_pub = O⁻¹(P(L)) be the pullback sigma-algebra on H, and let E = {h : I(h)}.

**Theorem 3.** E is not F_pub-measurable, and F_pub is strictly smaller than P(H).

**Proof.** Every public-measurable set is saturated along O-fibers. The empty history and a private-only history have the same public trace, but only the latter belongs to E. Hence E cannot be the inverse image of any subset of L. ∎

## 5. Singular lifts of arbitrary public probability laws

Let ν be any probability measure on L. Define two sections of O:

- r₀(l) = r(l);
- r₁(l) = r(l) followed by the fixed valid private episode.

Both satisfy O ∘ rᵢ = id. Form the pushforward measures μᵢ = (rᵢ)₍*₎ν on H.

**Theorem 4 (universal statistical non-identifiability).** For every ν, the measures μ₀ and μ₁ are probability measures, are mutually singular, and have identical public pushforwards. Moreover μ₀(E) = 0 and μ₁(H ∖ E) = 0.

**Proof.** Measurability follows from discreteness. Pushforward functoriality gives O₍*₎μᵢ = (O ∘ rᵢ)₍*₎ν = ν. The sections take values respectively in H ∖ E and E. Thus r₀⁻¹(E) = ∅ and r₁⁻¹(H ∖ E) = ∅, which proves the claimed null sets and mutual singularity. Probability mass is preserved by pushforward. ∎

These are two perfectly separable complete-history experiments but indistinguishable public experiments. No amount of additional sampling from the public law can identify which lift generated it.

## 6. A sharp minimax obstruction

Let q: L → [0,1] be an integrable randomized decision rule predicting private activity. Its risks in the two experiments are

$$
R_0(q)=\int_L q\,d\nu,\qquad R_1(q)=\int_L(1-q)\,d\nu.
$$

**Theorem 5.** The minimax risk equals 1/2.

**Proof.** Linearity of the integral yields R₀(q)+R₁(q)=1, since ν is a probability measure. Consequently max(R₀,R₁) ≥ 1/2. The constant randomized rule q=1/2 attains equality. The Lean result proves the lower bound for every integrable real-valued q, hence also for the admissible randomized rules. ∎

## 7. Radon–Nikodym theory: the entire posterior is unidentifiable

Given a compatible full law μ with public marginal ν, define the joint
subprobability η = O₍*₎(μ restricted to E). Since η ≤ ν, the Radon–Nikodym
theorem supplies a measurable density q = dη/dν, satisfying 0 ≤ q ≤ 1
almost everywhere. This is the conditional probability of the private event
given the public observation.

Conversely, for every measurable q: L → [0,1], define

$
\mu_q=(r_0)_*\big((1-q)\nu\big)+(r_1)_*\big(q\nu\big).
$

**Theorem 6 (posterior realization).** The public marginal of μ_q is ν,
its total mass is one, and its hidden-event posterior agrees with q
ν-almost everywhere.

**Proof.** The two sections preserve the public trace. Additivity of
pushforward and of measures with density yields
O₍*₎μ_q = (1-q)ν + qν = ν. Restricting to E annihilates the first term and
leaves the second, so its private joint marginal is qν. The Radon–Nikodym
uniqueness theorem identifies its density with q almost everywhere. ∎

Thus the ambiguity is not merely between two discrete alternatives:
the complete measurable function of conditional probabilities is
unidentified by the entire observed law.

## 8. Independent algebraic appendix: a geometry of words

The earlier polynomial construction is explicitly a *syntactic* representation. In a free rewrite system, encode the A and B labels by 1+X and X, and a chosen symbolic B-to-BB rewrite by squaring. This is not an encoding of actual activities. Evaluation at zero is conserved under the specified rewrites; it induces a functor to an ordered category and separates the A label from the BB label.

The kernel of evaluation is the maximal ideal m=(X) in R[X]; the first isomorphism theorem identifies the residue field with R. The powers mⁿ form a strictly decreasing separated filtration. The quotient maps to R[X]/mⁿ jointly separate polynomials, while compatible geometric-series truncations give a family not represented by any polynomial. Thus the compatible jet space strictly contains the polynomial ring.

The Zariski loci V(X) and V(X²) coincide because their radicals agree, but X is a nonzero nilpotent in R[X]/(X²), whereas X² vanishes. Iterating the symbolic squaring operation gives X^(2^n), with exact vanishing order 2^n; every fixed finite jet eventually vanishes.

This appendix is a mathematical study of the chosen word representation, not an argument that intimate activities are B-class publications.

## 9. Formalization index

| Result | Lean declaration |
|---|---|
| Lexical rewrite | [Life.lean](../Trashlean/Academic/Life.lean): lexical_derivation |
| Semantic independence and coexistence | Life.lean: life_model_obstruction |
| Quotient universal property | Life.lean: universal_public_observer |
| Finite resource bound | Life.lean: certified_budget |
| Strict sigma-algebra | [Statistics.lean](../Trashlean/Academic/Statistics.lean): public_sigma_strict |
| Singular indistinguishable experiments | Statistics.lean: statistical_nonidentifiability |
| Radon–Nikodym characterization and arbitrary posterior realization | Statistics.lean: posterior_characterization, arbitrary_posterior_realization |
| Sharp randomized minimax risk | Statistics.lean: minimax_lower_bound, minimax_attained |
| Word-rewriting category | [Degeneration.lean](../Trashlean/Academic/Degeneration.lean) |
| Jet separation and strict completion | [Infinitesimal.lean](../Trashlean/Academic/Infinitesimal.lean) |

The formal model is deliberately contrived. The statistical obstruction, quotient property and commutative-algebra claims are mathematical consequences of their stated hypotheses, not empirical or causal results about life.
