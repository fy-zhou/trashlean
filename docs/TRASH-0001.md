# TRASH-0001 — The Fundamental Theorem of Academic Non-Substitution

**A study in causal certification, observational quotients, singular statistical experiments, and the impossibility of semantic substitution.**

## Abstract

A lexical resemblance between two labels is not evidence that their denotations share a mathematical structure. We distinguish a formal rewriting system from a model of academic and private events. The principal theorem is that the predicates CCFA and CCBB on complete histories are unequal, yet their intersection is nonempty. The stronger result is an observational non-identifiability theorem: every probability law on public academic logs admits mutually singular probability extensions with identical public pushforwards and opposite private-event outcomes. The associated binary decision problem has sharp randomized minimax risk $1/2$.

All assumptions are fictional modeling conventions. No empirical claims concerning researchers or conference rules are made.

## 1. Two levels of interpretation

Let $\mathcal W$ be the set of words over a finite alphabet. The lexical rewrite replaces F by B, so the word CCFB is sent to CCBB. This is a morphism of words only. It neither induces a map between actual research and intimate activity nor implies any semantic inclusion.

For the semantic model, let $\mathcal H$ be the set of finite event histories. An event is either a public academic record or a private episode of consensual adult intimate activity. The latter records an interval, participants, and their consent; its validity does not depend on academic achievement.

A public event records a versioned submission, referee report or editorial decision. Write $\pi:\mathcal H\to\mathcal L$ for deletion of private events, and $P:\mathcal H\to\mathcal S$ for deletion of public events.

## 2. Causal certification

For a venue $v$ and manuscript $p$, a certificate is a tuple consisting of a submission $s$, a decision $d$, a finite set $J$ of referee identities, and a family of reports indexed by $J$. Its admissibility requires:

- matching manuscript and version identifiers;
- a submission before every report and every report before the decision;
- sufficient experimental evidence and distinct effort slots before submission;
- a quorum of at least two referees, each distinct from the author and affiliated elsewhere;
- reproducible reports with bounded scores;
- a collective score at least $\lvert J\rvert$ times the decision cutoff and an accepted decision.

Define $A(h)$ and $B(h)$ to hold if the corresponding certificate exists for some manuscript in $\pi(h)$. Define $I(h)$ to hold if $P(h)$ contains a valid private episode, with positive duration, at least two participants and consent of every participant.

The three predicates are the semantic interpretations of CCFA, CCFB and CCBB. The predicates $A$ and $B$ are not assertions about the intrinsic quality of a paper.

**Theorem 1 (semantic independence).** The predicates satisfy $A\ne I$ and $B\ne I$. Neither $B$ implies $I$ nor $I$ implies $B$. All four combinations of $A$ and $I$ are realizable.

**Proof.** Construct an explicit submission at time $4$, three experiments and effort slots $0,1,2$. Two independent reports at times $5$ and $6$ each score $9$; the accepted decision at time $7$ has quorum $2$ and cutoff $8$. This produces a valid $A$ certificate (or $B$ certificate by changing the venue). A private episode at time $10$ has positive duration, two consenting participants, and no academic record. The public-only history satisfies $A$ and not $I$; the private-only history satisfies $I$ and neither $A$ nor $B$. Concatenating the two gives $A$ and $I$, and the empty history gives neither. In particular, $B$ and $I$ have witnesses in both set differences. $\square$

## 3. Observation as a universal quotient

Define $h\sim k$ if and only if $\pi(h)=\pi(k)$. The public restoration map $r$ embeds public logs into histories and satisfies $\pi\circ r=\mathrm{id}_{\mathcal L}$. It follows that the induced map $\mathcal H/{\sim}\to\mathcal L$ is bijective.

**Theorem 2 (universal observation).** For every set $Y$ and every map $F:\mathcal H\to Y$ constant on observation fibers, there exists exactly one $G:\mathcal L\to Y$ with $F=G\circ\pi$.

**Proof.** Set $G=F\circ r$. Since $\pi(r(\pi(h)))=\pi(h)$, fiber invariance gives $G(\pi(h))=F(h)$. Any competing factorization agrees with $G$ after applying it to $r(\ell)$. $\square$

Appending private episodes leaves $\pi$ unchanged, so this result holds for every public observer, not just for one scoring function. It says nothing about how private life might causally affect future public records.

## 4. The sigma-algebra obstruction

Equip $\mathcal H$ and $\mathcal L$ with their discrete sigma-algebras. Write $\mathcal P(X)$ for the power set of $X$. Let

$$
\mathscr F_{\mathrm{pub}}
=\{\pi^{-1}(U):U\in\mathcal P(\mathcal L)\}
$$

be the pullback sigma-algebra on $\mathcal H$, and let $E=\{h\in\mathcal H:I(h)\}$.

**Theorem 3.** The event $E$ is not $\mathscr F_{\mathrm{pub}}$-measurable, and $\mathscr F_{\mathrm{pub}}\subsetneq\mathcal P(\mathcal H)$.

**Proof.** Every public-measurable set is saturated along $\pi$-fibers. The empty history and a private-only history have the same public trace, but only the latter belongs to $E$. Hence $E$ cannot be the inverse image of any subset of $\mathcal L$. $\square$

## 5. Singular lifts of arbitrary public probability laws

Let $\nu$ be any probability measure on $\mathcal L$. Define two sections of $\pi$:

- $r_0(\ell)=r(\ell)$;
- $r_1(\ell)=r(\ell)$ followed by the fixed valid private episode.

Both satisfy $\pi\circ r_i=\mathrm{id}_{\mathcal L}$. Form the pushforward measures $\mu_i=(r_i)_{\ast}\nu$ on $\mathcal H$.

**Theorem 4 (universal statistical non-identifiability).** For every $\nu$, the measures $\mu_0$ and $\mu_1$ are probability measures, are mutually singular, and have identical public pushforwards. Moreover,

$$
\mu_0(E)=0,\qquad
\mu_1(\mathcal H\setminus E)=0.
$$

**Proof.** Measurability follows from discreteness. Pushforward functoriality gives

$$
\pi_{\ast}\mu_i=(\pi\circ r_i)_{\ast}\nu=\nu.
$$

The sections take values respectively in $\mathcal H\setminus E$ and $E$. Thus $r_0^{-1}(E)=\varnothing$ and $r_1^{-1}(\mathcal H\setminus E)=\varnothing$, which proves the claimed null sets and mutual singularity. Probability mass is preserved by pushforward. $\square$

These are two perfectly separable complete-history experiments but indistinguishable public experiments. No amount of additional sampling from the public law can identify which lift generated it.

## 6. A sharp minimax obstruction

Let $q:\mathcal L\to[0,1]$ be an integrable randomized decision rule predicting private activity. Its risks in the two experiments are

$$
R_0(q)=\int_{\mathcal L}q\,d\nu,\qquad
R_1(q)=\int_{\mathcal L}(1-q)\,d\nu.
$$

**Theorem 5.** The minimax risk equals $1/2$.

**Proof.** Linearity of the integral yields $R_0(q)+R_1(q)=1$, since $\nu$ is a probability measure. Consequently,

$$
\max\{R_0(q),R_1(q)\}\geq\frac12.
$$

The constant randomized rule $q=1/2$ attains equality. The Lean result proves the lower bound for every integrable real-valued $q$, hence also for the admissible randomized rules. $\square$

## 7. Radon–Nikodym theory: the entire posterior is unidentifiable

Given a compatible full law $\mu$ with public marginal $\nu$, define the joint subprobability measure

$$
\eta=\pi_{\ast}\bigl(\mu|_E\bigr).
$$

Since $\eta\leq\nu$, the Radon–Nikodym theorem supplies a measurable density

$$
q=\frac{d\eta}{d\nu},\qquad
0\leq q\leq 1.
$$

The inequality holds almost everywhere with respect to $\nu$.

This is the conditional probability of the private event given the public observation.

Conversely, for every measurable $q:\mathcal L\to[0,1]$, define

$$
\mu_q=(r_0)_{\ast}\bigl((1-q)\nu\bigr)
+(r_1)_{\ast}\bigl(q\nu\bigr).
$$

**Theorem 6 (posterior realization).** The public marginal of $\mu_q$ is $\nu$, its total mass is one, and its hidden-event posterior agrees with $q$ almost everywhere with respect to $\nu$.

**Proof.** The two sections preserve the public trace. Additivity of pushforward and of measures with density yields

$$
\pi_{\ast}\mu_q=(1-q)\nu+q\nu=\nu.
$$

Restricting to $E$ annihilates the first term and leaves the second, so its private joint marginal is $q\nu$. The Radon–Nikodym uniqueness theorem identifies its density with $q$ almost everywhere. $\square$

Thus the ambiguity is not merely between two discrete alternatives: the complete measurable function of conditional probabilities is unidentified by the entire observed law.

## 8. Independent algebraic appendix: a geometry of words

The earlier polynomial construction is explicitly a *syntactic* representation. In a free rewrite system, encode the A and B labels by $1+X$ and $X$, and a chosen symbolic B-to-BB rewrite by squaring. This is not an encoding of actual activities. Evaluation at zero is conserved under the specified rewrites; it induces a functor to an ordered category and separates the A label from the BB label.

The kernel of evaluation is the maximal ideal $\mathfrak m=(X)$ in $\mathbb R[X]$; the first isomorphism theorem identifies the residue field with $\mathbb R$. The powers $\mathfrak m^n$ form a strictly decreasing separated filtration. The quotient maps to $\mathbb R[X]/\mathfrak m^n$ jointly separate polynomials, while compatible geometric-series truncations give a family not represented by any polynomial. Thus the compatible jet space strictly contains the polynomial ring.

The Zariski loci $V(X)$ and $V(X^2)$ coincide because their radicals agree, but $X$ is a nonzero nilpotent in $\mathbb R[X]/(X^2)$, whereas $X^2$ vanishes. Iterating the symbolic squaring operation gives $X^{2^n}$, with exact vanishing order $2^n$; every fixed finite jet eventually vanishes.

This appendix is a mathematical study of the chosen word representation, not an argument that intimate activities are B-class publications.

## 9. Formalization index

| Result | Lean declaration |
|---|---|
| Lexical rewrite | [Life.lean](../Trashlean/Academic/Life.lean): `lexical_derivation` |
| Semantic independence and coexistence | Life.lean: `life_model_obstruction` |
| Quotient universal property | Life.lean: `universal_public_observer` |
| Finite resource bound | Life.lean: `certified_budget` |
| Strict sigma-algebra | [Statistics.lean](../Trashlean/Academic/Statistics.lean): `public_sigma_strict` |
| Singular indistinguishable experiments | Statistics.lean: `statistical_nonidentifiability` |
| Radon–Nikodym characterization and arbitrary posterior realization | Statistics.lean: `posterior_characterization`, `arbitrary_posterior_realization` |
| Sharp randomized minimax risk | Statistics.lean: `minimax_lower_bound`, `minimax_attained` |
| Word-rewriting category | [Degeneration.lean](../Trashlean/Academic/Degeneration.lean) |
| Jet separation and strict completion | [Infinitesimal.lean](../Trashlean/Academic/Infinitesimal.lean) |

The formal model is deliberately contrived. The statistical obstruction, quotient property and commutative-algebra claims are mathematical consequences of their stated hypotheses, not empirical or causal results about life.

## 10. Finite-horizon scheduling and exact information capacity

For a public log $\ell$, let $T(\ell)$ be one more than its latest event time (or zero for the empty log). For each index $i\in\{0,\ldots,n-1\}$, define a valid private episode of unit duration starting at $T(\ell)+i$. Any subset $S$ of these indices gives a history $H(\ell,S)$ by appending the corresponding episodes in increasing order.

**Theorem 7.** The construction has no overlap between distinct private intervals, every private event follows the public record, and the map $S\mapsto H(\ell,S)$ is injective. Its public trace is $\ell$. The number of histories is exactly $2^n$, or $\binom nk$ if the private time budget fixes $\lvert S\rvert=k$.

**Proof.** Distinct indices give distinct start times; unit intervals cannot overlap. Recover the indices from the private trace. The counting formulas are the powerset and fixed-cardinality powerset identities. All public certificates are unchanged since the public trace is fixed. $\square$

**Theorem 8 (leakage capacity).** If a supplementary observation has $m$ possible values and permits exact reconstruction of every one of the $2^n$ schedules when the public trace is given, then

$$
m\geq 2^n.
$$

**Proof.** On the fixed public fiber the supplementary observation must be injective: equal messages have equal decoded schedules. Compare cardinalities of the finite image and its codomain. $\square$

## 11. Faithful realization of arbitrary joint laws

The map $J:(\ell,S)\mapsto H(\ell,S)$ is jointly injective, since the public projection recovers $\ell$ and the private trace recovers $S$. Choose a left inverse $D$. For every probability law $\rho$ on the product space, let $\mu=J_{\ast}\rho$. Then

$$
\pi_{\ast}\mu=(\mathrm{pr}_1)_{\ast}\rho,
\qquad D_{\ast}\mu=\rho.
$$

The second identity proves faithfulness of the measure embedding: no distinct joint laws collapse before observation. Every possible correlation between the academic and private schedules is realizable.

For each fixed schedule $S$, push the same public law $\nu$ forward along $\ell\mapsto H(\ell,S)$. All such measures have public marginal $\nu$. For distinct $S$ and $T$ they are mutually singular, witnessed by the measurable set of histories with exactly schedule $T$ in this canonical construction.

## 12. Exponential minimax theorem

Let $\mathcal C$ be the finite set of compatible schedules and let $q_S(\ell)$ be the probability assigned by a randomized decoder to $S$. Normalization says the sum over $\mathcal C$ is one at each public observation. Integrating against the common observed law gives

$$
\sum_{S\in\mathcal C}\mathrm{success}(S)=1.
$$

Hence for some $S$ the success probability is no larger than $1/\lvert\mathcal C\rvert$. The constant uniform rule attains this value. In the $n$-slot model $\lvert\mathcal C\rvert=2^n$, yielding worst-case success at most $2^{-n}$, or error at least $1-2^{-n}$.

## 13. Split exact sequence of observables

Let $U$ be the real vector space of functions on public logs and $V$ the space of functions on full histories. Pullback $P:U\to V$ and restriction $R:V\to U$ along the public section are linear, and $RP=\mathrm{id}_U$.

**Theorem 9 (linear splitting).** There is a linear isomorphism

$$
V\cong U\oplus\ker R,
\qquad f\mapsto(Rf,f-PRf).
$$

The inverse sends $(g,k)$ to $Pg+k$. The identities follow from $RP=\mathrm{id}_U$ and $Rk=0$. Consequently $PR$ is an idempotent projection, and every full observable has a unique public part and a residual part. An observable factors through the public trace if and only if its residual vanishes. The private-event indicator belongs to $\ker R$ and is nonzero, providing a genuine hidden direction.

| Additional result | Lean |
|---|---|
| Feasible schedules and exponential fiber size | [Schedules.lean](../Trashlean/Academic/Schedules.lean) |
| Exact supplementary information bound | Schedules.lean: `leakage_capacity` |
| Faithful joint probability realization | [Joint.lean](../Trashlean/Academic/Joint.lean) |
| Pairwise singular experiments and exponential minimax | Joint.lean: `exponentially_many_singular_experiments`, `exponential_minimax` |
| Split exact linear algebra | [Observables.lean](../Trashlean/Academic/Observables.lean) |

The unit-slot schedules are constructive witnesses, not a claim that real life is discrete or that real correlations vanish. The public-only model allows arbitrary correlations when the full joint law is chosen.

## 14. Constrained resource allocation: Hall's theorem and the assignment polytope

The earlier suffix construction is one explicit family of feasible schedules. A more general model uses commitments with participant sets, release times, deadlines, and types (research, review, or private activity). The environment specifies a finite horizon and availability of each participant. A global single-slot resource prevents simultaneous commitments in this model.

For each commitment $i$, let $A_i$ be the slots within its release/deadline window available to every participant. A schedule is an injective map $f$ with $f(i)\in A_i$.

**Theorem 10 (global feasibility).** A schedule exists if and only if every finite coalition $S$ of commitments satisfies

$$
\lvert S\rvert\leq
\left\lvert\bigcup_{i\in S}A_i\right\rvert.
$$

This is Hall's marriage theorem applied to the scheduling graph. Its negation gives an exact bottleneck certificate. Aggregate time budget is necessary but not sufficient: two individually feasible commitments can both require the same single available slot. Increasing participant availability or extending the horizon cannot destroy a feasible schedule.

In the balanced assignment problem, let $M$ be a doubly stochastic matrix, where $M_{ij}$ represents fractional allocation of commitment $i$ to slot $j$. For an arbitrary real cost matrix $C$ define the linear cost

$$
\mathcal C(M)=\sum_{i,j}C_{ij}M_{ij}.
$$

**Theorem 11 (zero integrality gap).** There is a permutation matrix globally minimizing this cost over all doubly stochastic matrices.

**Proof.** The Birkhoff–von Neumann theorem represents each feasible $M$ as a convex combination of permutation matrices. By linearity, its cost is a weighted average of deterministic costs and cannot be smaller than their minimum. A minimizing permutation exists by finiteness. The extreme points of the polytope are exactly the permutation matrices. $\square$

**Theorem 12 (support-preserving decomposition).** Suppose some edges are forbidden and $M$ has zero on them. In any Birkhoff decomposition with nonnegative weights, every positive-weight permutation must also vanish on every forbidden edge.

**Proof.** At a forbidden edge the sum of nonnegative terms is zero. If a positive-weight permutation assigned positive mass there, the sum would be positive, a contradiction. $\square$

This resource-allocation theory does not identify private activities with academic commitments. They compete for resources only when the environment imposes a shared constraint.

[Lean: Allocation.lean](../Trashlean/Academic/Allocation.lean) — `hall_feasibility`, `infeasible_iff_bottleneck`, `integral_global_optimum`, `fractional_extreme_points`, `feasible_support_decomposition`.
