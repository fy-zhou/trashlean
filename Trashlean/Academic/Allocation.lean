import Mathlib

/-!
# Global allocation of academic and private commitments

A finite schedule is not merely a time budget: tasks have distinct sets
of admissible slots induced by participant availability and release/deadline
constraints. Hall's theorem detects global bottlenecks. The Birkhoff–von
Neumann theorem gives an exact fractional relaxation for balanced assignment.
-/

namespace Trashlean.Academic.Allocation

open Finset Function Matrix
open scoped BigOperators
noncomputable section

inductive ActivityKind
  | research
  | review
  | privateCommitment
  deriving DecidableEq

structure Commitment where
  kind : ActivityKind
  participants : Finset ℕ
  release : ℕ
  deadline : ℕ
  deriving DecidableEq

/-- Discrete global availability: one unit commitment may occupy a slot.
This models a single shared scheduling resource; distinct resources
would require a more general capacity model. -/
structure Environment where
  horizon : ℕ
  available : ℕ → Finset ℕ

def admissible (env : Environment) (c : Commitment) : Finset ℕ :=
  (Finset.range env.horizon).filter fun t =>
    c.release ≤ t ∧ t < c.deadline ∧
      ∀ p ∈ c.participants, t ∈ env.available p

theorem admissible_iff (env : Environment) (c : Commitment) (t : ℕ) :
    t ∈ admissible env c ↔
      t < env.horizon ∧ c.release ≤ t ∧ t < c.deadline ∧
        ∀ p ∈ c.participants, t ∈ env.available p := by
  simp [admissible]

section Hall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complete allocation satisfies every deadline and every participant's
availability, with no collision on the global resource. -/
def Feasible (env : Environment) (tasks : ι → Commitment) : Prop :=
  ∃ f : ι → ℕ, Function.Injective f ∧
    ∀ i, f i ∈ admissible env (tasks i)

def neighbourhood (env : Environment) (tasks : ι → Commitment)
    (S : Finset ι) : Finset ℕ :=
  S.biUnion fun i => admissible env (tasks i)

/-- A necessary and sufficient criterion for simultaneous feasibility,
quantified over every coalition of commitments. -/
theorem hall_feasibility (env : Environment) (tasks : ι → Commitment) :
    Feasible env tasks ↔
      ∀ S : Finset ι, S.card ≤ (neighbourhood env tasks S).card := by
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i => admissible env (tasks i))).symm

/-- Every impossible instance has an explicit overcrowded coalition.
This is an exact obstruction, not a heuristic based on average effort. -/
theorem infeasible_iff_bottleneck (env : Environment) (tasks : ι → Commitment) :
    ¬ Feasible env tasks ↔
      ∃ S : Finset ι, (neighbourhood env tasks S).card < S.card := by
  rw [hall_feasibility]
  push_neg
  rfl

theorem allocation_time_budget (env : Environment) (tasks : ι → Commitment)
    (h : Feasible env tasks) : Fintype.card ι ≤ env.horizon := by
  have hhall := (hall_feasibility env tasks).mp h Finset.univ
  have hsub : neighbourhood env tasks Finset.univ ⊆ Finset.range env.horizon := by
    intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_range.mpr ((admissible_iff _ _ _).mp hi).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ] at hhall
  rw [Finset.card_range] at hcard
  exact hhall.trans hcard

/-- Expanding all admissible sets cannot destroy an allocation. -/
theorem feasibility_monotone (env₀ env₁ : Environment) (tasks : ι → Commitment)
    (h : ∀ i, admissible env₀ (tasks i) ⊆ admissible env₁ (tasks i))
    (hf : Feasible env₀ tasks) : Feasible env₁ tasks := by
  obtain ⟨f, hi, hf⟩ := hf
  exact ⟨f, hi, fun i => h i (hf i)⟩

theorem feasibility_availability_monotone (env₀ env₁ : Environment)
    (tasks : ι → Commitment)
    (hh : env₀.horizon ≤ env₁.horizon)
    (ha : ∀ p, env₀.available p ⊆ env₁.available p)
    (hf : Feasible env₀ tasks) : Feasible env₁ tasks := by
  apply feasibility_monotone env₀ env₁ tasks _ hf
  intro i t ht
  obtain ⟨horizon, release, deadline, available⟩ := (admissible_iff _ _ _).mp ht
  exact (admissible_iff _ _ _).mpr
    ⟨horizon.trans_le hh, release, deadline, fun p hp => ha p (available p hp)⟩

end Hall

/-! A counterexample to the sufficiency of aggregate time accounting. -/

def collisionEnv : Environment :=
  ⟨2, fun _ => {0}⟩

def collisionTasks (i : Fin 2) : Commitment :=
  ⟨if i = 0 then .research else .privateCommitment, {0}, 0, 2⟩

theorem collision_individually_feasible :
    ∀ i : Fin 2, (admissible collisionEnv (collisionTasks i)).Nonempty := by
  intro i
  refine ⟨0, ?_⟩
  simp [admissible, collisionEnv, collisionTasks]

theorem collision_has_aggregate_capacity :
    Fintype.card (Fin 2) ≤ collisionEnv.horizon := by
  simp [collisionEnv]

theorem collision_globally_infeasible :
    ¬ Feasible collisionEnv collisionTasks := by
  rintro ⟨f, hi, hf⟩
  have hzero (i : Fin 2) : f i = 0 := by
    have hh := ((admissible_iff _ _ _).mp (hf i)).2.2.2 0 (by simp [collisionTasks])
    simpa [collisionEnv] using hh
  have h := hi ((hzero 0).trans (hzero 1).symm)
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-! ## The balanced fractional assignment problem -/

section Birkhoff

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear cost of assigning commitments to slots, incorporating any
fixed linear opportunity-cost matrix. -/
def assignmentCost (C : Matrix n n ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := ∑ i, ∑ j, C i j * M i j
  map_add' := by
    intro M N
    simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r M
    change (∑ i, ∑ j, C i j * (r • M) i j) =
      r * (∑ i, ∑ j, C i j * M i j)
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Birkhoff–von Neumann: a balanced fractional schedule is a convex
mixture of deterministic permutation schedules. -/
theorem fractional_decomposition (M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n) :
    ∃ w : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ w σ) ∧
      (∑ σ, w σ = 1) ∧ (∑ σ, w σ • σ.permMatrix ℝ = M) :=
  exists_eq_sum_perm_of_mem_doublyStochastic hM

/-- Every fractional assignment has a deterministic assignment whose
linear cost is no greater. This proves zero integrality gap. -/
theorem deterministic_dominates_fractional (C M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n) :
    ∃ σ : Equiv.Perm n, assignmentCost C (σ.permMatrix ℝ) ≤ assignmentCost C M := by
  classical
  obtain ⟨w, hw, hsum, hdecomp⟩ := fractional_decomposition M hM
  obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Equiv.Perm n))
    (fun σ => assignmentCost C (σ.permMatrix ℝ)) Finset.univ_nonempty
  refine ⟨σ, ?_⟩
  have hc : assignmentCost C M = ∑ τ, w τ * assignmentCost C (τ.permMatrix ℝ) := by
    rw [← hdecomp, map_sum]
    simp
  calc
    assignmentCost C (σ.permMatrix ℝ) =
        ∑ τ, w τ * assignmentCost C (σ.permMatrix ℝ) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ τ, w τ * assignmentCost C (τ.permMatrix ℝ) := by
      exact Finset.sum_le_sum fun τ _ =>
        mul_le_mul_of_nonneg_left (hmin τ (by simp)) (hw τ)
    _ = assignmentCost C M := hc.symm

/-- There exists a deterministic schedule globally optimal over the
entire doubly stochastic polytope, even allowing all fractional plans. -/
theorem integral_global_optimum (C : Matrix n n ℝ) :
    ∃ σ : Equiv.Perm n,
      σ.permMatrix ℝ ∈ doublyStochastic ℝ n ∧
      ∀ M : Matrix n n ℝ, M ∈ doublyStochastic ℝ n →
        assignmentCost C (σ.permMatrix ℝ) ≤ assignmentCost C M := by
  classical
  obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Equiv.Perm n))
    (fun σ => assignmentCost C (σ.permMatrix ℝ)) Finset.univ_nonempty
  refine ⟨σ, permMatrix_mem_doublyStochastic, ?_⟩
  intro M hM
  obtain ⟨τ, ht⟩ := deterministic_dominates_fractional C M hM
  exact (hmin τ (by simp)).trans ht

/-- The extreme points of the feasible polytope are precisely
deterministic allocations. -/
theorem fractional_extreme_points :
    Set.extremePoints ℝ (doublyStochastic ℝ n) =
      {σ.permMatrix ℝ | σ : Equiv.Perm n} :=
  extremePoints_doublyStochastic

/-- An actual forbidden edge cannot receive positive mass in any
positive-weight permutation of a Birkhoff decomposition. -/
theorem decomposition_respects_zeros (M : Matrix n n ℝ)
    (w : Equiv.Perm n → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hM : ∑ σ, w σ • σ.permMatrix ℝ = M)
    (σ : Equiv.Perm n) (hσ : 0 < w σ) (i j : n) (hz : M i j = 0) :
    σ.permMatrix ℝ i j = 0 := by
  have hsum : ∑ τ, w τ * τ.permMatrix ℝ i j = 0 := by
    have hh := congrArg (fun N : Matrix n n ℝ => N i j) hM
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hz] using hh
  have hn (τ : Equiv.Perm n) : 0 ≤ τ.permMatrix ℝ i j :=
    nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic
  have hle := Finset.single_le_sum
    (f := fun τ : Equiv.Perm n => w τ * τ.permMatrix ℝ i j)
    (fun τ _ => mul_nonneg (hw τ) (hn τ)) (Finset.mem_univ σ)
  rw [hsum] at hle
  by_contra h
  have hp := mul_pos hσ ((hn σ).lt_of_ne' h)
  exact (not_lt_of_ge hle) hp

/-- A feasible fractional allocation respecting a forbidden-edge mask
admits a decomposition into feasible deterministic schedules only. -/
theorem feasible_support_decomposition (M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n) (allowed : n → n → Prop)
    (hzero : ∀ i j, ¬ allowed i j → M i j = 0) :
    ∃ w : Equiv.Perm n → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, w σ • σ.permMatrix ℝ = M) ∧
      ∀ σ, 0 < w σ → ∀ i j, ¬ allowed i j → σ.permMatrix ℝ i j = 0 := by
  obtain ⟨w, hw, hs, hd⟩ := fractional_decomposition M hM
  exact ⟨w, hw, hs, hd, fun σ hσ i j hij =>
    decomposition_respects_zeros M w hw hd σ hσ i j (hzero i j hij)⟩

end Birkhoff

#print axioms hall_feasibility
#print axioms infeasible_iff_bottleneck
#print axioms integral_global_optimum
#print axioms feasible_support_decomposition

end
end Trashlean.Academic.Allocation
