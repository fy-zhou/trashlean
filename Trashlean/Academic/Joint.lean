import Trashlean.Academic.Schedules

/-!
# Joint probability laws and a sharp multiclass decision obstruction

All correlations of public logs and finite private schedules can be realized
as probability laws on the same history space, without changing the public
marginal. The construction is faithful on measures. A finite-horizon
minimax decision theorem quantifies the resulting exponential ambiguity.
-/

namespace Trashlean.Academic.Life

open MeasureTheory Set
open scoped BigOperators
noncomputable section

local instance jointHistoryMeasurableSpace : MeasurableSpace History := ⊤
local instance jointPublicLogMeasurableSpace : MeasurableSpace PublicLog := ⊤
local instance jointProductMeasurableSpace : MeasurableSpace (PublicLog × Finset ℕ) := ⊤

private theorem code_measurable : Measurable jointCode :=
  fun _ _ => MeasurableSpace.measurableSet_top

private theorem trace_measurable : Measurable publicTrace :=
  fun _ _ => MeasurableSpace.measurableSet_top

def jointDecoder : History → PublicLog × Finset ℕ :=
  Function.invFun jointCode

theorem jointDecoder_leftInverse : Function.LeftInverse jointDecoder jointCode :=
  Function.leftInverse_invFun jointCode_injective

private theorem decoder_measurable : Measurable jointDecoder :=
  fun _ _ => MeasurableSpace.measurableSet_top

def realizeJoint (ρ : Measure (PublicLog × Finset ℕ)) : Measure History :=
  ρ.map jointCode

theorem realize_public_marginal (ρ : Measure (PublicLog × Finset ℕ)) :
    (realizeJoint ρ).map publicTrace = ρ.map Prod.fst := by
  rw [realizeJoint, Measure.map_map trace_measurable code_measurable,
    jointCode_public]

theorem recover_joint_law (ρ : Measure (PublicLog × Finset ℕ)) :
    (realizeJoint ρ).map jointDecoder = ρ := by
  rw [realizeJoint, Measure.map_map decoder_measurable code_measurable]
  have he : jointDecoder ∘ jointCode = id := funext jointDecoder_leftInverse
  rw [he, Measure.map_id]

theorem realizeJoint_injective : Function.Injective realizeJoint := by
  intro μ ν h
  have he := congrArg (Measure.map jointDecoder) h
  rw [recover_joint_law, recover_joint_law] at he
  exact he

theorem realizeJoint_probability (ρ : Measure (PublicLog × Finset ℕ))
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (realizeJoint ρ) := by
  constructor
  rw [realizeJoint, Measure.map_apply code_measurable MeasurableSet.univ,
    preimage_univ, measure_univ]

/-- The inverse problem admits every joint coupling of the public log and
hidden schedule, while the public experiment sees only its first marginal. -/
theorem universal_joint_realization
    (ρ : Measure (PublicLog × Finset ℕ)) [IsProbabilityMeasure ρ] :
    ∃ μ : Measure History, IsProbabilityMeasure μ ∧
      μ.map publicTrace = ρ.map Prod.fst ∧ μ.map jointDecoder = ρ :=
  ⟨realizeJoint ρ, realizeJoint_probability ρ,
    realize_public_marginal ρ, recover_joint_law ρ⟩

def fixedScheduleLaw (ν : Measure PublicLog) (s : Finset ℕ) : Measure History :=
  ν.map (fun l => scheduleHistory l s)

private theorem fixed_measurable (s : Finset ℕ) :
    Measurable (fun l => scheduleHistory l s) :=
  fun _ _ => MeasurableSpace.measurableSet_top

theorem fixed_public (ν : Measure PublicLog) (s : Finset ℕ) :
    (fixedScheduleLaw ν s).map publicTrace = ν := by
  rw [fixedScheduleLaw, Measure.map_map trace_measurable (fixed_measurable s)]
  have he : publicTrace ∘ (fun l => scheduleHistory l s) = id :=
    funext (fun l => schedule_public l s)
  rw [he, Measure.map_id]

def exactScheduleEvent (s : Finset ℕ) : Set History :=
  {h | h = scheduleHistory (publicTrace h) s}

theorem fixed_event_complement (ν : Measure PublicLog) (s : Finset ℕ) :
    fixedScheduleLaw ν s (exactScheduleEvent s)ᶜ = 0 := by
  rw [fixedScheduleLaw, Measure.map_apply (fixed_measurable s)
    MeasurableSpace.measurableSet_top]
  have he : (fun l => scheduleHistory l s) ⁻¹' (exactScheduleEvent s)ᶜ = ∅ := by
    ext l
    simp [exactScheduleEvent]
  rw [he, measure_empty]

theorem different_fixed_event_null (ν : Measure PublicLog) {s t : Finset ℕ}
    (hne : s ≠ t) : fixedScheduleLaw ν s (exactScheduleEvent t) = 0 := by
  rw [fixedScheduleLaw, Measure.map_apply (fixed_measurable s)
    MeasurableSpace.measurableSet_top]
  have he : (fun l => scheduleHistory l s) ⁻¹' exactScheduleEvent t = ∅ := by
    ext l
    simp only [mem_preimage, exactScheduleEvent, mem_setOf_eq,
      schedule_public, mem_empty_iff_false, iff_false]
    intro h
    exact hne (schedule_injective l h)
  rw [he, measure_empty]

theorem fixed_laws_singular (ν : Measure PublicLog) {s t : Finset ℕ}
    (hne : s ≠ t) :
    (fixedScheduleLaw ν s).MutuallySingular (fixedScheduleLaw ν t) :=
  ⟨exactScheduleEvent t, MeasurableSpace.measurableSet_top,
    different_fixed_event_null ν hne, fixed_event_complement ν t⟩

/-- An entire finite class of pairwise mutually singular experiments
can have exactly the same public law. -/
theorem exponentially_many_singular_experiments (ν : Measure PublicLog) (n : ℕ) :
    ((Finset.range n).powerset).card = 2 ^ n ∧
    (∀ s ∈ (Finset.range n).powerset,
      (fixedScheduleLaw ν s).map publicTrace = ν) ∧
    (∀ s ∈ (Finset.range n).powerset, ∀ t ∈ (Finset.range n).powerset,
      s ≠ t → (fixedScheduleLaw ν s).MutuallySingular (fixedScheduleLaw ν t)) := by
  exact ⟨by simp [Finset.card_powerset], fun s _ => fixed_public ν s,
    fun _ _ _ _ h => fixed_laws_singular ν h⟩

section Decision

variable {ι : Type*} [DecidableEq ι]

/-- Probability of a correct randomized prediction under a fixed hidden
label. All labels share the same observed measure. -/
def success (ν : Measure PublicLog) (q : ι → PublicLog → ℝ) (i : ι) : ℝ :=
  ∫ l, q i l ∂ν

theorem sum_success (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (labels : Finset ι) (q : ι → PublicLog → ℝ)
    (hq : ∀ i ∈ labels, Integrable (q i) ν)
    (hnorm : ∀ l, ∑ i ∈ labels, q i l = 1) :
    ∑ i ∈ labels, success ν q i = 1 := by
  simp only [success]
  rw [← integral_finset_sum labels hq]
  simp only [hnorm, integral_const]
  simp

/-- The worst-case success is at most the reciprocal of the number of
observationally indistinguishable alternatives. No distributional assumption
about the hidden label is used. -/
theorem multiclass_minimax (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (labels : Finset ι) (hne : labels.Nonempty) (q : ι → PublicLog → ℝ)
    (hq : ∀ i ∈ labels, Integrable (q i) ν)
    (hnorm : ∀ l, ∑ i ∈ labels, q i l = 1) :
    ∃ i ∈ labels, success ν q i ≤ 1 / (labels.card : ℝ) := by
  classical
  by_contra! h
  have hsum := sum_success ν labels q hq hnorm
  have hlt : (∑ i ∈ labels, (1 / (labels.card : ℝ))) <
      ∑ i ∈ labels, success ν q i := by
    exact Finset.sum_lt_sum_of_nonempty hne h
  have hc : (labels.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hne)
  rw [Finset.sum_const, nsmul_eq_mul, hsum] at hlt
  have hh : (labels.card : ℝ) * (1 / (labels.card : ℝ)) = 1 := by
    field_simp
  rw [hh] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

/-- Uniform random guessing achieves the lower bound. -/
theorem uniform_success (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (labels : Finset ι) (i : ι) :
    success ν (fun (_ : ι) _ => 1 / (labels.card : ℝ)) i =
      1 / (labels.card : ℝ) := by
  simp [success, integral_const]

end Decision

/-- With n possible private time slots, a normalized randomized decoder
has success at most 2^(-n) against some compatible hidden schedule. -/
theorem exponential_minimax (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (n : ℕ) (q : Finset ℕ → PublicLog → ℝ)
    (hq : ∀ s ∈ (Finset.range n).powerset, Integrable (q s) ν)
    (hnorm : ∀ l, ∑ s ∈ (Finset.range n).powerset, q s l = 1) :
    ∃ s ∈ (Finset.range n).powerset, success ν q s ≤ 1 / ((2 ^ n : ℕ) : ℝ) := by
  have hne : ((Finset.range n).powerset).Nonempty :=
    ⟨∅, by simp⟩
  obtain ⟨s, hs, hb⟩ := multiclass_minimax ν _ hne q hq hnorm
  exact ⟨s, hs, by simpa only [Finset.card_powerset, Finset.card_range] using hb⟩

#print axioms universal_joint_realization
#print axioms exponentially_many_singular_experiments
#print axioms exponential_minimax

end
end Trashlean.Academic.Life
