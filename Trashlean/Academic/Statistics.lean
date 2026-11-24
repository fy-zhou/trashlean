import Trashlean.Academic.Life

/-!
# TRASH-0001: Statistical impossibility and observational sigma-algebras

For every distribution of public logs, there are two mutually singular
extensions to complete histories, one with and one without a private event.
Their pushforwards under public observation coincide. No public estimator
can distinguish the two; randomized minimax error is exactly one half.
-/

namespace Trashlean.Academic.Life

open MeasureTheory Set
noncomputable section

local instance : MeasurableSpace History := ⊤
local instance : MeasurableSpace PublicLog := ⊤

def publicSigma : MeasurableSpace History :=
  MeasurableSpace.comap publicTrace (⊤ : MeasurableSpace PublicLog)

def privateEventSet : Set History := {h | CCBB h}

theorem private_event_not_public_measurable :
    ¬ MeasurableSet[publicSigma] privateEventSet := by
  intro h
  obtain ⟨s, _, hs⟩ := MeasurableSpace.measurableSet_comap.mp h
  have hp : privateSuffix [exampleEpisode] ∈ privateEventSet := BB_exists
  rw [← hs] at hp
  have h0 : ([] : History) ∈ publicTrace ⁻¹' s := by
    change publicTrace (privateSuffix [exampleEpisode]) ∈ s at hp
    rw [public_private] at hp
    exact hp
  rw [hs] at h0
  exact neither.2 h0

theorem public_sigma_strict :
    publicSigma < (⊤ : MeasurableSpace History) := by
  refine lt_of_le_of_ne le_top ?_
  intro h
  apply private_event_not_public_measurable
  rw [h]
  exact MeasurableSpace.measurableSet_top

def liftAbsent (l : PublicLog) : History := restorePublic l
def liftPresent (l : PublicLog) : History :=
  restorePublic l ++ privateSuffix [exampleEpisode]

@[simp] theorem absent_public (l : PublicLog) :
    publicTrace (liftAbsent l) = l := public_restore l

@[simp] theorem present_public (l : PublicLog) :
    publicTrace (liftPresent l) = l := by
  simp [liftPresent]

theorem absent_not_private (l : PublicLog) : ¬ CCBB (liftAbsent l) :=
  no_private_in_public l

theorem present_is_private (l : PublicLog) : CCBB (liftPresent l) :=
  BB_after_public l

private theorem public_measurable : Measurable publicTrace :=
  fun _ _ => MeasurableSpace.measurableSet_top

private theorem absent_measurable : Measurable liftAbsent :=
  fun _ _ => MeasurableSpace.measurableSet_top

private theorem present_measurable : Measurable liftPresent :=
  fun _ _ => MeasurableSpace.measurableSet_top

def lawAbsent (ν : Measure PublicLog) : Measure History := ν.map liftAbsent
def lawPresent (ν : Measure PublicLog) : Measure History := ν.map liftPresent

theorem absent_pushforward (ν : Measure PublicLog) :
    (lawAbsent ν).map publicTrace = ν := by
  rw [lawAbsent, Measure.map_map public_measurable absent_measurable]
  have he : publicTrace ∘ liftAbsent = id := funext absent_public
  rw [he, Measure.map_id]

theorem present_pushforward (ν : Measure PublicLog) :
    (lawPresent ν).map publicTrace = ν := by
  rw [lawPresent, Measure.map_map public_measurable present_measurable]
  have he : publicTrace ∘ liftPresent = id := funext present_public
  rw [he, Measure.map_id]

theorem absent_null_private (ν : Measure PublicLog) :
    lawAbsent ν privateEventSet = 0 := by
  rw [lawAbsent, Measure.map_apply absent_measurable
    MeasurableSpace.measurableSet_top]
  have he : liftAbsent ⁻¹' privateEventSet = ∅ := by
    ext l
    simp [privateEventSet, absent_not_private]
  rw [he, measure_empty]

theorem present_null_complement (ν : Measure PublicLog) :
    lawPresent ν privateEventSetᶜ = 0 := by
  rw [lawPresent, Measure.map_apply present_measurable
    MeasurableSpace.measurableSet_top]
  have he : liftPresent ⁻¹' privateEventSetᶜ = ∅ := by
    ext l
    simp [privateEventSet, present_is_private]
  rw [he, measure_empty]

theorem hidden_laws_singular (ν : Measure PublicLog) :
    (lawAbsent ν).MutuallySingular (lawPresent ν) :=
  ⟨privateEventSet, MeasurableSpace.measurableSet_top,
    absent_null_private ν, present_null_complement ν⟩

theorem absent_probability (ν : Measure PublicLog) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (lawAbsent ν) := by
  constructor
  rw [lawAbsent, Measure.map_apply absent_measurable MeasurableSet.univ,
    preimage_univ, measure_univ]

theorem present_probability (ν : Measure PublicLog) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (lawPresent ν) := by
  constructor
  rw [lawPresent, Measure.map_apply present_measurable MeasurableSet.univ,
    preimage_univ, measure_univ]

/-- Every public probability law has two singular probability extensions
that induce exactly the same observed law. -/
theorem statistical_nonidentifiability (ν : Measure PublicLog)
    [IsProbabilityMeasure ν] :
    ∃ μ₀ μ₁ : Measure History,
      IsProbabilityMeasure μ₀ ∧ IsProbabilityMeasure μ₁ ∧
      μ₀.MutuallySingular μ₁ ∧
      μ₀.map publicTrace = ν ∧ μ₁.map publicTrace = ν ∧
      μ₀ privateEventSet = 0 ∧ μ₁ privateEventSetᶜ = 0 := by
  exact ⟨lawAbsent ν, lawPresent ν, absent_probability ν,
    present_probability ν, hidden_laws_singular ν,
    absent_pushforward ν, present_pushforward ν,
    absent_null_private ν, present_null_complement ν⟩

/-- A randomized classifier outputs a probability q of the private event.
Under the two observationally identical experiments its error risks are
the integrals of q and 1-q against the same public law. -/
def riskAbsent (ν : Measure PublicLog) (q : PublicLog → ℝ) : ℝ :=
  ∫ l, q l ∂ν

def riskPresent (ν : Measure PublicLog) (q : PublicLog → ℝ) : ℝ :=
  ∫ l, (1 - q l) ∂ν

theorem complementary_risks (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (q : PublicLog → ℝ) (hq : Integrable q ν) :
    riskAbsent ν q + riskPresent ν q = 1 := by
  have hc : Integrable (fun _ : PublicLog => (1 : ℝ)) ν := integrable_const _
  unfold riskAbsent riskPresent
  rw [integral_sub hc hq, integral_const]
  simp

theorem minimax_lower_bound (ν : Measure PublicLog) [IsProbabilityMeasure ν]
    (q : PublicLog → ℝ) (hq : Integrable q ν) :
    (1 : ℝ) / 2 ≤ max (riskAbsent ν q) (riskPresent ν q) := by
  have hs := complementary_risks ν q hq
  have h₀ := le_max_left (riskAbsent ν q) (riskPresent ν q)
  have h₁ := le_max_right (riskAbsent ν q) (riskPresent ν q)
  linarith

theorem minimax_attained (ν : Measure PublicLog) [IsProbabilityMeasure ν] :
    max (riskAbsent ν (fun _ => 1 / 2))
      (riskPresent ν (fun _ => 1 / 2)) = (1 : ℝ) / 2 := by
  unfold riskAbsent riskPresent
  simp [integral_const]
  norm_num

/-- Even access to the entire academic log cannot recover the private
predicate. The proof does not depend on the choice of codomain or scores. -/
theorem no_public_decoder :
    ¬ ∃ f : PublicLog → Prop, ∀ h, f (publicTrace h) ↔ CCBB h := by
  rintro ⟨f, hf⟩
  have hp := (hf (privateSuffix [exampleEpisode])).mpr BB_exists
  rw [public_private] at hp
  exact neither.2 ((hf []).mp hp)

#print axioms statistical_nonidentifiability
#print axioms minimax_lower_bound
#print axioms public_sigma_strict

end
end Trashlean.Academic.Life
