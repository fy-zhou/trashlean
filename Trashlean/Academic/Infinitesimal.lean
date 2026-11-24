import Trashlean.Academic.Degeneration

/-!
# TRASH-0001, Part II: Infinitesimal Academic Geometry

The Zariski topology forgets multiplicity, but the tower of infinitesimal
neighbourhoods remembers it. Repeated lexical degeneration converges to
zero in every fixed finite jet, while CCFA survives even the residue map.

All constructions below use the polynomial model of Part I.
-/

namespace Trashlean.Academic.Degeneration

open Polynomial
noncomputable section

abbrev AcademicRing := Polynomial ℝ

/-! ## The residue field and the adic filtration -/

/-- The first isomorphism theorem identifies the residue field. -/
def residueFieldEquiv : AcademicRing ⧸ vanishingIdeal ≃+* ℝ :=
  RingHom.quotientKerEquivOfSurjective evaluation_surjective

theorem vanishingIdeal_eq_span_X :
    vanishingIdeal = Ideal.span ({X} : Set AcademicRing) := by
  ext p
  change p ∈ RingHom.ker evaluation ↔ p ∈ Ideal.span ({X} : Set AcademicRing)
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero]
  rfl

/-- The order-n infinitesimal neighbourhood of the origin is cut out by m^n. -/
def jetIdeal (n : ℕ) : Ideal AcademicRing := vanishingIdeal ^ n

abbrev Jet (n : ℕ) := AcademicRing ⧸ jetIdeal n

def jetMap (n : ℕ) : AcademicRing →+* Jet n :=
  Ideal.Quotient.mk (jetIdeal n)

theorem jet_membership (n : ℕ) (p : AcademicRing) :
    p ∈ jetIdeal n ↔ ∀ d < n, p.coeff d = 0 := by
  rw [jetIdeal, vanishingIdeal_eq_span_X, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]

theorem jet_antitone {m n : ℕ} (h : m ≤ n) :
    jetIdeal n ≤ jetIdeal m :=
  Ideal.pow_le_pow_right h

theorem monomial_in_jet (n : ℕ) : (X : AcademicRing) ^ n ∈ jetIdeal n := by
  apply (jet_membership n _).mpr
  intro d hd
  rw [Polynomial.coeff_X_pow]
  simp [ne_of_lt hd]

theorem monomial_not_in_next_jet (n : ℕ) :
    (X : AcademicRing) ^ n ∉ jetIdeal (n + 1) := by
  intro h
  have hz := (jet_membership (n + 1) _).mp h n (Nat.lt_succ_self n)
  rw [Polynomial.coeff_X_pow_self] at hz
  exact one_ne_zero hz

/-- The adic filtration never stabilizes at a finite stage. -/
theorem strict_jet_filtration (n : ℕ) :
    jetIdeal (n + 1) < jetIdeal n := by
  refine lt_of_le_of_ne (jet_antitone (Nat.le_succ n)) ?_
  intro h
  have hm := monomial_in_jet n
  rw [← h] at hm
  exact monomial_not_in_next_jet n hm

/-! ## The inverse system of infinitesimal neighbourhoods -/

/-- Canonical transition maps between quotient rings. -/
def transition {m n : ℕ} (h : m ≤ n) : Jet n →+* Jet m :=
  Ideal.Quotient.factor (jet_antitone h)

@[simp] theorem transition_jetMap {m n : ℕ} (h : m ≤ n) (p : AcademicRing) :
    transition h (jetMap n p) = jetMap m p := rfl

/-- The filtration is separated: the intersection of all powers is zero.
This is proved coefficientwise, rather than assumed as an axiom. -/
theorem separated_filtration (p : AcademicRing)
    (h : ∀ n, p ∈ jetIdeal n) : p = 0 := by
  apply Polynomial.ext
  intro d
  rw [Polynomial.coeff_zero]
  exact (jet_membership (d + 1) p).mp (h (d + 1)) d (Nat.lt_succ_self d)

/-- The canonical map into the product of all jets is injective.
Together with the transition identities this gives a faithful compatible
family of finite-order observations. -/
theorem jets_jointly_injective :
    Function.Injective (fun p : AcademicRing => fun n : ℕ => jetMap n p) := by
  intro p q h
  apply sub_eq_zero.mp
  apply separated_filtration
  intro n
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change jetMap n (p - q) = 0
  have hn : jetMap n p = jetMap n q := congrFun h n
  rw [map_sub, hn, sub_self]

/-! ## Zariski topology versus infinitesimal geometry -/

def originPoint : PrimeSpectrum AcademicRing :=
  ⟨vanishingIdeal, RingHom.ker_isPrime evaluation⟩

theorem origin_is_closed :
    IsClosed ({originPoint} : Set (PrimeSpectrum AcademicRing)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal originPoint).mpr
    vanishingIdeal_maximal

/-- All positive-order thickenings have the same underlying closed locus. -/
theorem zariski_forgets_thickness (n : ℕ) (hn : n ≠ 0) :
    PrimeSpectrum.zeroLocus (jetIdeal n : Set AcademicRing) =
      PrimeSpectrum.zeroLocus (vanishingIdeal : Set AcademicRing) := by
  apply PrimeSpectrum.zeroLocus_eq_iff.mpr
  exact Ideal.radical_pow vanishingIdeal hn

theorem B_BB_same_zariski_locus :
    PrimeSpectrum.zeroLocus ({model CCFB} : Set AcademicRing) =
      PrimeSpectrum.zeroLocus ({model CCBB} : Set AcademicRing) := by
  calc
    _ = PrimeSpectrum.zeroLocus (vanishingIdeal : Set AcademicRing) := by
      rw [vanishingIdeal_eq_span_X, PrimeSpectrum.zeroLocus_span]
      rfl
    _ = PrimeSpectrum.zeroLocus (jetIdeal 2 : Set AcademicRing) :=
      (zariski_forgets_thickness 2 (by decide)).symm
    _ = _ := by
      rw [jetIdeal, vanishingIdeal_eq_span_X, Ideal.span_singleton_pow,
        PrimeSpectrum.zeroLocus_span]
      rfl

/-- The first nontrivial thickening distinguishes the two B-origin tokens. -/
theorem B_nonzero_in_second_jet : jetMap 2 (model CCFB) ≠ 0 := by
  intro h
  have hm : model CCFB ∈ jetIdeal 2 := Ideal.Quotient.eq_zero_iff_mem.mp h
  exact monomial_not_in_next_jet 1 (by simpa [model, CCFB] using hm)

theorem BB_zero_in_second_jet : jetMap 2 (model CCBB) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact monomial_in_jet 2

theorem B_BB_distinct_infinitesimal_structure :
    jetMap 2 (model CCFB) ≠ jetMap 2 (model CCBB) := by
  rw [BB_zero_in_second_jet]
  exact B_nonzero_in_second_jet

/-- The B-coordinate is a genuine nonzero nilpotent in the second jet ring. -/
theorem B_nonzero_nilpotent :
    jetMap 2 (model CCFB) ≠ 0 ∧ IsNilpotent (jetMap 2 (model CCFB)) := by
  refine ⟨B_nonzero_in_second_jet, ⟨2, ?_⟩⟩
  rw [← map_pow, ← lexical_degeneration]
  exact BB_zero_in_second_jet

/-- The A-coordinate remains visible in every positive-order jet. -/
theorem A_survives_all_jets (n : ℕ) (hn : 0 < n) :
    jetMap n (model CCFA) ≠ 0 := by
  intro h
  have hm : model CCFA ∈ jetIdeal n := Ideal.Quotient.eq_zero_iff_mem.mp h
  have hz := (jet_membership n _).mp hm 0 hn
  rw [Polynomial.coeff_zero_eq_eval_zero] at hz
  change credit CCFA = 0 at hz
  exact one_ne_zero (credit_A.symm.trans hz)

/-! ## Dynamics: exponential growth of the vanishing order -/

def iteratedDegeneration : ℕ → Artifact
  | 0 => CCFB
  | n + 1 => .square (iteratedDegeneration n)

theorem iterated_model (n : ℕ) :
    model (iteratedDegeneration n) = X ^ (2 ^ n) := by
  induction n with
  | zero => simp [iteratedDegeneration, model, CCFB]
  | succ n ih =>
      change model (iteratedDegeneration n) ^ 2 = X ^ (2 ^ (n + 1))
      rw [ih, pow_succ (2 : ℕ), pow_mul]

/-- Exact vanishing order, not merely a lower bound. -/
theorem exponential_vanishing_order (n : ℕ) :
    model (iteratedDegeneration n) ∈ jetIdeal (2 ^ n) ∧
      model (iteratedDegeneration n) ∉ jetIdeal (2 ^ n + 1) := by
  rw [iterated_model]
  exact ⟨monomial_in_jet _, monomial_not_in_next_jet _⟩

private theorem index_le_exp (n : ℕ) : n ≤ (2 : ℕ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
      omega

/-- Every fixed finite jet eventually sees only zero. -/
theorem finite_jet_eventual_extinction (k n : ℕ) (h : k ≤ n) :
    jetMap k (model (iteratedDegeneration n)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact jet_antitone (h.trans (index_le_exp n))
    (exponential_vanishing_order n).1

/-- A sharp distinction: increasing degeneration destroys all finite-order
observations, whereas A survives every positive-order observation. -/
theorem no_jet_recovery (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    jetMap k (model CCFA) ≠ jetMap k (model (iteratedDegeneration n)) := by
  rw [finite_jet_eventual_extinction k n hkn]
  exact A_survives_all_jets k hk

theorem infinitesimal_obstruction :
    CCFA ≠ CCBB ∧
    PrimeSpectrum.zeroLocus ({model CCFB} : Set AcademicRing) =
      PrimeSpectrum.zeroLocus ({model CCBB} : Set AcademicRing) ∧
    jetMap 2 (model CCFB) ≠ jetMap 2 (model CCBB) ∧
    (∀ n, jetIdeal (n + 1) < jetIdeal n) ∧
    (∀ k n : ℕ, 0 < k → k ≤ n →
      jetMap k (model CCFA) ≠ jetMap k (model (iteratedDegeneration n))) := by
  exact ⟨CCFA_ne_CCBB, B_BB_same_zariski_locus,
    B_BB_distinct_infinitesimal_structure, strict_jet_filtration,
    no_jet_recovery⟩

#print axioms infinitesimal_obstruction
#print axioms jets_jointly_injective

end
end Trashlean.Academic.Degeneration
