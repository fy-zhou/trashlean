import Mathlib

/-!
# TRASH-0001: The Fundamental Theorem of Academic Degeneration

An algebraic, categorical and topological obstruction to the equivalence of
CCFA and CCBB.

CCFA and CCFB are conference-category tokens; CCBB is the lexical parody
derived from CCFB. The model is fictional. Its scalar credit counts A-origin
tokens, not scientific merit or human worth.

The proof goes through the representation in ℝ[X], a conserved character,
a thin category, the residue ring of a maximal ideal, and a closed linear
span in a topological vector space.
-/

namespace Trashlean.Academic.Degeneration

open Polynomial CategoryTheory
noncomputable section

/-! ## I. Syntax and polynomial semantics -/

inductive Artifact where
  | a
  | b
  | revise (x : Artifact) (q : Polynomial ℝ)
  | square (x : Artifact)

def CCFA : Artifact := .a
def CCFB : Artifact := .b
def CCBB : Artifact := .square CCFB

/-- A representation into the real polynomial ring. -/
def model : Artifact → Polynomial ℝ
  | .a => 1 + X
  | .b => X
  | .revise x q => model x + X * q
  | .square x => model x ^ 2

/-- The sector of the original artifact. -/
def sector : Artifact → Bool
  | .a => true
  | .b => false
  | .revise x _ => sector x
  | .square x => sector x

theorem lexical_degeneration :
    model CCBB = (model CCFB) ^ 2 := rfl

/-- Evaluation at the origin is a ring character. -/
def evaluation : Polynomial ℝ →+* ℝ :=
  Polynomial.evalRingHom 0

def credit (x : Artifact) : ℝ := (model x).eval 0

/-- The character is Boolean-valued on every syntactic history. -/
theorem semantic_constant (x : Artifact) :
    (model x).eval 0 = if sector x then 1 else 0 := by
  induction x with
  | a => simp [model, sector]
  | b => simp [model, sector]
  | revise x q ih => simp [model, sector, ih]
  | square x ih =>
      cases h : sector x <;> simp [model, sector, ih, h]

theorem credit_sector (x : Artifact) :
    credit x = if sector x then 1 else 0 :=
  semantic_constant x

@[simp] theorem credit_A : credit CCFA = 1 := by
  simp [credit, model, CCFA]

@[simp] theorem credit_B : credit CCFB = 0 := by
  simp [credit, model, CCFB]

@[simp] theorem credit_BB : credit CCBB = 0 := by
  simp [credit, model, CCBB, CCFB]

/-! ## II. Rewriting theory and a categorical conservation law -/

inductive Derives : Artifact → Artifact → Prop where
  | refl (x : Artifact) : Derives x x
  | revise (x : Artifact) (q : Polynomial ℝ) : Derives x (.revise x q)
  | square (x : Artifact) : Derives x (.square x)
  | trans {x y z : Artifact} :
      Derives x y → Derives y z → Derives x z

instance : Preorder Artifact where
  le := Derives
  le_refl := Derives.refl
  le_trans := by
    intro x y z hxy hyz
    exact Derives.trans hxy hyz

theorem fundamental_derivation : CCFB ≤ CCBB :=
  Derives.square CCFB

theorem sector_conserved {x y : Artifact} (h : Derives x y) :
    sector x = sector y := by
  induction h with
  | refl _ => rfl
  | revise _ _ => rfl
  | square _ => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem credit_conserved {x y : Artifact} (h : Derives x y) :
    credit x = credit y := by
  rw [credit_sector x, credit_sector y, sector_conserved h]

theorem descendant_zero {x : Artifact} (h : CCFB ≤ x) :
    credit x = 0 :=
  (credit_conserved h).symm.trans credit_B

/-- Both the rewriting system and the ordered real line are thin categories. -/
theorem credit_monotone : Monotone credit := by
  intro x y h
  exact le_of_eq (credit_conserved h)

def creditFunctor : Artifact ⥤ ℝ := credit_monotone.functor

def degenerationMorphism : CCFB ⟶ CCBB :=
  CategoryTheory.homOfLE fundamental_derivation

/-- A hypothetical arrow would map to an arrow from 1 to 0 in the target. -/
theorem no_arrow_A_to_BB : ¬ Nonempty (CCFA ⟶ CCBB) := by
  rintro ⟨f⟩
  have h := CategoryTheory.leOfHom (creditFunctor.map f)
  change credit CCFA ≤ credit CCBB at h
  rw [credit_A, credit_BB] at h
  norm_num at h

theorem no_arrow_BB_to_A : ¬ Nonempty (CCBB ⟶ CCFA) := by
  rintro ⟨f⟩
  have h := credit_conserved (CategoryTheory.leOfHom f)
  rw [credit_BB, credit_A] at h
  norm_num at h

/-- In particular, no isomorphism can exist in the derivation category. -/
theorem no_categorical_equivalence : ¬ Nonempty (CCFA ≅ CCBB) := by
  rintro ⟨e⟩
  exact no_arrow_A_to_BB ⟨e.hom⟩

/-- Equality would induce an identity transported along that equality. -/
theorem CCFA_ne_CCBB : CCFA ≠ CCBB := by
  intro h
  exact no_arrow_A_to_BB ⟨eqToHom h⟩

/-! ## III. Commutative algebra and the residue field at the origin -/

def vanishingIdeal : Ideal (Polynomial ℝ) :=
  RingHom.ker evaluation

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro r
  refine ⟨Polynomial.C r, ?_⟩
  simp [evaluation]

/-- The kernel of the surjective character to a field is maximal. -/
theorem vanishingIdeal_maximal : vanishingIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective evaluation evaluation_surjective

theorem B_descendant_mem_ideal {x : Artifact} (h : CCFB ≤ x) :
    model x ∈ vanishingIdeal := by
  change model x ∈ RingHom.ker evaluation
  rw [RingHom.mem_ker]
  change credit x = 0
  exact descendant_zero h

def residue (x : Artifact) : Polynomial ℝ ⧸ vanishingIdeal :=
  Ideal.Quotient.mk vanishingIdeal (model x)

/-- Every B-derived artifact disappears in the residue ring. -/
theorem B_descendant_residue_zero {x : Artifact} (h : CCFB ≤ x) :
    residue x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (B_descendant_mem_ideal h)

theorem A_residue_ne_zero : residue CCFA ≠ 0 := by
  intro h
  have hm : model CCFA ∈ RingHom.ker evaluation :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  have he := RingHom.mem_ker.mp hm
  change credit CCFA = 0 at he
  exact one_ne_zero (credit_A.symm.trans he)

/-- Equality fails even after passage to the residue ring. -/
theorem residue_separation : residue CCFA ≠ residue CCBB := by
  rw [B_descendant_residue_zero fundamental_derivation]
  exact A_residue_ne_zero

theorem algebraic_obstruction : model CCFA ≠ model CCBB := by
  intro h
  exact residue_separation (congrArg (Ideal.Quotient.mk vanishingIdeal) h)

/-! ## IV. Linear algebra and functional analysis -/

/-- All real-valued functions with the product (pointwise) topology. -/
abbrev Profile := ℝ → ℝ

def profile (x : Artifact) : Profile :=
  fun t => (model x).eval t

/-- Evaluation at the origin is also a linear functional on profiles. -/
def originFunctional : Profile →ₗ[ℝ] ℝ where
  toFun f := f 0
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

def BProfiles : Set Profile :=
  {f | ∃ x : Artifact, CCFB ≤ x ∧ f = profile x}

def BSpan : Submodule ℝ Profile :=
  Submodule.span ℝ BProfiles

theorem BSpan_le_kernel : BSpan ≤ LinearMap.ker originFunctional := by
  apply Submodule.span_le.mpr
  rintro f ⟨x, hx, rfl⟩
  apply LinearMap.mem_ker.mpr
  change credit x = 0
  exact descendant_zero hx

/-- A closed hyperplane containing every finite linear combination of
B-derived profiles, including arbitrary real coefficients. -/
def zeroHyperplane : Set Profile := {f | f 0 = 0}

theorem zeroHyperplane_closed : IsClosed zeroHyperplane := by
  exact isClosed_eq (continuous_apply (0 : ℝ)) continuous_const

theorem BSpan_subset_hyperplane :
    (BSpan : Set Profile) ⊆ zeroHyperplane := by
  intro f hf
  have hk := BSpan_le_kernel hf
  have hz := LinearMap.mem_ker.mp hk
  exact hz

/-- Even the closure of the linear span cannot escape the hyperplane. -/
theorem closed_span_confinement :
    closure (BSpan : Set Profile) ⊆ zeroHyperplane :=
  closure_minimal BSpan_subset_hyperplane zeroHyperplane_closed

theorem no_finite_linear_substitution : profile CCFA ∉ BSpan := by
  intro h
  have hz := LinearMap.mem_ker.mp (BSpan_le_kernel h)
  change credit CCFA = 0 at hz
  exact one_ne_zero (credit_A.symm.trans hz)

/-- No pointwise limit (indeed no topological closure point) of arbitrary
finite real linear combinations of B-descendants can be the A-profile. -/
theorem no_infinite_substitution :
    profile CCFA ∉ closure (BSpan : Set Profile) := by
  intro h
  have hz := closed_span_confinement h
  change credit CCFA = 0 at hz
  exact one_ne_zero (credit_A.symm.trans hz)

/-! ## V. The grand obstruction theorem -/

theorem fundamental_theorem :
    (CCFB ≤ CCBB) ∧
    (CCFA ≠ CCBB) ∧
    (¬ Nonempty (CCFA ≅ CCBB)) ∧
    vanishingIdeal.IsMaximal ∧
    (residue CCFA ≠ residue CCBB) ∧
    (profile CCFA ∉ closure (BSpan : Set Profile)) := by
  exact ⟨fundamental_derivation, CCFA_ne_CCBB,
    no_categorical_equivalence, vanishingIdeal_maximal,
    residue_separation, no_infinite_substitution⟩

#print axioms CCFA_ne_CCBB
#print axioms fundamental_theorem

end
end Trashlean.Academic.Degeneration
