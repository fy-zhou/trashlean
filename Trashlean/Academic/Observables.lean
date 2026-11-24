import Trashlean.Academic.Life

/-!
# Split exact linear algebra of public observation

The restriction of arbitrary real-valued observables to the public section
is a split epimorphism. Its kernel records all variation invisible on the
public section, and every observable has a unique decomposition into a
public component and a residual component.
-/

namespace Trashlean.Academic.Life

noncomputable section

abbrev PublicObservable := PublicLog → ℝ
abbrev FullObservable := History → ℝ

def pullbackObservable : PublicObservable →ₗ[ℝ] FullObservable where
  toFun f h := f (publicTrace h)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def restrictObservable : FullObservable →ₗ[ℝ] PublicObservable where
  toFun f l := f (restorePublic l)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem restrict_pullback (f : PublicObservable) :
    restrictObservable (pullbackObservable f) = f := by
  funext l
  change f (publicTrace (restorePublic l)) = f l
  rw [public_restore]

theorem pullback_injective : Function.Injective pullbackObservable := by
  intro f g h
  have hh := congrArg restrictObservable h
  simpa using hh

theorem restrict_surjective : Function.Surjective restrictObservable :=
  fun f => ⟨pullbackObservable f, restrict_pullback f⟩

/-- A linear idempotent onto the subspace of public observables. -/
def publicProjection : FullObservable →ₗ[ℝ] FullObservable :=
  pullbackObservable.comp restrictObservable

def residualProjection : FullObservable →ₗ[ℝ] FullObservable :=
  LinearMap.id - publicProjection

@[simp] theorem publicProjection_idempotent (f : FullObservable) :
    publicProjection (publicProjection f) = publicProjection f := by
  change pullbackObservable (restrictObservable
    (pullbackObservable (restrictObservable f))) = _
  rw [restrict_pullback]
  rfl

theorem residual_in_kernel (f : FullObservable) :
    residualProjection f ∈ LinearMap.ker restrictObservable := by
  apply LinearMap.mem_ker.mpr
  change restrictObservable (f - pullbackObservable (restrictObservable f)) = 0
  rw [map_sub, restrict_pullback, sub_self]

theorem residual_fixed (f : LinearMap.ker restrictObservable) :
    residualProjection (f : FullObservable) = f := by
  have hz : restrictObservable (f : FullObservable) = 0 :=
    LinearMap.mem_ker.mp f.property
  change (f : FullObservable) - pullbackObservable (restrictObservable f) = _
  rw [hz, map_zero, sub_zero]

theorem projections_sum (f : FullObservable) :
    publicProjection f + residualProjection f = f := by
  change publicProjection f + (f - publicProjection f) = f
  abel

/-- The algebraic splitting is an actual linear equivalence, not only a
pointwise identity. -/
def observableSplit :
    FullObservable ≃ₗ[ℝ] PublicObservable × LinearMap.ker restrictObservable where
  toFun f := (restrictObservable f, ⟨residualProjection f, residual_in_kernel f⟩)
  invFun p := pullbackObservable p.1 + (p.2 : FullObservable)
  left_inv := by
    intro f
    exact projections_sum f
  right_inv := by
    rintro ⟨f, g⟩
    have hg : restrictObservable (g : FullObservable) = 0 :=
      LinearMap.mem_ker.mp g.property
    apply Prod.ext
    · change restrictObservable (pullbackObservable f + (g : FullObservable)) = f
      rw [map_add, restrict_pullback, hg, add_zero]
    · apply Subtype.ext
      change residualProjection (pullbackObservable f + (g : FullObservable)) = g
      rw [map_add, residual_fixed]
      have hz : residualProjection (pullbackObservable f) = 0 := by
        change pullbackObservable f -
          pullbackObservable (restrictObservable (pullbackObservable f)) = 0
        rw [restrict_pullback, sub_self]
      rw [hz, zero_add]
  map_add' := by
    intro f g
    apply Prod.ext
    · exact map_add restrictObservable f g
    · apply Subtype.ext
      exact map_add residualProjection f g
  map_smul' := by
    intro r f
    apply Prod.ext
    · exact map_smul restrictObservable r f
    · apply Subtype.ext
      exact map_smul residualProjection r f

/-- An observable factors through the public trace exactly when its hidden
residual is zero. -/
theorem residual_zero_iff_observable (f : FullObservable) :
    residualProjection f = 0 ↔
      ∃ g : PublicObservable, f = pullbackObservable g := by
  constructor
  · intro h
    refine ⟨restrictObservable f, ?_⟩
    have hp := projections_sum f
    rw [h, add_zero] at hp
    exact hp.symm
  · rintro ⟨g, rfl⟩
    change pullbackObservable g -
      pullbackObservable (restrictObservable (pullbackObservable g)) = 0
    rw [restrict_pullback, sub_self]

/-- The private-event indicator is genuinely nonzero in the hidden kernel. -/
def privateIndicator : FullObservable :=
  fun h => if CCBB h then 1 else 0

theorem privateIndicator_kernel :
    privateIndicator ∈ LinearMap.ker restrictObservable := by
  apply LinearMap.mem_ker.mpr
  funext l
  change (if CCBB (restorePublic l) then (1 : ℝ) else 0) = 0
  simp [no_private_in_public]

theorem privateIndicator_nonzero : privateIndicator ≠ 0 := by
  intro h
  have he := congrFun h (privateSuffix [exampleEpisode])
  change (if CCBB (privateSuffix [exampleEpisode]) then (1 : ℝ) else 0) = 0 at he
  simp [BB_exists] at he

theorem privateIndicator_not_public :
    ¬ ∃ g : PublicObservable, privateIndicator = pullbackObservable g := by
  intro h
  obtain ⟨g, hg⟩ := h
  have hz := LinearMap.mem_ker.mp privateIndicator_kernel
  rw [hg, restrict_pullback] at hz
  exact privateIndicator_nonzero (by rw [hg, hz, map_zero])

#print axioms observableSplit
#print axioms privateIndicator_not_public

end
end Trashlean.Academic.Life
