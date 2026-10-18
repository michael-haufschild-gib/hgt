import GaloisForLFunctions.RHTower.CCMRestrictedWeilEvenStrictDomain

/-!
# The actual finite-aperture even-polar ground operator

The literal constrained form domain is embedded into its physical L2 closure. Compressing the actual bounded Weil remainder constructs its self-adjoint Friedrichs operator with compact resolvent. Every variational even-polar ground lies in the operator domain and satisfies the exact ground eigenvalue equation.
-/

set_option autoImplicit false
open Complex MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround RHTower.CCMGroundStructure
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section


namespace RHTower.CCMEvenSector

theorem isClosed_evenPolarSubmodule (a : SuzukiPositiveAperture) :
    IsClosed (evenPolarSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  change IsClosed ((ccmPolarConstraintSubmodule a : Set (CCMArchimedeanFormDomain a)) ∩
    {u | ccmArchimedeanFormReflection a u = u})
  exact (isClosed_ccmPolarConstraintSubmodule a).inter
    (isClosed_eq (ccmArchimedeanFormReflection a).continuous continuous_id)

local instance evenPolarFormNorm (a : SuzukiPositiveAperture) :
    NormedAddCommGroup (evenPolarSubmodule a) := inferInstance

local instance evenPolarFormInner (a : SuzukiPositiveAperture) :
    InnerProductSpace ℂ (evenPolarSubmodule a) := inferInstance

instance evenPolarSubmodule_complete (a : SuzukiPositiveAperture) :
    CompleteSpace (evenPolarSubmodule a) := (isClosed_evenPolarSubmodule a).completeSpace_coe

/-- The original physical embedding restricted to the even sector and both pole constraints. -/
def evenPolarPhysicalEmbedding (a : SuzukiPositiveAperture) :
    evenPolarSubmodule a →L[ℂ] suzukiApertureHilbert a :=
  (ccmArchimedeanFormToAperture a).comp (evenPolarSubmodule a).subtypeL

/-- The physical completion of the actual constrained form vectors. -/
def evenPolarPhysicalSpace (a : SuzukiPositiveAperture) :
    Submodule ℂ (suzukiApertureHilbert a) := (evenPolarPhysicalEmbedding a).range.topologicalClosure

local instance evenPolarPhysicalNorm (a : SuzukiPositiveAperture) :
    NormedAddCommGroup (evenPolarPhysicalSpace a) := inferInstance

local instance evenPolarPhysicalInner (a : SuzukiPositiveAperture) :
    InnerProductSpace ℂ (evenPolarPhysicalSpace a) := inferInstance

instance evenPolarPhysicalSpace_complete (a : SuzukiPositiveAperture) :
    CompleteSpace (evenPolarPhysicalSpace a) :=
  (evenPolarPhysicalEmbedding a).range.isClosed_topologicalClosure.completeSpace_coe

def evenPolarEmbedding (a : SuzukiPositiveAperture) :
    evenPolarSubmodule a →L[ℂ] evenPolarPhysicalSpace a :=
  (evenPolarPhysicalEmbedding a).codRestrict (evenPolarPhysicalSpace a)
    (fun u => (evenPolarPhysicalEmbedding a).range.le_topologicalClosure ⟨u, rfl⟩)

theorem evenPolarEmbedding_injective (a : SuzukiPositiveAperture) :
    Function.Injective (evenPolarEmbedding a) := by
  intro u v huv
  apply Subtype.ext
  apply ccmArchimedeanFormToAperture_injective a
  exact congrArg Subtype.val huv

theorem dense_evenPolarEmbedding (a : SuzukiPositiveAperture) :
    Dense ((evenPolarEmbedding a).range : Set (evenPolarPhysicalSpace a)) := by
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  intro x
  have hr : Subtype.val '' ((evenPolarEmbedding a).range : Set (evenPolarPhysicalSpace a)) =
      ((evenPolarPhysicalEmbedding a).range : Set (suzukiApertureHilbert a)) := by
    ext y
    constructor
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨evenPolarEmbedding a u, ⟨u, rfl⟩, rfl⟩
  change (x : suzukiApertureHilbert a) ∈ closure
    (Subtype.val '' ((evenPolarEmbedding a).range : Set (evenPolarPhysicalSpace a)))
  rw [hr]
  change (x : suzukiApertureHilbert a) ∈
    ((evenPolarPhysicalEmbedding a).range.topologicalClosure : Set (suzukiApertureHilbert a))
  exact x.property

theorem isCompactOperator_evenPolarEmbedding (a : SuzukiPositiveAperture) :
    IsCompactOperator (evenPolarEmbedding a) := by
  have h := (isCompactOperator_ccmArchimedeanFormToAperture a).comp_clm
    (evenPolarSubmodule a).subtypeL
  apply h.codRestrict
  exact (evenPolarPhysicalEmbedding a).range.isClosed_topologicalClosure

local instance evenPolarCLMStar (a : SuzukiPositiveAperture) :
    Star (evenPolarPhysicalSpace a →L[ℂ] evenPolarPhysicalSpace a) :=
  ContinuousLinearMap.instStarId (𝕜 := ℂ) (E := evenPolarPhysicalSpace a)

local instance evenPolarPMapStar (a : SuzukiPositiveAperture) :
    Star (evenPolarPhysicalSpace a →ₗ.[ℂ] evenPolarPhysicalSpace a) :=
  LinearPMap.instStar (𝕜 := ℂ) (E := evenPolarPhysicalSpace a)
/-- Compression of the actual Gamma, polar and finite-prime bounded remainder. -/
def evenPolarRemainder (a : SuzukiPositiveAperture) :
    evenPolarPhysicalSpace a →L[ℂ] evenPolarPhysicalSpace a :=
  (evenPolarPhysicalSpace a).orthogonalProjectionOnto.comp
    ((ccmRestrictedWeilBoundedRemainder a).comp (evenPolarPhysicalSpace a).subtypeL)

theorem evenPolarRemainder_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (evenPolarRemainder a) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
    (𝕜 := ℂ) (E := evenPolarPhysicalSpace a) (A := evenPolarRemainder a)).mpr
  intro x y
  change inner ℂ ((evenPolarPhysicalSpace a).orthogonalProjectionOnto
      (ccmRestrictedWeilBoundedRemainder a x)) y =
    inner ℂ x ((evenPolarPhysicalSpace a).orthogonalProjectionOnto
      (ccmRestrictedWeilBoundedRemainder a y))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric x y

theorem inner_evenPolarRemainder (a : SuzukiPositiveAperture)
    (x y : evenPolarPhysicalSpace a) :
    inner ℂ (evenPolarRemainder a x) y =
      inner ℂ (ccmRestrictedWeilBoundedRemainder a x) (y : suzukiApertureHilbert a) :=
  (evenPolarPhysicalSpace a).inner_orthogonalProjectionOnto_eq_of_mem_right y _

/-- Exact form identity, with the original prime terms and both original pole constraints. -/
theorem evenPolarForm_eq (a : SuzukiPositiveAperture) (u v : evenPolarSubmodule a) :
    inner ℂ u v + inner ℂ (evenPolarRemainder a (evenPolarEmbedding a u))
      (evenPolarEmbedding a v) = ccmRestrictedWeilForm a u.val v.val := by
  rw [inner_evenPolarRemainder]
  rfl

/-- Explicit Friedrichs operator of the actual even-polar Weil form. -/
def evenPolarGroundOperator (a : SuzukiPositiveAperture) :
    evenPolarPhysicalSpace a →ₗ.[ℂ] evenPolarPhysicalSpace a :=
  boundedPerturbedFriedrichsOperator
    (H := evenPolarPhysicalSpace a) (V := evenPolarSubmodule a)
    (evenPolarEmbedding a) (evenPolarRemainder a)
    (evenPolarRemainder_isSelfAdjoint a)

theorem evenPolarGroundOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (evenPolarGroundOperator a) :=
  boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (H := evenPolarPhysicalSpace a) (V := evenPolarSubmodule a) _ _ _
    (evenPolarEmbedding_injective a) (dense_evenPolarEmbedding a)

theorem evenPolarGroundOperator_hasCompactResolvent (a : SuzukiPositiveAperture) :
    LinearPMap.HasCompactResolventAt (H := evenPolarPhysicalSpace a) (evenPolarGroundOperator a)
      (-(boundedPerturbedFormShift (H := evenPolarPhysicalSpace a) (evenPolarRemainder a) : ℂ)) :=
  boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    (H := evenPolarPhysicalSpace a) (V := evenPolarSubmodule a) _ _ _
    (evenPolarEmbedding_injective a) (dense_evenPolarEmbedding a)
    (isCompactOperator_evenPolarEmbedding a)

theorem evenGround_shifted_form_zero (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsEvenGround a u)
    (v : evenPolarSubmodule a) :
    ccmRestrictedWeilForm a u v.val -
      inner ℂ ((evenGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a v.val) = 0 := by
  let K := ccmRestrictedWeilFormBirmanSchwinger a (evenGroundEnergy a)
  have hr := mem_compactConstrainedRadical_of_null (evenPolarSubmodule a) K
    (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a _)
    (fun w hw => by
      rw [ccmRestrictedWeil_shifted_diagonal]
      exact sub_nonneg.mpr (evenGroundEnergy_mul_le a w hw.1 hw.2)) ⟨hu.1, hu.2.1⟩
    (by rw [ccmRestrictedWeil_shifted_diagonal, hu.2.2, sub_self])
  have hz := ((mem_compactConstrainedRadical _ K u).mp hr).2 v.val v.property
  have hz' : inner ℂ (u - K u) v.val = 0 := by
    have hc := congrArg (starRingEnd ℂ) hz
    rw [inner_conj_symm (𝕜 := ℂ) (u - K u) v.val, map_zero] at hc
    exact hc
  rw [ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger]
  exact hz'

theorem evenPolarGroundOperator_represents (a : SuzukiPositiveAperture)
    (u : evenPolarSubmodule a) (y : evenPolarPhysicalSpace a)
    (hform : ∀ v : evenPolarSubmodule a,
      inner ℂ u v + inner ℂ (evenPolarRemainder a (evenPolarEmbedding a u))
        (evenPolarEmbedding a v) = inner ℂ y (evenPolarEmbedding a v)) :
    ∃ hm : evenPolarEmbedding a u ∈ (evenPolarGroundOperator a).domain,
      evenPolarGroundOperator a ⟨evenPolarEmbedding a u, hm⟩ = y := by
  unfold evenPolarGroundOperator
  have hB := evenPolarRemainder_isSelfAdjoint a
  have hinj := evenPolarEmbedding_injective a
  have hdense := dense_evenPolarEmbedding a
  exact boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (evenPolarEmbedding a) (evenPolarRemainder a)
    hB hinj hdense u y hform

/-- Every variational even-polar ground lies in the actual operator domain and is an eigenstate. -/
theorem evenPolarGroundOperator_ground (a : SuzukiPositiveAperture)
    (u : evenPolarSubmodule a) (hu : IsEvenGround a u.val) :
    ∃ hm : evenPolarEmbedding a u ∈ (evenPolarGroundOperator a).domain,
      evenPolarGroundOperator a ⟨evenPolarEmbedding a u, hm⟩ =
        (evenGroundEnergy a : ℂ) • evenPolarEmbedding a u := by
  apply evenPolarGroundOperator_represents
  intro v
  rw [evenPolarForm_eq]
  exact sub_eq_zero.mp (evenGround_shifted_form_zero a u.val hu v)

theorem evenPolarGroundEnergy_lower_bound (a : SuzukiPositiveAperture)
    (u : evenPolarSubmodule a) :
    evenGroundEnergy a * ‖evenPolarEmbedding a u‖ ^ 2 ≤
      (inner ℂ u u + inner ℂ (evenPolarRemainder a (evenPolarEmbedding a u))
        (evenPolarEmbedding a u)).re := by
  rw [evenPolarForm_eq, ccmRestrictedWeilForm_self_re_eq_source]
  exact evenGroundEnergy_mul_le a u.val u.property.1 u.property.2

/-- Unconditional normalized operator ground at every positive aperture. -/
theorem exists_normalized_evenPolarGroundOperator_eigenstate (a : SuzukiPositiveAperture) :
    ∃ u : evenPolarSubmodule a, ‖evenPolarEmbedding a u‖ = 1 ∧
      ∃ hm : evenPolarEmbedding a u ∈ (evenPolarGroundOperator a).domain,
        evenPolarGroundOperator a ⟨evenPolarEmbedding a u, hm⟩ =
          (evenGroundEnergy a : ℂ) • evenPolarEmbedding a u := by
  obtain ⟨u, hp, he, hn, hQ⟩ := exists_evenGround a
  refine ⟨⟨u, hp, he⟩, hn, evenPolarGroundOperator_ground a _ ⟨hp, he, ?_⟩⟩
  rw [hQ, hn]
  ring

/-- The ground can retain the existing exact two-axis zero theorem for its entire transform. -/
theorem exists_crossRooted_evenPolarGroundOperator_eigenstate (a : SuzukiPositiveAperture) :
    ∃ u : evenPolarSubmodule a, evenPolarEmbedding a u ≠ 0 ∧
      (∃ hm : evenPolarEmbedding a u ∈ (evenPolarGroundOperator a).domain,
        evenPolarGroundOperator a ⟨evenPolarEmbedding a u, hm⟩ =
          (evenGroundEnergy a : ℂ) • evenPolarEmbedding a u) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u.val) w = 0 → w ≠ polarPoint (1 / 2) →
        w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0 := by
  obtain ⟨u, hu, hn, hz⟩ := exists_crossRooted_evenGround a
  refine ⟨⟨u, hu.1, hu.2.1⟩, ?_, evenPolarGroundOperator_ground a _ hu, hz⟩
  intro h
  exact hn (congrArg Subtype.val h)

end RHTower.CCMEvenSector

end
