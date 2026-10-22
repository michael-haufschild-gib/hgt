import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureGroundSimplicity

/-!
# Actual restricted-Weil Birman--Schwinger reduction

The exact unbounded CCM restricted-Weil eigenproblem is equivalent to fixed-vector equations for
explicit compact Birman--Schwinger pencils.  The ambient pencil preserves scalar, polar, and
finite-prime channels with their literal signs.  Its sandwich on the complete archimedean form
domain is compact and self-adjoint, and its energy dependence is an exact positive affine flow.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Every exact restricted-Weil operator vector has a complete-form lift realizing all mixed
pairings, not only its diagonal quadratic value. -/
theorem ccmRestrictedWeilOperator_exists_completeFormLift_mixed
    (b : SuzukiPositiveAperture)
    (x : (ccmRestrictedWeilOperator b).domain) :
    ∃ u : CCMArchimedeanFormDomain b,
      ccmArchimedeanFormToAperture b u =
          (x : suzukiApertureHilbert b) ∧
        ∀ v : CCMArchimedeanFormDomain b,
          ccmRestrictedWeilForm b u v =
            inner ℂ (ccmRestrictedWeilOperator b x)
              (ccmArchimedeanFormToAperture b v) := by
  let J := ccmArchimedeanFormToAperture b
  let B := ccmRestrictedWeilBoundedRemainder b
  let C := boundedPerturbedFormCovariance J B
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
      (ccmArchimedeanFormToAperture_injective b)
      (denseRange_ccmArchimedeanFormToAperture b)
  have hxrange : (x : suzukiApertureHilbert b) ∈ C.range := by
    simpa only [J, B, C, ccmRestrictedWeilOperator,
      boundedPerturbedFriedrichsOperator_domain,
      closedDenseInverse_domain] using x.property
  obtain ⟨y, hy⟩ := hxrange
  have hmem : C y ∈ (ccmRestrictedWeilOperator b).domain := by
    change C y ∈ (closedDenseInverse C).domain
    exact (closedDenseInverse_apply_C C hCinj y).1
  let xc : (ccmRestrictedWeilOperator b).domain := ⟨C y, hmem⟩
  let u : CCMArchimedeanFormDomain b :=
    boundedPerturbedFormRieszInv J B
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b) (J.adjoint y)
  have hrepSelf := boundedPerturbedFriedrichsOperator_represents_form
    J B (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
      (ccmArchimedeanFormToAperture_injective b)
      (denseRange_ccmArchimedeanFormToAperture b) y u
  change (xc : suzukiApertureHilbert b) = J u ∧
      inner ℂ (ccmRestrictedWeilOperator b xc) (J u) =
        inner ℂ u u + inner ℂ (B (J u)) (J u) at hrepSelf
  have hxc : xc = x := Subtype.ext hy
  refine ⟨u, ?_, ?_⟩
  · rw [← hrepSelf.1, hxc]
  · intro v
    have hrep := boundedPerturbedFriedrichsOperator_represents_form
      J B (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
        (ccmArchimedeanFormToAperture_injective b)
        (denseRange_ccmArchimedeanFormToAperture b) y v
    change (xc : suzukiApertureHilbert b) = J u ∧
        inner ℂ (ccmRestrictedWeilOperator b xc) (J v) =
          inner ℂ u v + inner ℂ (B (J u)) (J v) at hrep
    change inner ℂ u v + inner ℂ (B (J u)) (J v) =
      inner ℂ (ccmRestrictedWeilOperator b x) (J v)
    rw [← hrep.2, hxc]

noncomputable def ccmRestrictedWeilCanonicalGroundEigenstate
    (a : SuzukiPositiveAperture) : (ccmRestrictedWeilOperator a).domain :=
  Classical.choose (ccmRestrictedWeilOperator_exists_groundEigenstate a)

theorem ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero
    (a : SuzukiPositiveAperture) :
    (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) ≠ 0 :=
  (Classical.choose_spec (ccmRestrictedWeilOperator_exists_groundEigenstate a)).1

theorem ccmRestrictedWeilCanonicalGroundEigenstate_eigen
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilOperator a (ccmRestrictedWeilCanonicalGroundEigenstate a) =
      (ccmRestrictedWeilGroundEnergy a : ℂ) •
        (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) :=
  (Classical.choose_spec (ccmRestrictedWeilOperator_exists_groundEigenstate a)).2

noncomputable def ccmRestrictedWeilCanonicalGroundFormLift
    (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  Classical.choose (ccmRestrictedWeilOperator_exists_completeFormLift_mixed a
    (ccmRestrictedWeilCanonicalGroundEigenstate a))

theorem ccmRestrictedWeilCanonicalGroundFormLift_embedding
    (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilCanonicalGroundFormLift a) =
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) :=
  (Classical.choose_spec (ccmRestrictedWeilOperator_exists_completeFormLift_mixed a
    (ccmRestrictedWeilCanonicalGroundEigenstate a))).1

theorem ccmRestrictedWeilCanonicalGroundFormLift_mixed
    (a : SuzukiPositiveAperture) (v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (ccmRestrictedWeilCanonicalGroundFormLift a) v =
      inner ℂ
        ((ccmRestrictedWeilGroundEnergy a : ℂ) •
          (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a))
        (ccmArchimedeanFormToAperture a v) := by
  rw [← ccmRestrictedWeilCanonicalGroundEigenstate_eigen a]
  exact (Classical.choose_spec
    (ccmRestrictedWeilOperator_exists_completeFormLift_mixed a
      (ccmRestrictedWeilCanonicalGroundEigenstate a))).2 v

/-- Exact source-faithful ground equation: the complete-form ground is the adjoint Gamma
resolvent applied to the signed scalar--polar--prime forcing. -/
theorem ccmRestrictedWeilCanonicalGroundFormLift_eq_adjoint_primePolarForcing
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilCanonicalGroundFormLift a =
      (ccmArchimedeanFormToAperture a).adjoint
        (((ccmRestrictedWeilGroundEnergy a : ℂ) -
              ccmArchimedeanRemainderScalar) •
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a) -
          ccmPolarOperator a
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a) +
          ccmFinitePrimeOperator a
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a)) := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hmixed := ccmRestrictedWeilCanonicalGroundFormLift_mixed a v
  unfold ccmRestrictedWeilForm at hmixed
  rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding] at hmixed
  unfold ccmRestrictedWeilBoundedRemainder at hmixed
  change inner ℂ (ccmRestrictedWeilCanonicalGroundFormLift a) v +
      inner ℂ
        (ccmArchimedeanRemainderScalar •
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a) +
          ccmPolarOperator a
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a) -
          ccmFinitePrimeOperator a
            (ccmRestrictedWeilCanonicalGroundEigenstate a :
              suzukiApertureHilbert a))
        (ccmArchimedeanFormToAperture a v) =
      inner ℂ
        ((ccmRestrictedWeilGroundEnergy a : ℂ) •
          (ccmRestrictedWeilCanonicalGroundEigenstate a :
            suzukiApertureHilbert a))
        (ccmArchimedeanFormToAperture a v) at hmixed
  simp only [inner_sub_left, inner_add_left] at hmixed
  rw [inner_smul_left
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
      (ccmArchimedeanFormToAperture a v) ccmArchimedeanRemainderScalar,
    inner_smul_left
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
      (ccmArchimedeanFormToAperture a v)
      (ccmRestrictedWeilGroundEnergy a : ℂ)] at hmixed
  rw [star_ccmArchimedeanRemainderScalar, Complex.conj_ofReal] at hmixed
  change inner ℂ (ccmRestrictedWeilCanonicalGroundFormLift a) v = _
  simp only [inner_sub_left, inner_add_left]
  rw [inner_smul_left
    (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a)
    (ccmArchimedeanFormToAperture a v)
    ((ccmRestrictedWeilGroundEnergy a : ℂ) - ccmArchimedeanRemainderScalar)]
  rw [map_sub, Complex.conj_ofReal, star_ccmArchimedeanRemainderScalar]
  linear_combination hmixed

/-! ## Actual compact Birman--Schwinger pencil -/

/-- Bounded source forcing at spectral parameter `E`. -/
def ccmRestrictedWeilBirmanSchwingerForcing
    (a : SuzukiPositiveAperture) (E : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (E : ℂ) • 1 - ccmRestrictedWeilBoundedRemainder a

/-- The source forcing keeps the scalar, polar, and finite-prime channels with their exact signs. -/
theorem ccmRestrictedWeilBirmanSchwingerForcing_eq_primePolar
    (a : SuzukiPositiveAperture) (E : ℝ) :
    ccmRestrictedWeilBirmanSchwingerForcing a E =
      ((E : ℂ) - ccmArchimedeanRemainderScalar) • 1 -
        ccmPolarOperator a + ccmFinitePrimeOperator a := by
  apply ContinuousLinearMap.ext
  intro x
  change (E : ℂ) • x -
      (ccmArchimedeanRemainderScalar • x + ccmPolarOperator a x -
        ccmFinitePrimeOperator a x) =
    ((E : ℂ) - ccmArchimedeanRemainderScalar) • x -
      ccmPolarOperator a x + ccmFinitePrimeOperator a x
  module

/-- Actual bounded Birman--Schwinger pencil for the restricted Weil operator. -/
def ccmRestrictedWeilBirmanSchwinger
    (a : SuzukiPositiveAperture) (E : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  formEmbeddingCovariance (ccmArchimedeanFormToAperture a) ∘L
    ccmRestrictedWeilBirmanSchwingerForcing a E

/-- The actual restricted-Weil Birman--Schwinger pencil is compact at every real energy. -/
theorem isCompactOperator_ccmRestrictedWeilBirmanSchwinger
    (a : SuzukiPositiveAperture) (E : ℝ) :
    IsCompactOperator (ccmRestrictedWeilBirmanSchwinger a E) := by
  exact (formEmbeddingCovariance_isCompact
    (ccmArchimedeanFormToAperture a)
    (isCompactOperator_ccmArchimedeanFormToAperture a)).comp_clm
      (ccmRestrictedWeilBirmanSchwingerForcing a E)

/-- **Actual Birman--Schwinger equivalence.** A real number is an eigenvalue of the exact
unbounded restricted-Weil operator at `x` exactly when the explicit compact scalar--polar--prime
pencil fixes `x`. -/
theorem ccmRestrictedWeil_eigen_iff_birmanSchwinger_fixed
    (a : SuzukiPositiveAperture) (E : ℝ)
    (x : suzukiApertureHilbert a) :
    (∃ hx : x ∈ (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨x, hx⟩ = (E : ℂ) • x) ↔
      ccmRestrictedWeilBirmanSchwinger a E x = x := by
  let J := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  let F := ccmRestrictedWeilBirmanSchwingerForcing a E
  constructor
  · rintro ⟨hx, heigen⟩
    let xd : (ccmRestrictedWeilOperator a).domain := ⟨x, hx⟩
    obtain ⟨u, huJ, hform⟩ :=
      ccmRestrictedWeilOperator_exists_completeFormLift_mixed a xd
    have huAdj : u = J.adjoint (F x) := by
      apply ext_inner_right ℂ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left]
      have hmixed := hform v
      rw [heigen] at hmixed
      unfold ccmRestrictedWeilForm at hmixed
      change inner ℂ u v + inner ℂ (B (J u)) (J v) =
        inner ℂ ((E : ℂ) • x) (J v) at hmixed
      rw [huJ] at hmixed
      change inner ℂ u v = inner ℂ (F x) (J v)
      change inner ℂ u v = inner ℂ ((E : ℂ) • x - B x) (J v)
      rw [inner_sub_left]
      linear_combination hmixed
    change formEmbeddingCovariance J (F x) = x
    change J (J.adjoint (F x)) = x
    rw [← huAdj, huJ]
  · intro hfixed
    let u : CCMArchimedeanFormDomain a := J.adjoint (F x)
    have huJ : J u = x := by
      change J (J.adjoint (F x)) = x
      exact hfixed
    have hrep : ∀ v : CCMArchimedeanFormDomain a,
        inner ℂ u v + inner ℂ (B (J u)) (J v) =
          inner ℂ ((E : ℂ) • x) (J v) := by
      intro v
      rw [huJ, ContinuousLinearMap.adjoint_inner_left]
      change inner ℂ (F x) (J v) + inner ℂ (B x) (J v) = _
      change inner ℂ ((E : ℂ) • x - B x) (J v) +
          inner ℂ (B x) (J v) = _
      rw [inner_sub_left]
      ring
    obtain ⟨hmem, happ⟩ :=
      boundedPerturbedFriedrichsOperator_mem_domain_of_represents
        J B (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
        (ccmArchimedeanFormToAperture_injective a)
        (denseRange_ccmArchimedeanFormToAperture a) u ((E : ℂ) • x) hrep
    have hmemActual : J u ∈ (ccmRestrictedWeilOperator a).domain := by
      simpa only [J, B, ccmRestrictedWeilOperator] using hmem
    have happActual :
        ccmRestrictedWeilOperator a ⟨J u, hmemActual⟩ = (E : ℂ) • x := by
      simpa only [J, B, ccmRestrictedWeilOperator] using happ
    have hxmem : x ∈ (ccmRestrictedWeilOperator a).domain := by
      rw [← huJ]
      exact hmemActual
    refine ⟨hxmem, ?_⟩
    have hdom : (⟨x, hxmem⟩ : (ccmRestrictedWeilOperator a).domain) =
        ⟨J u, hmemActual⟩ := Subtype.ext huJ.symm
    rw [hdom, happActual]

/-- The exact restricted-Weil ground is a nonzero fixed vector of the compact actual
Birman--Schwinger pencil at the ground energy. -/
theorem ccmRestrictedWeilCanonicalGround_birmanSchwinger_fixed
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilBirmanSchwinger a (ccmRestrictedWeilGroundEnergy a)
        (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) =
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) := by
  apply (ccmRestrictedWeil_eigen_iff_birmanSchwinger_fixed a
    (ccmRestrictedWeilGroundEnergy a)
    (ccmRestrictedWeilCanonicalGroundEigenstate a :
      suzukiApertureHilbert a)).mp
  exact ⟨(ccmRestrictedWeilCanonicalGroundEigenstate a).property,
    ccmRestrictedWeilCanonicalGroundEigenstate_eigen a⟩

/-! ## Self-adjoint form-domain pencil -/

/-- Compact Birman--Schwinger pencil on the complete archimedean form domain. -/
def ccmRestrictedWeilFormBirmanSchwinger
    (a : SuzukiPositiveAperture) (E : ℝ) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ccmRestrictedWeilBirmanSchwingerForcing a E ∘L
      ccmArchimedeanFormToAperture a

theorem ccmRestrictedWeilBirmanSchwingerForcing_isSelfAdjoint
    (a : SuzukiPositiveAperture) (E : ℝ) :
    IsSelfAdjoint (ccmRestrictedWeilBirmanSchwingerForcing a E) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmRestrictedWeilBirmanSchwingerForcing
  rw [ContinuousLinearMap.adjoint.map_sub,
    ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_one,
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).adjoint_eq]
  rw [Complex.conj_ofReal]

set_option maxHeartbeats 1000000 in
/-- The form-domain Birman--Schwinger pencil is self-adjoint at every real energy. -/
theorem ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint
    (a : SuzukiPositiveAperture) (E : ℝ) :
    IsSelfAdjoint (ccmRestrictedWeilFormBirmanSchwinger a E) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmRestrictedWeilFormBirmanSchwinger
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (ccmRestrictedWeilBirmanSchwingerForcing_isSelfAdjoint a E).adjoint_eq]
  rw [ContinuousLinearMap.comp_assoc]

/-- The form-domain Birman--Schwinger pencil is compact at every real energy. -/
theorem isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger
    (a : SuzukiPositiveAperture) (E : ℝ) :
    IsCompactOperator (ccmRestrictedWeilFormBirmanSchwinger a E) := by
  have hmid : IsCompactOperator
      (ccmRestrictedWeilBirmanSchwingerForcing a E ∘L
        ccmArchimedeanFormToAperture a) :=
    (isCompactOperator_ccmArchimedeanFormToAperture a).clm_comp
      (ccmRestrictedWeilBirmanSchwingerForcing a E)
  exact hmid.clm_comp (ccmArchimedeanFormToAperture a).adjoint

/-- Exact compatibility of ambient and complete-form Birman--Schwinger pencils. -/
theorem ccmRestrictedWeilBirmanSchwinger_embedding
    (a : SuzukiPositiveAperture) (E : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilBirmanSchwinger a E
        (ccmArchimedeanFormToAperture a u) =
      ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilFormBirmanSchwinger a E u) := rfl

/-- **Self-adjoint Birman--Schwinger equivalence.** Fixed form vectors of the compact
self-adjoint source pencil are exactly form representatives of exact restricted-Weil
eigenvectors. -/
theorem ccmRestrictedWeil_embedding_eigen_iff_formBirmanSchwinger_fixed
    (a : SuzukiPositiveAperture) (E : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    (∃ hmem : ccmArchimedeanFormToAperture a u ∈
          (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a
            ⟨ccmArchimedeanFormToAperture a u, hmem⟩ =
          (E : ℂ) • ccmArchimedeanFormToAperture a u) ↔
      ccmRestrictedWeilFormBirmanSchwinger a E u = u := by
  rw [ccmRestrictedWeil_eigen_iff_birmanSchwinger_fixed a E
    (ccmArchimedeanFormToAperture a u)]
  constructor
  · intro h
    apply ccmArchimedeanFormToAperture_injective a
    rw [← ccmRestrictedWeilBirmanSchwinger_embedding]
    exact h
  · intro h
    rw [ccmRestrictedWeilBirmanSchwinger_embedding, h]

set_option maxHeartbeats 1000000 in
/-- Exact affine spectral-flow law: changing energy moves the self-adjoint compact pencil only
along the positive form-embedding Gram direction. -/
theorem ccmRestrictedWeilFormBirmanSchwinger_sub
    (a : SuzukiPositiveAperture) (E₂ E₁ : ℝ) :
    ccmRestrictedWeilFormBirmanSchwinger a E₂ -
        ccmRestrictedWeilFormBirmanSchwinger a E₁ =
      ((E₂ - E₁ : ℝ) : ℂ) •
        ((ccmArchimedeanFormToAperture a).adjoint ∘L
          ccmArchimedeanFormToAperture a) := by
  apply ContinuousLinearMap.ext
  intro u
  change (ccmArchimedeanFormToAperture a).adjoint
      (((E₂ : ℂ) • ccmArchimedeanFormToAperture a u -
          ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))) -
    (ccmArchimedeanFormToAperture a).adjoint
      (((E₁ : ℂ) • ccmArchimedeanFormToAperture a u -
          ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))) = _
  rw [map_sub, map_sub, map_smul, map_smul]
  simp only [ContinuousLinearMap.comp_apply, smul_apply]
  push_cast
  module

/-- A unit increase of spectral energy adds exactly the positive form-embedding Gram operator. -/
theorem ccmRestrictedWeilFormBirmanSchwinger_unitStep_sub
    (a : SuzukiPositiveAperture) (E : ℝ) :
    ccmRestrictedWeilFormBirmanSchwinger a (E + 1) -
        ccmRestrictedWeilFormBirmanSchwinger a E =
      (ccmArchimedeanFormToAperture a).adjoint ∘L
        ccmArchimedeanFormToAperture a := by
  rw [ccmRestrictedWeilFormBirmanSchwinger_sub]
  norm_num

/-- The actual form-domain Birman--Schwinger pencil moves in a positive direction under every
unit energy increment. -/
theorem ccmRestrictedWeilFormBirmanSchwinger_unitStep_isPositive
    (a : SuzukiPositiveAperture) (E : ℝ) :
    (ccmRestrictedWeilFormBirmanSchwinger a (E + 1) -
      ccmRestrictedWeilFormBirmanSchwinger a E).IsPositive := by
  rw [ccmRestrictedWeilFormBirmanSchwinger_unitStep_sub]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (ccmArchimedeanFormToAperture a)

/-- The exact canonical ground form lift is a fixed vector of the compact self-adjoint pencil at
the true restricted-Weil ground energy. -/
theorem ccmRestrictedWeilCanonicalGroundFormLift_birmanSchwinger_fixed
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilFormBirmanSchwinger a
        (ccmRestrictedWeilGroundEnergy a)
        (ccmRestrictedWeilCanonicalGroundFormLift a) =
      ccmRestrictedWeilCanonicalGroundFormLift a := by
  apply (ccmRestrictedWeil_embedding_eigen_iff_formBirmanSchwinger_fixed a
    (ccmRestrictedWeilGroundEnergy a)
    (ccmRestrictedWeilCanonicalGroundFormLift a)).mp
  rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding]
  exact ⟨(ccmRestrictedWeilCanonicalGroundEigenstate a).property,
    ccmRestrictedWeilCanonicalGroundEigenstate_eigen a⟩

end RHTower
