import GaloisForLFunctions.RHTower.Suzuki.SuzukiFriedrichsExtension

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Primitive lift from zero-mean derivative coordinates to the exact complete Weil form domain. -/
def suzukiZeroMeanPrimitiveCCMFormCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] CCMArchimedeanFormDomain a :=
  (suzukiAperturePrimitiveCCMFormCLM a).comp
    (SuzukiApertureZeroMean a).subtypeL

@[simp]
theorem suzukiZeroMeanPrimitiveCCMFormCLM_apply
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    suzukiZeroMeanPrimitiveCCMFormCLM a f =
      suzukiAperturePrimitiveCCMFormVector a
        (f : SuzukiApertureIntervalL2 a.1) := rfl

/-- Suzuki's entire Dirichlet primitive range is dense in the exact Weil form domain. -/
theorem denseRange_suzukiZeroMeanPrimitiveCCMFormCLM
    (a : SuzukiPositiveAperture) :
    DenseRange (suzukiZeroMeanPrimitiveCCMFormCLM a) := by
  apply (denseRange_suzukiDirichletDomainCCMFormLift a).mono
  rintro y ⟨v, rfl⟩
  let f : SuzukiApertureZeroMean a :=
    (suzukiDirichletInverseRangeEquiv a).symm
      (suzukiDirichletDomainToH01 a v)
  refine ⟨f, ?_⟩
  rfl

/-- Strict-interior smooth functions are dense in the complete restricted-Weil form norm. -/
theorem denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector
    (a : SuzukiPositiveAperture) :
    DenseRange (fun u : CCMComplexSmoothInteriorSource a => u.toCCMFormVector) := by
  have hcomp : DenseRange (fun u : CCMComplexSmoothInteriorSource a =>
      suzukiZeroMeanPrimitiveCCMFormCLM a u.toDerivativeZeroMean) :=
    (denseRange_suzukiZeroMeanPrimitiveCCMFormCLM a).comp
      (denseRange_ccmComplexSmoothInteriorSource_toDerivativeZeroMean a)
      (suzukiZeroMeanPrimitiveCCMFormCLM a).continuous
  simpa only [suzukiZeroMeanPrimitiveCCMFormCLM_apply,
    CCMComplexSmoothInteriorSource.toCCMFormVector_eq_primitive] using hcomp

/-- The exact spectral floor is attained inside Suzuki's complete restricted-Weil form domain. -/
theorem exists_suzukiWeilGroundFormVector
    (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a,
      suzukiWeilIntervalFormEmbedding a u ≠ 0 ∧
        ccmRestrictedWeilSourceQuadratic a u =
          suzukiWeilIntervalGroundEnergy a *
            ‖suzukiWeilIntervalFormEmbedding a u‖ ^ 2 := by
  let J := suzukiWeilIntervalFormEmbedding a
  let B := suzukiWeilIntervalBoundedRemainder a
  let hB := suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a
  let C := boundedPerturbedFormCovariance J B hB
  let mu : ℝ := ‖C‖
  have hmu : 0 < mu := norm_suzukiWeilIntervalCovariance_pos a
  obtain ⟨e, hene, he⟩ :=
    boundedPerturbedFormCovariance_exists_norm_eigenvector
      J B hB
      (suzukiWeilIntervalFormEmbedding_injective a)
      (denseRange_suzukiWeilIntervalFormEmbedding a)
      (isCompactOperator_suzukiWeilIntervalFormEmbedding a)
  change C e = (mu : ℂ) • e at he
  let u : CCMArchimedeanFormDomain a :=
    boundedPerturbedFormRieszInv J B hB (J.adjoint e)
  have hR : boundedPerturbedFormRiesz J B u = J.adjoint e :=
    (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply (J.adjoint e)
  have hJu : J u = (mu : ℂ) • e := by
    change C e = (mu : ℂ) • e at he
    exact he
  have hJne : J u ≠ 0 := by
    rw [← norm_pos_iff, hJu, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hmu]
    exact mul_pos hmu (norm_pos_iff.mpr hene)
  refine ⟨u, hJne, ?_⟩
  have hRreal : (inner ℂ (boundedPerturbedFormRiesz J B u) u).re =
      mu * ‖e‖ ^ 2 := by
    rw [hR, J.adjoint_inner_left, hJu, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  have hRexpand : (inner ℂ (boundedPerturbedFormRiesz J B u) u).re =
      ccmRestrictedWeilSourceQuadratic a u +
        boundedPerturbedFormShift B * ‖J u‖ ^ 2 := by
    rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
      inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left]
    rw [← suzukiWeilIntervalForm_self_re_eq_source a u]
    rw [suzukiWeilIntervalForm]
    change (inner ℂ u u + inner ℂ (B (J u)) (J u) +
        (starRingEnd ℂ) (boundedPerturbedFormShift B : ℂ) *
          inner ℂ (J u) (J u)).re =
      (inner ℂ u u + inner ℂ (B (J u)) (J u)).re +
        boundedPerturbedFormShift B * ‖J u‖ ^ 2
    rw [Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  have hnorm : ‖J u‖ ^ 2 = mu ^ 2 * ‖e‖ ^ 2 := by
    rw [hJu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmu]
    ring
  unfold suzukiWeilIntervalGroundEnergy
  change ccmRestrictedWeilSourceQuadratic a u =
    (mu⁻¹ - boundedPerturbedFormShift B) * ‖J u‖ ^ 2
  rw [hRexpand] at hRreal
  rw [hnorm]
  have hmune : mu ≠ 0 := hmu.ne'
  calc
    ccmRestrictedWeilSourceQuadratic a u =
        mu * ‖e‖ ^ 2 -
          boundedPerturbedFormShift B * (mu ^ 2 * ‖e‖ ^ 2) := by
      rw [hnorm] at hRreal
      linarith
    _ = (mu⁻¹ - boundedPerturbedFormShift B) *
        (mu ^ 2 * ‖e‖ ^ 2) := by
      symm
      calc
        (mu⁻¹ - boundedPerturbedFormShift B) *
            (mu ^ 2 * ‖e‖ ^ 2) =
            ((mu⁻¹ * mu) * mu -
              boundedPerturbedFormShift B * mu ^ 2) * ‖e‖ ^ 2 := by
          ring
        _ = mu * ‖e‖ ^ 2 -
            boundedPerturbedFormShift B * (mu ^ 2 * ‖e‖ ^ 2) := by
          rw [inv_mul_cancel₀ hmune]
          ring

/-! ## Suzuki's exact smooth Rayleigh infimum -/

/-- Physical interval mass of a vector in Suzuki's complete Weil form domain. -/
def suzukiWeilIntervalFormMass (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  ‖suzukiWeilIntervalFormEmbedding a u‖ ^ 2

theorem continuous_suzukiWeilIntervalFormMass (a : SuzukiPositiveAperture) :
    Continuous (suzukiWeilIntervalFormMass a) := by
  unfold suzukiWeilIntervalFormMass
  fun_prop

/-- Rayleigh quotient of Suzuki's exact localized Weil form. -/
def suzukiWeilIntervalFormRayleigh (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u / suzukiWeilIntervalFormMass a u

theorem continuous_suzukiWeilIntervalSourceQuadratic
    (a : SuzukiPositiveAperture) :
    Continuous (ccmRestrictedWeilSourceQuadratic a) := by
  have heq : ccmRestrictedWeilSourceQuadratic a = fun u =>
      (suzukiWeilIntervalForm a u u).re := by
    funext u
    exact (suzukiWeilIntervalForm_self_re_eq_source a u).symm
  rw [heq]
  unfold suzukiWeilIntervalForm
  exact Complex.continuous_re.comp
    ((continuous_id.inner continuous_id).add
      (((suzukiWeilIntervalBoundedRemainder a).continuous.comp
          (suzukiWeilIntervalFormEmbedding a).continuous).inner
        (suzukiWeilIntervalFormEmbedding a).continuous))

theorem continuousAt_suzukiWeilIntervalFormRayleigh
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : suzukiWeilIntervalFormMass a u ≠ 0) :
    ContinuousAt (suzukiWeilIntervalFormRayleigh a) u := by
  unfold suzukiWeilIntervalFormRayleigh
  exact (continuous_suzukiWeilIntervalSourceQuadratic a).continuousAt.div
    (continuous_suzukiWeilIntervalFormMass a).continuousAt hu

/-- Rayleigh values on the literal strict-interior smooth source class
`C_c^∞(-a,a)`. -/
def suzukiSmoothInteriorRayleighSet (a : SuzukiPositiveAperture) : Set ℝ :=
  {r | ∃ u : CCMComplexSmoothInteriorSource a,
    suzukiWeilIntervalFormEmbedding a u.toCCMFormVector ≠ 0 ∧
      r = suzukiWeilIntervalFormRayleigh a u.toCCMFormVector}

/-- Suzuki 2026, Corollary 1.2: the lowest eigenvalue is exactly the greatest lower
bound of the Rayleigh quotient on `C_c^∞(-a,a)`. -/
theorem isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy
    (a : SuzukiPositiveAperture) :
    IsGLB (suzukiSmoothInteriorRayleighSet a)
      (suzukiWeilIntervalGroundEnergy a) := by
  constructor
  · rintro r ⟨v, hvJ, rfl⟩
    have hmass : 0 < suzukiWeilIntervalFormMass a v.toCCMFormVector := by
      unfold suzukiWeilIntervalFormMass
      exact pow_pos (norm_pos_iff.mpr hvJ) 2
    rw [suzukiWeilIntervalFormRayleigh, le_div_iff₀ hmass]
    exact suzukiWeilIntervalGroundEnergy_mul_formNorm_sq_le_source
      a v.toCCMFormVector
  · intro b hb
    obtain ⟨u, hJu, hground⟩ := exists_suzukiWeilGroundFormVector a
    have hmass : suzukiWeilIntervalFormMass a u ≠ 0 := by
      unfold suzukiWeilIntervalFormMass
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hJu)
    have hrayleigh : suzukiWeilIntervalFormRayleigh a u =
        suzukiWeilIntervalGroundEnergy a := by
      rw [suzukiWeilIntervalFormRayleigh, hground]
      exact mul_div_cancel_right₀ _ hmass
    have hcont : ContinuousAt (suzukiWeilIntervalFormRayleigh a) u :=
      continuousAt_suzukiWeilIntervalFormRayleigh a u hmass
    have hu : u ≠ 0 := by
      intro hu0
      rw [hu0, map_zero] at hJu
      exact hJu rfl
    refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
    have hrayNhds :
        {v | suzukiWeilIntervalFormRayleigh a v <
          suzukiWeilIntervalGroundEnergy a + epsilon} ∈ 𝓝 u := by
      have hIio : Iio (suzukiWeilIntervalGroundEnergy a + epsilon) ∈
          𝓝 (suzukiWeilIntervalFormRayleigh a u) := by
        rw [hrayleigh]
        exact Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)
      exact hcont hIio
    have hneNhds : ({0}ᶜ : Set (CCMArchimedeanFormDomain a)) ∈ 𝓝 u :=
      isOpen_compl_singleton.mem_nhds hu
    obtain ⟨v, hvRay, hvne⟩ :=
      (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds
        (inter_mem hrayNhds hneNhds)
    have hvJ : suzukiWeilIntervalFormEmbedding a v.toCCMFormVector ≠ 0 := by
      intro hvzero
      apply hvne
      apply suzukiWeilIntervalFormEmbedding_injective a
      simpa using hvzero
    change suzukiWeilIntervalFormRayleigh a v.toCCMFormVector <
      suzukiWeilIntervalGroundEnergy a + epsilon at hvRay
    exact (lt_of_le_of_lt (hb ⟨v, hvJ, rfl⟩) hvRay).le

/-- Infimum form of Suzuki 2026, Corollary 1.2. -/
theorem sInf_suzukiSmoothInteriorRayleighSet
    (a : SuzukiPositiveAperture) :
    sInf (suzukiSmoothInteriorRayleighSet a) =
      suzukiWeilIntervalGroundEnergy a := by
  obtain ⟨u, hJu, -⟩ := exists_suzukiWeilGroundFormVector a
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0, map_zero] at hJu
    exact hJu rfl
  obtain ⟨v, hvne⟩ :=
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds
      (isOpen_compl_singleton.mem_nhds hu)
  have hvJ : suzukiWeilIntervalFormEmbedding a v.toCCMFormVector ≠ 0 := by
    intro hvzero
    apply hvne
    apply suzukiWeilIntervalFormEmbedding_injective a
    simpa using hvzero
  exact (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy a).csInf_eq
    ⟨_, ⟨v, hvJ, rfl⟩⟩

/-! ## Literal `B_a` quotient on `C_c^∞(-a,a)` -/

/-- A strict-interior smooth source as an element of Suzuki's exact Dirichlet
derivative domain `H₀¹(-a,a)`. -/
def CCMComplexSmoothInteriorSource.toDirichletDerivativeDomain
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    (suzukiDirichletDerivative a).domain :=
  ⟨suzukiDirichletInverseCLM a u.toDerivativeZeroMean, by
    rw [suzukiDirichletDerivative_domain, SuzukiApertureH01]
    exact ⟨u.toDerivativeZeroMean, rfl⟩⟩

/-- The same strict source in the natural domain of `B_a = D† G_a D`. -/
def CCMComplexSmoothInteriorSource.toDirichletScrewDomain
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    (suzukiDirichletScrewOperator a).domain :=
  ⟨u.toDirichletDerivativeDomain, by
    rw [suzukiDirichletScrewOperator_domain,
      suzukiDirichletScrewNaturalDomain_eq_H01]
    exact u.toDirichletDerivativeDomain.property⟩

theorem CCMComplexSmoothInteriorSource.toDirichletDerivativeCoordinate
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    suzukiDirichletDomainDerivativeCoordinate a
        u.toDirichletDerivativeDomain =
      (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) := by
  apply suzukiAperturePrimitiveCLM_injective a
  change suzukiAperturePrimitive a.1
      (suzukiDirichletDomainDerivativeCoordinate a
        u.toDirichletDerivativeDomain) =
    suzukiAperturePrimitive a.1
      (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1)
  rw [suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate]
  rfl

/-- The physical vector represented by a strict source is simultaneously its
completed-form image and its literal Dirichlet primitive. -/
theorem CCMComplexSmoothInteriorSource.toDirichletScrewDomain_coe
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    (u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1) =
      suzukiWeilIntervalFormEmbedding a u.toCCMFormVector := by
  rw [u.toCCMFormVector_eq_primitive,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector]
  rfl

/-- On a literal strict smooth source, Suzuki's natural operator `B_a` has the
same exact Weil representative as its Friedrichs extension `A_a`. -/
theorem CCMComplexSmoothInteriorSource.suzukiDirichletScrewOperator_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    suzukiDirichletScrewOperator a u.toDirichletScrewDomain =
      suzukiAperturePrimitiveWeilRepresentative a
        (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) := by
  rw [suzukiDirichletScrewOperator_apply_eq_adjointWitness]
  change suzukiRawScrewAdjointWitness a
      (suzukiDirichletDomainDerivativeCoordinate a
        u.toDirichletDerivativeDomain) = _
  rw [u.toDirichletDerivativeCoordinate,
    suzukiRawScrewAdjointWitness_eq_primitiveWeilRepresentative]

/-- Exact diagonal identity `Q_W^a(v) = ⟨v, B_a v⟩` on the literal
`C_c^∞(-a,a)` class, in mathlib's conjugate-first inner-product convention. -/
theorem CCMComplexSmoothInteriorSource.inner_dirichletScrew_eq_weilForm
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    inner ℂ (u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1)
        (suzukiDirichletScrewOperator a u.toDirichletScrewDomain) =
      ccmRestrictedWeilForm a u.toCCMFormVector u.toCCMFormVector := by
  rw [u.suzukiDirichletScrewOperator_apply]
  change inner ℂ
      (suzukiDirichletInverseCLM a u.toDerivativeZeroMean)
      (suzukiAperturePrimitiveWeilRepresentative a
        (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1)) = _
  rw [inner_suzukiDirichletInverse_primitiveWeilRepresentative,
    u.toCCMFormVector_eq_primitive]

theorem CCMComplexSmoothInteriorSource.real_inner_dirichletScrew_eq_source
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    (inner ℂ (u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1)
        (suzukiDirichletScrewOperator a u.toDirichletScrewDomain)).re =
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  rw [u.inner_dirichletScrew_eq_weilForm,
    ccmRestrictedWeilForm_self_re_eq_source]

/-- Literal `B_a`-Rayleigh values on `C_c^∞(-a,a)`. -/
def suzukiDirichletSmoothRayleighSet (a : SuzukiPositiveAperture) : Set ℝ :=
  {r | ∃ u : CCMComplexSmoothInteriorSource a,
    (u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1) ≠ 0 ∧
      r =
        (inner ℂ (u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1)
          (suzukiDirichletScrewOperator a u.toDirichletScrewDomain)).re /
            ‖(u.toDirichletScrewDomain : SuzukiApertureIntervalL2 a.1)‖ ^ 2}

theorem suzukiDirichletSmoothRayleighSet_eq_formRayleighSet
    (a : SuzukiPositiveAperture) :
    suzukiDirichletSmoothRayleighSet a =
      suzukiSmoothInteriorRayleighSet a := by
  ext r
  constructor
  · rintro ⟨u, hune, rfl⟩
    refine ⟨u, ?_, ?_⟩
    · rwa [← u.toDirichletScrewDomain_coe]
    · unfold suzukiWeilIntervalFormRayleigh suzukiWeilIntervalFormMass
      rw [← u.real_inner_dirichletScrew_eq_source,
        ← u.toDirichletScrewDomain_coe]
  · rintro ⟨u, huJ, rfl⟩
    refine ⟨u, ?_, ?_⟩
    · rwa [u.toDirichletScrewDomain_coe]
    · unfold suzukiWeilIntervalFormRayleigh suzukiWeilIntervalFormMass
      rw [← u.real_inner_dirichletScrew_eq_source,
        ← u.toDirichletScrewDomain_coe]

/-- Literal operator statement of Suzuki 2026, Corollary 1.2: `lambda_a` is the
infimum of the `B_a` Rayleigh quotient over `C_c^∞(-a,a)`. -/
theorem sInf_suzukiDirichletSmoothRayleighSet
    (a : SuzukiPositiveAperture) :
    sInf (suzukiDirichletSmoothRayleighSet a) =
      suzukiWeilIntervalGroundEnergy a := by
  rw [suzukiDirichletSmoothRayleighSet_eq_formRayleighSet]
  exact sInf_suzukiSmoothInteriorRayleighSet a

/-- Strong form of Corollary 1.2's closure clause: the form-norm closure of the
literal `C_c^∞(-a,a)` source image is the entire completed Weil form domain. -/
theorem closure_range_ccmComplexSmoothInteriorSource_toCCMFormVector
    (a : SuzukiPositiveAperture) :
    closure (Set.range
      (fun u : CCMComplexSmoothInteriorSource a => u.toCCMFormVector)) =
      Set.univ :=
  (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).closure_eq

end RHTower
