import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMExactSourceIdentification
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilFriedrichsOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLimitingLogFormCoercivity

/-!
# Suzuki's limiting logarithmic operator

This module constructs the closed self-adjoint operator `T` used in Suzuki (2026), Theorem 1.4.
Its complete form domain is the exact `H^log`/CCM archimedean domain on `(-1,1)`.  The bounded
correction removes the finite-prime block and the smooth origin remainder and applies Suzuki's
scalar renormalization.  On every strict real source-core vector, the resulting closed form is
proved equal to the literal Hadamard finite-part block, hence to Suzuki's Eq. (404).

The construction also proves compact resolvent and attainment of the bottom spectral value by a
nonzero eigenstate.  All kernels and transports are explicit; no comparison-form premise or
spectral hypothesis is introduced.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiLimitingUnitAperture : SuzukiPositiveAperture := ⟨1, one_pos⟩

noncomputable instance instNontrivialSuzukiLimitingUnitInterval :
    Nontrivial (SuzukiApertureIntervalL2 1) := by
  simpa only [suzukiLimitingUnitAperture] using
    instNontrivialSuzukiApertureIntervalL2 suzukiLimitingUnitAperture

/-- Unit-aperture form embedding with literal endpoint type exposed to elaboration. -/
def suzukiLimitingLogFormEmbedding :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture →L[ℂ]
      SuzukiApertureIntervalL2 1 :=
  suzukiWeilIntervalFormEmbedding suzukiLimitingUnitAperture

theorem suzukiLimitingLogFormEmbedding_injective :
    Function.Injective suzukiLimitingLogFormEmbedding := by
  exact suzukiWeilIntervalFormEmbedding_injective suzukiLimitingUnitAperture

theorem denseRange_suzukiLimitingLogFormEmbedding :
    DenseRange suzukiLimitingLogFormEmbedding := by
  exact denseRange_suzukiWeilIntervalFormEmbedding suzukiLimitingUnitAperture

theorem isCompactOperator_suzukiLimitingLogFormEmbedding :
    IsCompactOperator suzukiLimitingLogFormEmbedding := by
  exact isCompactOperator_suzukiWeilIntervalFormEmbedding suzukiLimitingUnitAperture

/-- Continuous complex kernel of Suzuki's smooth origin remainder on the unit aperture. -/
def suzukiLimitingOriginKernel :
    C(SuzukiApertureInterval 1 × SuzukiApertureInterval 1, ℂ) where
  toFun z := (suzukiOriginRemainderCurvature ((z.1 : ℝ) - (z.2 : ℝ)) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (continuous_suzukiOriginRemainderCurvature.comp
      ((continuous_subtype_val.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd)))

def suzukiLimitingOriginKernelSection :
    C(SuzukiApertureInterval 1, SuzukiApertureIntervalL2 1) where
  toFun x := ContinuousMap.toLp 2 volume ℂ (suzukiLimitingOriginKernel.curry x)
  continuous_toFun :=
    (ContinuousMap.toLp 2 volume ℂ).continuous.comp
      suzukiLimitingOriginKernel.curry.continuous

def suzukiLimitingOriginKernelFunctional :
    C(SuzukiApertureInterval 1,
      SuzukiApertureIntervalL2 1 →L[ℂ] ℂ) where
  toFun x := InnerProductSpace.toDual ℂ (SuzukiApertureIntervalL2 1)
    (suzukiLimitingOriginKernelSection x)
  continuous_toFun :=
    (InnerProductSpace.toDual ℂ (SuzukiApertureIntervalL2 1)).continuous.comp
      suzukiLimitingOriginKernelSection.continuous

def suzukiLimitingOriginKernelField :
    Lp (SuzukiApertureIntervalL2 1 →L[ℂ] ℂ) 2
      (volume : Measure (SuzukiApertureInterval 1)) :=
  ContinuousMap.toLp 2 volume ℂ suzukiLimitingOriginKernelFunctional

/-- Bounded integral operator of the smooth origin-remainder kernel. -/
def suzukiLimitingOriginKernelOperatorRaw :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  kernelOperator (volume : Measure (SuzukiApertureInterval 1))
    suzukiLimitingOriginKernelField

theorem suzukiLimitingOriginKernelOperatorRaw_coeFn
    (f : SuzukiApertureIntervalL2 1) :
    (suzukiLimitingOriginKernelOperatorRaw f : SuzukiApertureInterval 1 → ℂ)
      =ᵐ[volume] fun x => ∫ y : SuzukiApertureInterval 1,
        (suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) : ℂ) * f y := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := SuzukiApertureIntervalL2 1)).coeFn_holder
      (r := (2 : ENNReal)) suzukiLimitingOriginKernelField
      (Lp.const ∞ (volume : Measure (SuzukiApertureInterval 1)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (SuzukiApertureInterval 1)))
      suzukiLimitingOriginKernelFunctional,
    Lp.coeFn_const (p := ∞) (volume : Measure (SuzukiApertureInterval 1)) f
  ] with x hholder hfield hconst
  rw [suzukiLimitingOriginKernelOperatorRaw, kernelOperator,
    kernelOperatorMap_apply, hholder, suzukiLimitingOriginKernelField,
    hfield, hconst]
  change inner ℂ (suzukiLimitingOriginKernelSection x) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (SuzukiApertureInterval 1)))
    (suzukiLimitingOriginKernel.curry x)] with y hy
  change inner ℂ
    (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiLimitingOriginKernel.curry x) : SuzukiApertureIntervalL2 1) y)
      (f y) = _
  rw [hy]
  simp [suzukiLimitingOriginKernel, RCLike.inner_apply]
  ring

/-- Canonically self-adjoint smooth origin-remainder operator. -/
def suzukiLimitingOriginKernelOperator :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  (1 / 2 : ℂ) • (suzukiLimitingOriginKernelOperatorRaw +
    ContinuousLinearMap.adjoint suzukiLimitingOriginKernelOperatorRaw)

theorem suzukiLimitingOriginKernelOperator_isSelfAdjoint :
    IsSelfAdjoint suzukiLimitingOriginKernelOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold suzukiLimitingOriginKernelOperator
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint.map_add,
    ContinuousLinearMap.adjoint_adjoint]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    apply Complex.ext <;> norm_num]
  congr 1
  abel

/-- Polar operator transported from the physical aperture to literal interval coordinates. -/
def suzukiLimitingIntervalPolarOperator :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  suzukiPhysicalToApertureCLM suzukiLimitingUnitAperture ∘L
    ccmPolarOperator suzukiLimitingUnitAperture ∘L
      suzukiApertureToPhysicalCLM suzukiLimitingUnitAperture

theorem suzukiLimitingIntervalPolarOperator_isSelfAdjoint :
    IsSelfAdjoint suzukiLimitingIntervalPolarOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have hp := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ccmPolarOperator_isSelfAdjoint suzukiLimitingUnitAperture)
  intro f g
  let e : SuzukiApertureIntervalL2 1 ≃ₗᵢ[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture :=
    suzukiApertureL2Equiv suzukiLimitingUnitAperture
  change inner ℂ (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e f))) g =
    inner ℂ f (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e g)))
  calc
    inner ℂ (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e f))) g =
        inner ℂ (ccmPolarOperator suzukiLimitingUnitAperture (e f)) (e g) := by
          simpa using e.symm.inner_map_map
            (ccmPolarOperator suzukiLimitingUnitAperture (e f)) (e g)
    _ = inner ℂ (e f) (ccmPolarOperator suzukiLimitingUnitAperture (e g)) :=
      hp (e f) (e g)
    _ = inner ℂ f (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e g))) := by
      calc
        inner ℂ (e f) (ccmPolarOperator suzukiLimitingUnitAperture (e g)) =
            inner ℂ (e.symm (e f))
              (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e g))) :=
          (e.symm.inner_map_map (e f)
            (ccmPolarOperator suzukiLimitingUnitAperture (e g))).symm
        _ = _ := congrArg
          (fun z => inner ℂ z
            (e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e g))))
          (e.symm_apply_apply f)

/-- Finite-prime operator transported to literal unit-interval coordinates. -/
def suzukiLimitingIntervalPrimeOperator :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  suzukiPhysicalToApertureCLM suzukiLimitingUnitAperture ∘L
    ccmFinitePrimeOperator suzukiLimitingUnitAperture ∘L
      suzukiApertureToPhysicalCLM suzukiLimitingUnitAperture

def suzukiLimitingScalar : ℂ :=
  ccmArchimedeanRemainderScalar +
    ((2 * suzukiWeilArchimedeanConstant + 1 : ℝ) : ℂ)

theorem star_suzukiLimitingScalar :
    (starRingEnd ℂ) suzukiLimitingScalar = suzukiLimitingScalar := by
  unfold suzukiLimitingScalar ccmArchimedeanRemainderScalar
  apply Complex.ext <;> simp

/-- Exact bounded correction whose closed form is Suzuki's limiting finite-part form. -/
def suzukiLimitingLogBoundedRemainder :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  suzukiLimitingScalar • 1 + suzukiLimitingIntervalPolarOperator +
    suzukiLimitingOriginKernelOperator

theorem suzukiLimitingLogBoundedRemainder_isSelfAdjoint :
    IsSelfAdjoint suzukiLimitingLogBoundedRemainder := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold suzukiLimitingLogBoundedRemainder
  rw [ContinuousLinearMap.adjoint.map_add,
    ContinuousLinearMap.adjoint.map_add,
    ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_one,
    (suzukiLimitingIntervalPolarOperator_isSelfAdjoint).adjoint_eq,
    (suzukiLimitingOriginKernelOperator_isSelfAdjoint).adjoint_eq,
    star_suzukiLimitingScalar]

/-- Closed sesquilinear form of Suzuki's limiting finite-part energy. -/
def suzukiLimitingLogClosedForm
    (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) : ℂ :=
  inner ℂ u v +
    inner ℂ
      (suzukiLimitingLogBoundedRemainder
        (suzukiLimitingLogFormEmbedding u))
      (suzukiLimitingLogFormEmbedding v)

/-- Closed limiting operator `T` in Suzuki (2026), Theorem 1.4. -/
def suzukiLimitingLogOperator :
    SuzukiApertureIntervalL2 1 →ₗ.[ℂ] SuzukiApertureIntervalL2 1 :=
  boundedPerturbedFriedrichsOperator
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint

theorem suzukiLimitingLogOperator_isSelfAdjoint :
    IsSelfAdjoint suzukiLimitingLogOperator := by
  exact boundedPerturbedFriedrichsOperator_isSelfAdjoint
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding

theorem suzukiLimitingLogOperator_hasCompactResolvent :
    LinearPMap.HasCompactResolventAt suzukiLimitingLogOperator
      (-(boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder : ℂ)) := by
  exact boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding
    isCompactOperator_suzukiLimitingLogFormEmbedding

/-- Compact positive covariance of Suzuki's limiting logarithmic form. -/
def suzukiLimitingLogCovariance :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  boundedPerturbedFormCovariance
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint

theorem suzukiLimitingLogCovariance_injective :
    Function.Injective suzukiLimitingLogCovariance := by
  exact boundedPerturbedFormCovariance_injective
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding

theorem suzukiLimitingLogCovariance_isCompact :
    IsCompactOperator suzukiLimitingLogCovariance := by
  exact boundedPerturbedFormCovariance_isCompact
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    isCompactOperator_suzukiLimitingLogFormEmbedding

theorem norm_suzukiLimitingLogCovariance_pos :
    0 < ‖suzukiLimitingLogCovariance‖ := by
  apply (norm_pos_iff (E := SuzukiApertureIntervalL2 1 →L[ℂ]
    SuzukiApertureIntervalL2 1)).mpr
  intro hzero
  obtain ⟨z, hz⟩ := exists_ne (0 : SuzukiApertureIntervalL2 1)
  apply hz
  apply suzukiLimitingLogCovariance_injective
  simp [hzero]

/-- Bottom spectral value of Suzuki's limiting operator. -/
def suzukiLimitingLogOperatorGroundEnergy : ℝ :=
  ‖suzukiLimitingLogCovariance‖⁻¹ -
    boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder

/-- Suzuki's limiting logarithmic ground value is attained by a genuine nonzero eigenstate. -/
theorem suzukiLimitingLogOperator_exists_groundEigenstate :
    ∃ x : suzukiLimitingLogOperator.domain,
      (x : SuzukiApertureIntervalL2 1) ≠ 0 ∧
        suzukiLimitingLogOperator x =
          (suzukiLimitingLogOperatorGroundEnergy : ℂ) •
            (x : SuzukiApertureIntervalL2 1) := by
  let C := suzukiLimitingLogCovariance
  let mu : ℝ := ‖C‖
  have hCinj : Function.Injective C := suzukiLimitingLogCovariance_injective
  have hmu : 0 < mu := norm_suzukiLimitingLogCovariance_pos
  obtain ⟨e, hene, he⟩ :=
    boundedPerturbedFormCovariance_exists_norm_eigenvector
      suzukiLimitingLogFormEmbedding
      suzukiLimitingLogBoundedRemainder
      suzukiLimitingLogBoundedRemainder_isSelfAdjoint
      suzukiLimitingLogFormEmbedding_injective
      denseRange_suzukiLimitingLogFormEmbedding
      isCompactOperator_suzukiLimitingLogFormEmbedding
  change C e = (mu : ℂ) • e at he
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
  let z : SuzukiApertureIntervalL2 1 := (mu : ℂ)⁻¹ • e
  have hCz : C z = e := by
    change C ((mu : ℂ)⁻¹ • e) = e
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
  have hedom : e ∈ (closedDenseInverse C).domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hCz⟩
  let x : suzukiLimitingLogOperator.domain :=
    ⟨e, by
      change e ∈ (closedDenseInverse C).domain
      exact hedom⟩
  refine ⟨x, hene, ?_⟩
  have hinvZ := (closedDenseInverse_apply_C C hCinj z).2
  have hinv : closedDenseInverse C ⟨e, hedom⟩ = z := by
    let Cz : (closedDenseInverse C).domain :=
      ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩
    have heq : (⟨e, hedom⟩ : (closedDenseInverse C).domain) = Cz :=
      Subtype.ext hCz.symm
    rw [heq]
    exact hinvZ
  change boundedPerturbedFriedrichsOperator
      suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder
        suzukiLimitingLogBoundedRemainder_isSelfAdjoint x = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  change closedDenseInverse C ⟨e, hedom⟩ -
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder : ℂ) • e =
    (suzukiLimitingLogOperatorGroundEnergy : ℂ) • e
  rw [hinv]
  change (mu : ℂ)⁻¹ • e -
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder : ℂ) • e = _
  unfold suzukiLimitingLogOperatorGroundEnergy
  dsimp only [C, mu]
  push_cast
  module

/-- Literal interval representative of a real unit-aperture source core. -/
def suzukiLimitingCoreIntervalVector
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    SuzukiApertureIntervalL2 1 :=
  suzukiApertureRestrictL2 1
    (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) : SoninL2)

theorem suzukiLimitingCoreIntervalVector_coeFn
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (suzukiLimitingCoreIntervalVector u : SuzukiApertureInterval 1 → ℂ)
      =ᵐ[volume] fun x => (u (x : ℝ) : ℂ) := by
  let F : SoninL2 := ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
    (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
  have hF : (F : ℝ → ℂ) =ᵐ[volume] fun x => (u x : ℂ) :=
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn
      suzukiLimitingUnitAperture u
  have hFsub : (fun x : SuzukiApertureInterval 1 => F (x : ℝ)) =ᵐ[volume]
      fun x => (u (x : ℝ) : ℂ) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae hF)
  filter_upwards [suzukiApertureRestrictL2_coeFn 1 F,
    suzukiApertureRestrictRepresentative_ae 1 F, hFsub] with x hres hrep hcore
  rw [suzukiLimitingCoreIntervalVector]
  rw [hres, hrep, hcore]

theorem suzukiLimitingCoreIntervalVector_eq_formEmbedding
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiLimitingCoreIntervalVector u =
      suzukiWeilIntervalFormEmbedding suzukiLimitingUnitAperture
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) := by
  let e := suzukiApertureL2Equiv suzukiLimitingUnitAperture
  apply e.injective
  change e (suzukiLimitingCoreIntervalVector u) =
    e (e.symm (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)))
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact suzukiApertureZeroExtendL2_restrict_eq suzukiLimitingUnitAperture
    (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u))

theorem suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiLimitingCoreIntervalVector u =
      suzukiLimitingLogFormEmbedding
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) :=
  suzukiLimitingCoreIntervalVector_eq_formEmbedding u

private theorem integral_subtype_Icc_eq_intervalIntegral_complex
    {b c : ℝ} (hbc : b ≤ c) (F : ℝ → ℂ) :
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) = ∫ x in b..c, F x := by
  calc
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) =
        ∫ x in Set.Icc b c, F x :=
      MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Set.Ioc b c, F x := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in b..c, F x := by rw [intervalIntegral.integral_of_le hbc]

private theorem integral_subtype_Icc_eq_intervalIntegral_real
    {b c : ℝ} (hbc : b ≤ c) (F : ℝ → ℝ) :
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) = ∫ x in b..c, F x := by
  calc
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) =
        ∫ x in Set.Icc b c, F x :=
      MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Set.Ioc b c, F x := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in b..c, F x := by rw [intervalIntegral.integral_of_le hbc]

theorem inner_suzukiLimitingOriginKernelOperatorRaw_core
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiLimitingOriginKernelOperatorRaw
          (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector u) =
      ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) := by
  let f := suzukiLimitingCoreIntervalVector u
  have hf : (f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (u (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn u
  have hop := suzukiLimitingOriginKernelOperatorRaw_coeFn f
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1,
        inner ℂ (suzukiLimitingOriginKernelOperatorRaw f x) (f x)) =
        ∫ x : SuzukiApertureInterval 1,
          (((∫ y : SuzukiApertureInterval 1,
              suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ)) * u (x : ℝ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hop, hf] with x hx hfx
      rw [hx, hfx]
      have hinner :
          (∫ y : SuzukiApertureInterval 1,
              (suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) : ℂ) * f y) =
            ((∫ y : SuzukiApertureInterval 1,
              suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) * u (y : ℝ) : ℝ) : ℂ) := by
        calc
          _ = ∫ y : SuzukiApertureInterval 1,
              ((suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ) : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards [hf] with y hfy
            rw [hfy]
            push_cast
            rfl
          _ = _ := integral_ofReal
      rw [hinner]
      simp [RCLike.inner_apply]
      ring
    _ = (((∫ x : SuzukiApertureInterval 1,
          (∫ y : SuzukiApertureInterval 1,
              suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ)) * u (x : ℝ) : ℝ)) : ℂ) := integral_ofReal
    _ = ((∫ x in (-1 : ℝ)..1,
          (∫ y in (-1 : ℝ)..1,
              suzukiOriginRemainderCurvature (x - y) * u y) * u x : ℝ) : ℂ) := by
      congr 1
      calc
        (∫ x : SuzukiApertureInterval 1,
            (∫ y : SuzukiApertureInterval 1,
                suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                  u (y : ℝ)) * u (x : ℝ)) =
            ∫ x in (-1 : ℝ)..1,
              (∫ y : SuzukiApertureInterval 1,
                suzukiOriginRemainderCurvature (x - (y : ℝ)) * u (y : ℝ)) * u x :=
          by
            simpa only [SuzukiApertureInterval] using
              (integral_subtype_Icc_eq_intervalIntegral_real
                (b := (-1 : ℝ)) (c := 1) (by norm_num)
                (fun x =>
                  (∫ y : Set.Icc (-1 : ℝ) 1,
                    suzukiOriginRemainderCurvature (x - (y : ℝ)) * u (y : ℝ)) * u x))
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x _
          exact congrArg (fun z : ℝ => z * u x)
            (integral_subtype_Icc_eq_intervalIntegral_real
              (b := (-1 : ℝ)) (c := 1) (by norm_num)
              (fun y => suzukiOriginRemainderCurvature (x - y) * u y))
    _ = ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) := by
      unfold weilSmoothBlock
      ring

theorem inner_suzukiLimitingOriginKernelOperator_core
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiLimitingOriginKernelOperator
          (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector u) =
      ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) := by
  let f := suzukiLimitingCoreIntervalVector u
  have hraw :
      inner ℂ (suzukiLimitingOriginKernelOperatorRaw f) f =
        ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) :=
    inner_suzukiLimitingOriginKernelOperatorRaw_core u
  have hadj :
      inner ℂ (ContinuousLinearMap.adjoint
          suzukiLimitingOriginKernelOperatorRaw f) f =
        ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    calc
      inner ℂ f (suzukiLimitingOriginKernelOperatorRaw f) =
          (starRingEnd ℂ)
            (inner ℂ (suzukiLimitingOriginKernelOperatorRaw f) f) :=
        (inner_conj_symm f (suzukiLimitingOriginKernelOperatorRaw f)).symm
      _ = _ := by rw [hraw]; simp
  unfold suzukiLimitingOriginKernelOperator
  rw [smul_apply, add_apply, inner_smul_left, inner_add_left, hraw, hadj]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    apply Complex.ext <;> norm_num]
  push_cast
  ring

theorem inner_suzukiLimitingIntervalPrimeOperator_core
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiLimitingIntervalPrimeOperator
          (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector u) =
      ((-weilPrimeBlock (suzukiRestrictedWeilIndices 1) u u : ℝ) : ℂ) := by
  classical
  let a := suzukiLimitingUnitAperture
  let q := suzukiRestrictedWeilCoreCCMFormVector a u
  let F := ccmArchimedeanFormToAperture a q
  let e := suzukiApertureL2Equiv a
  have hf : suzukiLimitingCoreIntervalVector u = e.symm F := by
    exact suzukiLimitingCoreIntervalVector_eq_formEmbedding u
  rw [hf]
  change inner ℂ (e.symm (ccmFinitePrimeOperator a (e (e.symm F)))) (e.symm F) = _
  rw [e.apply_symm_apply, e.symm.inner_map_map]
  rw [inner_ccmFinitePrimeOperator]
  have hblock :
      ((-weilPrimeBlock (suzukiRestrictedWeilIndices 1) u u : ℝ) : ℂ) =
        ((2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          criticalMellinAtomWeight n *
            suzukiCoreAutocorrelation u (Real.log n) : ℝ) : ℂ) := by
    have h := weilPrimeBlock_suzukiRestrictedWeilIndices_eq_autocorrelation a u
    dsimp only [a, suzukiLimitingUnitAperture] at h ⊢
    rw [h]
    push_cast
    ring
  rw [hblock]
  simp_rw [inner_ccmPrimeTransportOperator]
  dsimp only [F, q]
  simp_rw [inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector]
  simp_rw [apertureAutocorrelation_suzukiRestrictedWeilCore_eq]
  simp_rw [GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation_neg]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have hnmem := Finset.mem_Icc.mp hn
    omega
  rw [criticalMellinAtomWeight_eq_primePairWeight hnpos]
  unfold GaloisForLFunctions.HTGeometry.primePairWeight
  push_cast
  rw [← two_mul]
  ring_nf
  norm_num
  exact Or.inl rfl

theorem inner_suzukiLimitingCoreIntervalVector_self
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ (suzukiLimitingCoreIntervalVector u)
        (suzukiLimitingCoreIntervalVector u) =
      (suzukiCoreAutocorrelation u 0 : ℂ) := by
  let f := suzukiLimitingCoreIntervalVector u
  have hf : (f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (u (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn u
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1, inner ℂ (f x) (f x)) =
        ∫ x : SuzukiApertureInterval 1, ((u (x : ℝ) ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
      simp only [inner_self_eq_norm_sq_to_K]
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        ((|u (x : ℝ)| : ℝ) : ℂ) ^ 2 =
            ((|u (x : ℝ)| ^ 2 : ℝ) : ℂ) :=
          (Complex.ofReal_pow _ 2).symm
        _ = ((u (x : ℝ) ^ 2 : ℝ) : ℂ) :=
          congrArg (fun z : ℝ => (z : ℂ)) (sq_abs (u (x : ℝ)))
    _ = ((∫ x : SuzukiApertureInterval 1, u (x : ℝ) ^ 2 : ℝ) : ℂ) :=
      integral_ofReal
    _ = ((∫ x in (-1 : ℝ)..1, u x ^ 2 : ℝ) : ℂ) := by
      congr 1
      simpa only [SuzukiApertureInterval] using
        (integral_subtype_Icc_eq_intervalIntegral_real
          (b := (-1 : ℝ)) (c := 1) (by norm_num) (fun x => u x ^ 2))
    _ = (suzukiCoreAutocorrelation u 0 : ℂ) := by
      have h :=
        integral_interval_sq_suzukiRestrictedWeilCore_eq_autocorrelation_zero
          suzukiLimitingUnitAperture u
      dsimp only [suzukiLimitingUnitAperture] at h
      exact congrArg (fun z : ℝ => (z : ℂ)) h

theorem inner_suzukiLimitingLogBoundedRemainder_eq_intervalWeil_add_corrections
    (f : SuzukiApertureIntervalL2 1) :
    inner ℂ (suzukiLimitingLogBoundedRemainder f) f =
      inner ℂ
          (suzukiWeilIntervalBoundedRemainder suzukiLimitingUnitAperture f) f +
        inner ℂ (suzukiLimitingIntervalPrimeOperator f) f +
        (((2 * suzukiWeilArchimedeanConstant + 1 : ℝ) : ℂ) * inner ℂ f f) +
        inner ℂ (suzukiLimitingOriginKernelOperator f) f := by
  let e : SuzukiApertureIntervalL2 1 ≃ₗᵢ[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture :=
    suzukiApertureL2Equiv suzukiLimitingUnitAperture
  have htransport (T : suzukiApertureHilbert suzukiLimitingUnitAperture →L[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture) :
      inner ℂ (e.symm (T (e f))) f = inner ℂ (T (e f)) (e f) := by
    calc
      inner ℂ (e.symm (T (e f))) f =
          inner ℂ (e.symm (T (e f))) (e.symm (e f)) := by
        rw [e.symm_apply_apply]
      _ = inner ℂ (T (e f)) (e f) := e.symm.inner_map_map _ _
  change inner ℂ
      (((suzukiLimitingScalar •
          (1 : SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1)) f +
        e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e f))) +
        suzukiLimitingOriginKernelOperator f) f =
      inner ℂ
          (e.symm (ccmRestrictedWeilBoundedRemainder
            suzukiLimitingUnitAperture (e f))) f +
        inner ℂ
          (e.symm (ccmFinitePrimeOperator suzukiLimitingUnitAperture (e f))) f +
        (((2 * suzukiWeilArchimedeanConstant + 1 : ℝ) : ℂ) * inner ℂ f f) +
        inner ℂ (suzukiLimitingOriginKernelOperator f) f
  rw [inner_add_left, inner_add_left, smul_apply, one_apply_eq_self,
    inner_smul_left, star_suzukiLimitingScalar,
    htransport (ccmPolarOperator suzukiLimitingUnitAperture),
    htransport (ccmRestrictedWeilBoundedRemainder suzukiLimitingUnitAperture),
    htransport (ccmFinitePrimeOperator suzukiLimitingUnitAperture),
    inner_ccmRestrictedWeilBoundedRemainder]
  rw [e.inner_map_map]
  unfold suzukiLimitingScalar
  ring

/-- On every literal Suzuki source-core vector, the closed limiting form is exactly the
finite-part logarithmic form from Suzuki (2026), Eq. (404). -/
theorem suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiLimitingLogClosedForm
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) =
      (weilFinitePartBlock 1 u u : ℂ) := by
  let q := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u
  let f := suzukiLimitingCoreIntervalVector u
  have hf : f = suzukiLimitingLogFormEmbedding q :=
    suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding u
  have hfWeil : f =
      suzukiWeilIntervalFormEmbedding suzukiLimitingUnitAperture q :=
    suzukiLimitingCoreIntervalVector_eq_formEmbedding u
  have hfull : suzukiWeilIntervalForm suzukiLimitingUnitAperture q q =
      (suzukiRestrictedWeilForm 1 u u : ℂ) := by
    rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
    exact ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm
      suzukiLimitingUnitAperture u
  have hprime := inner_suzukiLimitingIntervalPrimeOperator_core u
  have hmass := inner_suzukiLimitingCoreIntervalVector_self u
  have hsmooth := inner_suzukiLimitingOriginKernelOperator_core u
  have hscalar :=
    weilScalarBlock_suzukiWeilArchimedeanConstant_eq_autocorrelation_zero
      suzukiLimitingUnitAperture u
  dsimp only [suzukiLimitingUnitAperture] at hscalar
  change inner ℂ q q +
      inner ℂ (suzukiLimitingLogBoundedRemainder
        (suzukiLimitingLogFormEmbedding q))
        (suzukiLimitingLogFormEmbedding q) = _
  rw [← hf]
  rw [inner_suzukiLimitingLogBoundedRemainder_eq_intervalWeil_add_corrections]
  calc
    inner ℂ q q +
          (inner ℂ
              (suzukiWeilIntervalBoundedRemainder
                suzukiLimitingUnitAperture f) f +
            inner ℂ (suzukiLimitingIntervalPrimeOperator f) f +
            ↑(2 * suzukiWeilArchimedeanConstant + 1) * inner ℂ f f +
            inner ℂ (suzukiLimitingOriginKernelOperator f) f) =
        suzukiWeilIntervalForm suzukiLimitingUnitAperture q q +
          inner ℂ (suzukiLimitingIntervalPrimeOperator f) f +
          ↑(2 * suzukiWeilArchimedeanConstant + 1) * inner ℂ f f +
          inner ℂ (suzukiLimitingOriginKernelOperator f) f := by
      unfold suzukiWeilIntervalForm
      rw [← hfWeil]
      ring
    _ = (suzukiRestrictedWeilForm 1 u u : ℂ) +
          ((-weilPrimeBlock (suzukiRestrictedWeilIndices 1) u u : ℝ) : ℂ) +
          ↑(2 * suzukiWeilArchimedeanConstant + 1) *
            (suzukiCoreAutocorrelation u 0 : ℂ) +
          ((-weilSmoothBlock 1 suzukiOriginRemainderCurvature u u : ℝ) : ℂ) := by
      rw [hfull, hprime, hmass, hsmooth]
    _ = (weilFinitePartBlock 1 u u : ℂ) := by
      rw [suzukiRestrictedWeilForm_eq_originRemainderFourBlocks, hscalar]
      push_cast
      ring

/-- Covariance-defined bottom energy is the Rayleigh floor on the entire closed form domain. -/
theorem suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le
    (u : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogOperatorGroundEnergy *
          ‖suzukiLimitingLogFormEmbedding u‖ ^ 2 ≤
      (suzukiLimitingLogClosedForm u u).re := by
  exact boundedPerturbedForm_ground_mul_norm_sq_le
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding
    u

/-- Covariance-defined bottom energy lies below every real eigenvalue of the limiting operator. -/
theorem suzukiLimitingLogOperatorGroundEnergy_le_eigenvalue
    {lam : ℝ} (x : suzukiLimitingLogOperator.domain)
    (hxne : (x : SuzukiApertureIntervalL2 1) ≠ 0)
    (hx : suzukiLimitingLogOperator x =
      (lam : ℂ) • (x : SuzukiApertureIntervalL2 1)) :
    suzukiLimitingLogOperatorGroundEnergy ≤ lam := by
  exact boundedPerturbedFriedrichsOperator_ground_le_eigenvalue
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding
    x hxne hx

end RHTower
