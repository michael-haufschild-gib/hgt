import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableCompletedCovarianceCharacteristic
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAllAngleCarrierSchurSecondJet
import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
# Scaled self-adjoint realization of movable Suzuki covariance

For every positive height `c`, rescale Suzuki's minimal derivative by `c⁻¹`.  Literal raw
deficiencies at `±c` then become normalized `±i` deficiency vectors.  Complex eigenspace
completeness makes their von Neumann extension self-adjoint, and its Green boundary pairing is
exactly movable completed-covariance characteristic pencil.

Thus movable characteristic has all-angle real zeros and is strictly Schur without importing an
RH-equivalent positivity premise.  Combined with exact covariance defect rate, Schwarz--Pick gives
a cofinal `O(c²)` second-jet budget and boundary transport to zero.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section
namespace RHTower

/-- Minimal derivative in spectral units where movable height `c` becomes unit height. -/
def suzukiTaScaledMinimalDerivative
    (a : SuzukiPositiveAperture) (c : ℝ) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a :=
  ((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a

theorem dense_suzukiTaScaledMinimalDerivative_domain
    (a : SuzukiPositiveAperture) (c : ℝ) :
    Dense ((suzukiTaScaledMinimalDerivative a c).domain : Set (SuzukiTaHilbert a)) := by
  exact dense_suzukiTaShiftedDerivativePMap_domain a 0

theorem suzukiTaScaledMinimalDerivative_symmetric
    (a : SuzukiPositiveAperture) (c : ℝ) :
    (suzukiTaScaledMinimalDerivative a c).IsFormalAdjoint
      (suzukiTaScaledMinimalDerivative a c) := by
  intro x y
  change inner ℂ (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a x) (y : SuzukiTaHilbert a) =
    inner ℂ (x : SuzukiTaHilbert a) (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a y)
  rw [inner_smul_left, inner_smul_right]
  simpa using congrArg (fun q : ℂ => ((c : ℂ)⁻¹) * q)
    (suzukiTaMinimalDerivative_symmetric a x y)

theorem suzukiTaRawDeficiency_eq_spectralVector_mul_I
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaRawDeficiency a c = suzukiTaSpectralVector a ((c : ℂ) * I) := by
  apply ext_inner_right ℂ
  intro x
  rw [suzukiTaRawDeficiency_inner, suzukiTaSpectralVector_inner]
  rw [suzukiTaMoment, suzukiTaSpectralMoment,
    suzukiTaSpectralExponential_mul_I_eq]

def suzukiTaOriginalToScaledAdjointDomain
    (a : SuzukiPositiveAperture) (c : ℝ)
    (x : (suzukiTaMinimalDerivative a).adjoint.domain) :
    (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
  ⟨(x : SuzukiTaHilbert a), by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨((c : ℂ)⁻¹) • (suzukiTaMinimalDerivative a).adjoint x, ?_⟩
    intro y
    change inner ℂ (((c : ℂ)⁻¹) • (suzukiTaMinimalDerivative a).adjoint x)
        (y : SuzukiTaHilbert a) =
      inner ℂ (x : SuzukiTaHilbert a)
        (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a y)
    rw [inner_smul_left, inner_smul_right]
    simpa using congrArg (fun q : ℂ => ((c : ℂ)⁻¹) * q)
      (LinearPMap.adjoint_isFormalAdjoint
        (dense_suzukiTaShiftedDerivativePMap_domain a 0) x y)⟩

theorem suzukiTaScaled_adjoint_originalToScaled
    (a : SuzukiPositiveAperture) (c : ℝ)
    (x : (suzukiTaMinimalDerivative a).adjoint.domain) :
    (suzukiTaScaledMinimalDerivative a c).adjoint
        (suzukiTaOriginalToScaledAdjointDomain a c x) =
      ((c : ℂ)⁻¹) • (suzukiTaMinimalDerivative a).adjoint x := by
  apply LinearPMap.adjoint_apply_eq
    (dense_suzukiTaScaledMinimalDerivative_domain a c)
  intro y
  change inner ℂ (((c : ℂ)⁻¹) • (suzukiTaMinimalDerivative a).adjoint x)
      (y : SuzukiTaHilbert a) =
    inner ℂ (x : SuzukiTaHilbert a)
      (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a y)
  rw [inner_smul_left, inner_smul_right]
  simpa using congrArg (fun q : ℂ => ((c : ℂ)⁻¹) * q)
    (LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x y)

def suzukiTaScaledToOriginalAdjointDomain
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (x : (suzukiTaScaledMinimalDerivative a c).adjoint.domain) :
    (suzukiTaMinimalDerivative a).adjoint.domain :=
  ⟨(x : SuzukiTaHilbert a), by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨(c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x, ?_⟩
    intro y
    let yScaled : (suzukiTaScaledMinimalDerivative a c).domain :=
      ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaScaledMinimalDerivative_domain a c) x yScaled
    change inner ℂ ((c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x)
        (y : SuzukiTaHilbert a) =
      inner ℂ (x : SuzukiTaHilbert a) (suzukiTaMinimalDerivative a y)
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal]
    rw [hformal]
    change (c : ℂ) * inner ℂ (x : SuzukiTaHilbert a)
        (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a y) = _
    rw [inner_smul_right]
    field_simp [Complex.ofReal_ne_zero.mpr hc]⟩

theorem suzukiTaOriginal_adjoint_scaledToOriginal
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (x : (suzukiTaScaledMinimalDerivative a c).adjoint.domain) :
    (suzukiTaMinimalDerivative a).adjoint
        (suzukiTaScaledToOriginalAdjointDomain a hc x) =
      (c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x := by
  apply LinearPMap.adjoint_apply_eq
    (dense_suzukiTaShiftedDerivativePMap_domain a 0)
  intro y
  let yScaled : (suzukiTaScaledMinimalDerivative a c).domain :=
    ⟨(y : SuzukiTaHilbert a), y.property⟩
  have hformal := LinearPMap.adjoint_isFormalAdjoint
    (dense_suzukiTaScaledMinimalDerivative_domain a c) x yScaled
  change inner ℂ ((c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x)
      (y : SuzukiTaHilbert a) =
    inner ℂ (x : SuzukiTaHilbert a) (suzukiTaMinimalDerivative a y)
  rw [inner_smul_left]
  simp only [Complex.conj_ofReal]
  rw [hformal]
  change (c : ℂ) * inner ℂ (x : SuzukiTaHilbert a)
      (((c : ℂ)⁻¹) • suzukiTaMinimalDerivative a y) = _
  rw [inner_smul_right]
  field_simp [Complex.ofReal_ne_zero.mpr hc]

def suzukiTaScaledPlusDeficiencyDomain
    (a : SuzukiPositiveAperture) (c : ℝ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
  suzukiTaOriginalToScaledAdjointDomain a c
    (suzukiTaRawDeficiencyDomain a c)

def suzukiTaScaledMinusDeficiencyDomain
    (a : SuzukiPositiveAperture) (c : ℝ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
  suzukiTaOriginalToScaledAdjointDomain a c
    (suzukiTaRawDeficiencyDomain a (-c))

theorem suzukiTaScaled_adjoint_plusDeficiency
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0) :
    (suzukiTaScaledMinimalDerivative a c).adjoint
        (suzukiTaScaledPlusDeficiencyDomain a c) =
      I • suzukiTaRawDeficiency a c := by
  rw [suzukiTaScaledPlusDeficiencyDomain,
    suzukiTaScaled_adjoint_originalToScaled]
  rw [suzukiTa_adjoint_rawDeficiency, smul_smul]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hc]

theorem suzukiTaScaled_adjoint_minusDeficiency
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0) :
    (suzukiTaScaledMinimalDerivative a c).adjoint
        (suzukiTaScaledMinusDeficiencyDomain a c) =
      (-I) • suzukiTaRawDeficiency a (-c) := by
  rw [suzukiTaScaledMinusDeficiencyDomain,
    suzukiTaScaled_adjoint_originalToScaled]
  rw [suzukiTa_adjoint_rawDeficiency, smul_smul]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hc]

theorem suzukiTaScaled_plusEigenspace_span
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (x : (suzukiTaScaledMinimalDerivative a c).adjoint.domain)
    (hx : (suzukiTaScaledMinimalDerivative a c).adjoint x =
      I • (x : SuzukiTaHilbert a)) :
    ∃ alpha : ℂ, (x : SuzukiTaHilbert a) =
      alpha • suzukiTaRawDeficiency a c := by
  let xOriginal := suzukiTaScaledToOriginalAdjointDomain a hc x
  have hOriginal : (suzukiTaMinimalDerivative a).adjoint xOriginal =
      ((c : ℂ) * I) • (x : SuzukiTaHilbert a) := by
    rw [show (suzukiTaMinimalDerivative a).adjoint xOriginal =
      (c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x from
        suzukiTaOriginal_adjoint_scaledToOriginal a hc x, hx, smul_smul]
  obtain ⟨alpha, halpha⟩ :=
    suzukiTa_adjoint_eigenspace_span a ((c : ℂ) * I) xOriginal hOriginal
  rw [← suzukiTaRawDeficiency_eq_spectralVector_mul_I] at halpha
  exact ⟨alpha, halpha⟩

theorem suzukiTaScaled_minusEigenspace_span
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (x : (suzukiTaScaledMinimalDerivative a c).adjoint.domain)
    (hx : (suzukiTaScaledMinimalDerivative a c).adjoint x =
      (-I) • (x : SuzukiTaHilbert a)) :
    ∃ beta : ℂ, (x : SuzukiTaHilbert a) =
      beta • suzukiTaRawDeficiency a (-c) := by
  let xOriginal := suzukiTaScaledToOriginalAdjointDomain a hc x
  have hOriginal : (suzukiTaMinimalDerivative a).adjoint xOriginal =
      (((-c : ℝ) : ℂ) * I) • (x : SuzukiTaHilbert a) := by
    rw [show (suzukiTaMinimalDerivative a).adjoint xOriginal =
      (c : ℂ) • (suzukiTaScaledMinimalDerivative a c).adjoint x from
        suzukiTaOriginal_adjoint_scaledToOriginal a hc x, hx, smul_smul]
    congr 1
    push_cast
    ring
  obtain ⟨beta, hbeta⟩ :=
    suzukiTa_adjoint_eigenspace_span a (((-c : ℝ) : ℂ) * I) xOriginal hOriginal
  rw [← suzukiTaRawDeficiency_eq_spectralVector_mul_I] at hbeta
  exact ⟨beta, hbeta⟩

noncomputable def suzukiTaScaledSelfAdjointExtension
    (a : SuzukiPositiveAperture) (c theta : ℝ) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a :=
  LinearPMap.deficiencyExtension
    (dense_suzukiTaScaledMinimalDerivative_domain a c)
    (suzukiTaScaledMinimalDerivative_symmetric a c)
    (suzukiTaScaledPlusDeficiencyDomain a c)
    (suzukiTaScaledMinusDeficiencyDomain a c)
    (suzukiTaBoundaryPhase theta)

theorem suzukiTaScaledSelfAdjointExtension_isSelfAdjoint
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0) (theta : ℝ) :
    IsSelfAdjoint (suzukiTaScaledSelfAdjointExtension a c theta) := by
  exact LinearPMap.deficiencyExtension_isSelfAdjoint
    (dense_suzukiTaScaledMinimalDerivative_domain a c)
    (suzukiTaScaledMinimalDerivative_symmetric a c)
    (suzukiTaScaled_adjoint_plusDeficiency a hc)
    (suzukiTaScaled_adjoint_minusDeficiency a hc)
    (suzukiTaRawDeficiency_ne_zero a c)
    (norm_suzukiTaRawDeficiency_neg_eq a c).symm
    (norm_suzukiTaBoundaryPhase theta)
    (suzukiTaScaled_plusEigenspace_span a hc)
    (suzukiTaScaled_minusEigenspace_span a hc)

def suzukiTaScaledSpectralVectorDomain
    (a : SuzukiPositiveAperture) (c : ℝ) (z : ℂ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
  suzukiTaOriginalToScaledAdjointDomain a c
    (suzukiTaSpectralVectorDomain a ((c : ℂ) * z))

theorem suzukiTaScaled_adjoint_spectralVector
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint
        (suzukiTaScaledSpectralVectorDomain a c z) =
      z • suzukiTaSpectralVector a ((c : ℂ) * z) := by
  rw [suzukiTaScaledSpectralVectorDomain,
    suzukiTaScaled_adjoint_originalToScaled]
  rw [suzukiTa_adjoint_spectralVector, smul_smul]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hc]

theorem suzukiTaPhysicalFourier_rawDeficiency_reflection
    (a : SuzukiPositiveAperture) (c : ℝ) (z : ℂ) :
    suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a (-c)) z =
      suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a c) (-z) := by
  rw [suzukiTaPhysicalFourier, suzukiTaPhysicalFourier,
    suzukiTaPhysicalEmbedding_rawDeficiency_reflection,
    suzukiApertureZeroExtendL2_intervalReflection,
    suzukiCompactL2Fourier_l2Reflection]

def suzukiTaScaledBoundaryVectorDomain
    (a : SuzukiPositiveAperture) (c theta : ℝ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
  suzukiTaScaledPlusDeficiencyDomain a c +
    suzukiTaBoundaryPhase theta • suzukiTaScaledMinusDeficiencyDomain a c

theorem suzukiTaScaled_adjoint_boundaryVector
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0) (theta : ℝ) :
    (suzukiTaScaledMinimalDerivative a c).adjoint
        (suzukiTaScaledBoundaryVectorDomain a c theta) =
      I • suzukiTaRawDeficiency a c -
        I • (suzukiTaBoundaryPhase theta • suzukiTaRawDeficiency a (-c)) := by
  rw [suzukiTaScaledBoundaryVectorDomain, LinearPMap.map_add, LinearPMap.map_smul,
    suzukiTaScaled_adjoint_plusDeficiency a hc,
    suzukiTaScaled_adjoint_minusDeficiency a hc]
  module

theorem suzukiTaScaledSpectralVector_inner_plus
    (a : SuzukiPositiveAperture) (c : ℝ) (z : ℂ) :
    inner ℂ (suzukiTaSpectralVector a ((c : ℂ) * star z))
        (suzukiTaRawDeficiency a c) =
      suzukiTaMovableCompletedCovarianceFourier a c z := by
  rw [suzukiTaSpectralVector_inner,
    suzukiTaMovableCompletedCovarianceFourier_eq_physical,
    ← suzukiTaSpectralMoment_star_eq_physicalFourier]
  congr 2
  apply Complex.ext <;> simp

theorem suzukiTaScaledSpectralVector_inner_minus
    (a : SuzukiPositiveAperture) (c : ℝ) (z : ℂ) :
    inner ℂ (suzukiTaSpectralVector a ((c : ℂ) * star z))
        (suzukiTaRawDeficiency a (-c)) =
      suzukiTaMovableCompletedCovarianceFourier a c (-z) := by
  rw [suzukiTaSpectralVector_inner,
    show suzukiTaSpectralMoment a ((c : ℂ) * star z)
        (suzukiTaRawDeficiency a (-c)) =
      suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a (-c)) ((c : ℂ) * z) by
        rw [← suzukiTaSpectralMoment_star_eq_physicalFourier]
        congr 2
        apply Complex.ext <;> simp,
    suzukiTaPhysicalFourier_rawDeficiency_reflection,
    suzukiTaMovableCompletedCovarianceFourier_eq_physical]
  congr 2
  ring

theorem suzukiTaMovableCompletedCovariancePencil_eq_scaledBoundaryPairing
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (theta : ℝ) (z : ℂ) :
    suzukiCharacteristicPencil
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiTaBoundaryPhase theta) z =
      LinearPMap.adjointBoundaryPairing
        (suzukiTaScaledMinimalDerivative a c)
        (suzukiTaScaledSpectralVectorDomain a c (star z))
        (suzukiTaScaledBoundaryVectorDomain a c theta) := by
  rw [suzukiCharacteristicPencil, suzukiFourierNumerator,
    suzukiFourierDenominator, LinearPMap.adjointBoundaryPairing,
    suzukiTaScaled_adjoint_spectralVector a hc,
    suzukiTaScaled_adjoint_boundaryVector a hc]
  change
    (z - I) * suzukiTaMovableCompletedCovarianceFourier a c z +
        suzukiTaBoundaryPhase theta *
          ((z + I) * suzukiTaMovableCompletedCovarianceFourier a c (-z)) =
      inner ℂ ((star z) • suzukiTaSpectralVector a ((c : ℂ) * star z))
          (suzukiTaRawDeficiency a c +
            suzukiTaBoundaryPhase theta • suzukiTaRawDeficiency a (-c)) -
        inner ℂ (suzukiTaSpectralVector a ((c : ℂ) * star z))
          (I • suzukiTaRawDeficiency a c -
            I • (suzukiTaBoundaryPhase theta • suzukiTaRawDeficiency a (-c)))
  rw [inner_smul_left, inner_add_right, inner_smul_right,
    inner_sub_right, inner_smul_right, inner_smul_right, inner_smul_right,
    suzukiTaScaledSpectralVector_inner_plus,
    suzukiTaScaledSpectralVector_inner_minus]
  simp only [starRingEnd_apply, star_star]
  ring

theorem suzukiTaScaledSpectralVector_mem_extension_of_pencil_eq_zero
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (theta : ℝ) (z : ℂ)
    (hz : suzukiCharacteristicPencil
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiTaBoundaryPhase theta) z = 0) :
    suzukiTaSpectralVector a ((c : ℂ) * star z) ∈
      (suzukiTaScaledSelfAdjointExtension a c theta).domain := by
  apply LinearPMap.mem_deficiencyExtensionDomain_of_boundary_zero
    (dense_suzukiTaScaledMinimalDerivative_domain a c)
    (suzukiTaScaledMinimalDerivative_symmetric a c)
    (suzukiTaScaledPlusDeficiencyDomain a c)
    (suzukiTaScaledMinusDeficiencyDomain a c)
    (suzukiTaBoundaryPhase theta)
    (suzukiTaScaledSelfAdjointExtension_isSelfAdjoint a hc theta)
    (suzukiTaScaledSpectralVectorDomain a c (star z))
  change LinearPMap.adjointBoundaryPairing
      (suzukiTaScaledMinimalDerivative a c)
      (suzukiTaScaledSpectralVectorDomain a c (star z))
      (suzukiTaScaledBoundaryVectorDomain a c theta) = 0
  rw [← suzukiTaMovableCompletedCovariancePencil_eq_scaledBoundaryPairing a hc]
  exact hz

theorem suzukiTaMovableCompletedCovariancePencil_zero_im_eq_zero
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : c ≠ 0)
    (theta : ℝ) (z : ℂ)
    (hz : suzukiCharacteristicPencil
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiTaBoundaryPhase theta) z = 0) :
    z.im = 0 := by
  let x : (suzukiTaScaledSelfAdjointExtension a c theta).domain :=
    ⟨suzukiTaSpectralVector a ((c : ℂ) * star z),
      suzukiTaScaledSpectralVector_mem_extension_of_pencil_eq_zero
        a hc theta z hz⟩
  have hx0 : (x : SuzukiTaHilbert a) ≠ 0 :=
    suzukiTaSpectralVector_ne_zero a ((c : ℂ) * star z)
  have hx : suzukiTaScaledSelfAdjointExtension a c theta x =
      (star z) • (x : SuzukiTaHilbert a) := by
    calc
      suzukiTaScaledSelfAdjointExtension a c theta x =
          (suzukiTaScaledMinimalDerivative a c).adjoint
            ⟨(x : SuzukiTaHilbert a),
              LinearPMap.deficiencyExtensionDomain_le_adjoint
                (dense_suzukiTaScaledMinimalDerivative_domain a c)
                (suzukiTaScaledMinimalDerivative_symmetric a c)
                (suzukiTaScaledPlusDeficiencyDomain a c)
                (suzukiTaScaledMinusDeficiencyDomain a c)
                (suzukiTaBoundaryPhase theta) x.property⟩ := by
            exact LinearPMap.deficiencyExtension_apply
              (dense_suzukiTaScaledMinimalDerivative_domain a c)
              (suzukiTaScaledMinimalDerivative_symmetric a c)
              (suzukiTaScaledPlusDeficiencyDomain a c)
              (suzukiTaScaledMinusDeficiencyDomain a c)
              (suzukiTaBoundaryPhase theta) x
      _ = (star z) • (x : SuzukiTaHilbert a) := by
        let xAdj : (suzukiTaScaledMinimalDerivative a c).adjoint.domain :=
          ⟨(x : SuzukiTaHilbert a),
            LinearPMap.deficiencyExtensionDomain_le_adjoint
              (dense_suzukiTaScaledMinimalDerivative_domain a c)
              (suzukiTaScaledMinimalDerivative_symmetric a c)
              (suzukiTaScaledPlusDeficiencyDomain a c)
              (suzukiTaScaledMinusDeficiencyDomain a c)
              (suzukiTaBoundaryPhase theta) x.property⟩
        have hxeq : xAdj =
            suzukiTaScaledSpectralVectorDomain a c (star z) := by
          apply Subtype.ext
          rfl
        change (suzukiTaScaledMinimalDerivative a c).adjoint xAdj =
          (star z) • (x : SuzukiTaHilbert a)
        rw [hxeq]
        exact suzukiTaScaled_adjoint_spectralVector a hc (star z)
  have him : (star z).im = 0 :=
    eigenvalue_im_eq_zero_of_isFormalAdjoint
      (isFormalAdjoint_of_isSelfAdjoint
        (suzukiTaScaledSelfAdjointExtension_isSelfAdjoint a hc theta))
      x (star z) hx0 hx
  simpa using him

/-- Every unitary movable characteristic pencil has only real zeros at each positive height. -/
theorem suzukiTaMovableCompletedCovariance_allAngleRealZeros
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    SuzukiAllAngleRealZeros
      (suzukiFourierNumerator
        (suzukiTaMovableCompletedCovarianceFourier a c))
      (suzukiFourierDenominator
        (suzukiTaMovableCompletedCovarianceFourier a c)) := by
  intro u hu z hz
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff u).mp hu
  have hphase : suzukiTaBoundaryPhase theta = u := by
    rw [suzukiTaBoundaryPhase]
    convert htheta using 1
    ring_nf
  apply suzukiTaMovableCompletedCovariancePencil_zero_im_eq_zero
    a hc.ne' theta z
  rw [hphase]
  exact hz

theorem differentiable_suzukiTaMovableCompletedCovarianceFourier
    (a : SuzukiPositiveAperture) (c : ℝ) :
    Differentiable ℂ (suzukiTaMovableCompletedCovarianceFourier a c) := by
  intro z
  rw [show suzukiTaMovableCompletedCovarianceFourier a c =
      fun w => suzukiTaPhysicalFourier a
        (suzukiTaRawDeficiency a c) ((c : ℂ) * w) by
    funext w
    exact suzukiTaMovableCompletedCovarianceFourier_eq_physical a c w]
  exact ((differentiable_suzukiTaPhysicalFourier a _) _).comp z
    ((hasDerivAt_id z).const_mul (c : ℂ)).differentiableAt

theorem differentiable_suzukiTaMovableCompletedCovarianceNumerator
    (a : SuzukiPositiveAperture) (c : ℝ) :
    Differentiable ℂ
      (suzukiFourierNumerator
        (suzukiTaMovableCompletedCovarianceFourier a c)) := by
  exact (differentiable_id.sub_const I).mul
    (differentiable_suzukiTaMovableCompletedCovarianceFourier a c)

theorem differentiable_suzukiTaMovableCompletedCovarianceDenominator
    (a : SuzukiPositiveAperture) (c : ℝ) :
    Differentiable ℂ
      (suzukiFourierDenominator
        (suzukiTaMovableCompletedCovarianceFourier a c)) := by
  exact (differentiable_id.add_const I).mul
    ((differentiable_suzukiTaMovableCompletedCovarianceFourier a c).comp
      differentiable_neg)

@[simp] theorem suzukiTaMovableCompletedCovarianceNumerator_I
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiFourierNumerator
      (suzukiTaMovableCompletedCovarianceFourier a c) I = 0 := by
  simp [suzukiFourierNumerator]

/-- Literal movable completed-covariance characteristic is strictly Schur on upper half-plane. -/
theorem norm_suzukiTaMovableCompletedCovarianceLivsic_lt_one
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiLivsicQuotient
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c)) z‖ < 1 := by
  exact norm_suzukiLivsicQuotient_lt_one
    (differentiable_suzukiTaMovableCompletedCovarianceNumerator a c).continuous
    (differentiable_suzukiTaMovableCompletedCovarianceDenominator a c).continuous
    (suzukiTaMovableCompletedCovarianceNumerator_I a c)
    (suzukiTaMovableCompletedCovariance_allAngleRealZeros a hc) hz

theorem norm_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_le_schurSlack
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    ‖iteratedDeriv 2
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ ≤
      2 * (1 - ‖deriv
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ ^ 2) := by
  change ‖iteratedDeriv 2 (fun w =>
      suzukiLivsicQuotient
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiUpperCayleyInv w)) 0‖ ≤
    2 * (1 - ‖deriv (fun w =>
      suzukiLivsicQuotient
        (suzukiFourierNumerator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiFourierDenominator
          (suzukiTaMovableCompletedCovarianceFourier a c))
        (suzukiUpperCayleyInv w)) 0‖ ^ 2)
  exact norm_suzukiAllAngleCarrier_secondJet_le_schurSlack
    (differentiable_suzukiTaMovableCompletedCovarianceNumerator a c)
    (differentiable_suzukiTaMovableCompletedCovarianceDenominator a c)
    (suzukiTaMovableCompletedCovarianceNumerator_I a c)
    (suzukiTaMovableCompletedCovariance_allAngleRealZeros a hc)

theorem norm_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_le_sourceSlack
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    ‖iteratedDeriv 2
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ ≤
      2 * (1 -
        suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a c)
          (suzukiTaCoalescingOddEnergy a c) ^ 2) := by
  simpa only [deriv_suzukiTaMovableCompletedCovarianceLivsicDisk_zero,
    norm_real, Real.norm_eq_abs, sq_abs] using
      norm_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_le_schurSlack a hc

/-- Cofinal normalized second jet retains exact position-resolvent coefficient. -/
theorem eventually_suzukiTaMovableCompletedCovarianceLivsicDisk_normalizedSecondJet_lt
    (a : SuzukiPositiveAperture) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ‖iteratedDeriv 2
          (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ /
            (2 * c ^ 2) <
        4 * suzukiTaPositionResolventTangent a + 2 := by
  have hrate :=
    tendsto_suzukiTaMovableCompletedCovarianceLivsicDisk_deriv_re_sq_rate a
  have hlt : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      (1 - (deriv
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0).re ^ 2) /
          (2 * c ^ 2) <
        2 * suzukiTaPositionResolventTangent a + 1 :=
    hrate.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [self_mem_nhdsWithin, hlt] with c hc hrateLt
  have hc0 : c ≠ 0 := hc.ne'
  have hden : 0 < 2 * c ^ 2 := by positivity
  have hsource :=
    norm_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_le_sourceSlack
      a hc
  have hdiv :
      ‖iteratedDeriv 2
          (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ /
            (2 * c ^ 2) ≤
        2 * ((1 -
          suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a c)
            (suzukiTaCoalescingOddEnergy a c) ^ 2) /
              (2 * c ^ 2)) := by
    apply (div_le_iff₀ hden).2
    calc
      ‖iteratedDeriv 2
          (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ ≤
          2 * (1 -
            suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a c)
              (suzukiTaCoalescingOddEnergy a c) ^ 2) := hsource
      _ = 2 * ((1 -
            suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a c)
              (suzukiTaCoalescingOddEnergy a c) ^ 2) /
                (2 * c ^ 2)) * (2 * c ^ 2) := by
          field_simp [hc0]
  calc
    ‖iteratedDeriv 2
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0‖ /
          (2 * c ^ 2) ≤
        2 * ((1 -
          suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a c)
            (suzukiTaCoalescingOddEnergy a c) ^ 2) /
              (2 * c ^ 2)) := hdiv
    _ < 2 * (2 * suzukiTaPositionResolventTangent a + 1) := by
      apply mul_lt_mul_of_pos_left
      simpa only [deriv_suzukiTaMovableCompletedCovarianceLivsicDisk_zero,
        Complex.ofReal_re] using hrateLt
      norm_num
    _ = 4 * suzukiTaPositionResolventTangent a + 2 := by ring

/-- Movable characteristic second jet transports continuously to zero at coalescing boundary. -/
theorem tendsto_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_zero
    (a : SuzukiPositiveAperture) :
    Tendsto (fun c : ℝ => iteratedDeriv 2
        (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun c => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact norm_suzukiTaMovableCompletedCovarianceLivsicDisk_secondJet_le_sourceSlack
      a hc
  · have hfirst :=
      tendsto_suzukiTaMovableCompletedCovarianceLivsicDisk_deriv_re_one a
    have hsq : Tendsto (fun c : ℝ =>
        (deriv (suzukiTaMovableCompletedCovarianceLivsicDisk a c) 0).re ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [pow_two, one_mul] using hfirst.mul hfirst
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 2) := tendsto_const_nhds
    have hgap := hone.sub hsq
    have hbound := htwo.mul hgap
    convert hbound using 1
    · funext c
      rw [deriv_suzukiTaMovableCompletedCovarianceLivsicDisk_zero]
      simp
    · norm_num

end RHTower
