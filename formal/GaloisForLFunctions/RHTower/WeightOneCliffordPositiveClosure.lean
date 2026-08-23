import GaloisForLFunctions.HTGeometry.LinearPMapUnitarySquareTransport
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelCompressionBridge
import GaloisForLFunctions.RHTower.WeightOneCliffordLogClosure

/-!
# Closed weight-one Clifford--Dirac operator on the positive ray

This module transports the closed log-line realization to Suzuki's literal
`L²((0,∞), dt)` carrier. The exact natural square domain and composition identity are transported
together with the operators; the square remains self-adjoint.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal LinearPMap

namespace RHTower

/-- Closed weight-one Dirac realization on literal `L²((0,∞), dt)`. -/
def weightOnePositiveDirac (a : ℝ) : SuzukiPositiveL2 →ₗ.[ℂ] SuzukiPositiveL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap suzukiPositiveLogUnitary
    (weightOneLogDirac a)

/-- Literal positive-ray square transported from the self-adjoint log-line square. -/
def weightOnePositiveSquare (a : ℝ) : SuzukiPositiveL2 →ₗ.[ℂ] SuzukiPositiveL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap suzukiPositiveLogUnitary
    (weightOneLogSquare a)

/-- Integer-order Sobolev domain on the positive ray, transported by logarithmic half-density
coordinates from the standard Fourier domain on `L²(ℝ)`. -/
def weightOnePositiveSobolevDomain (n : ℕ) : Submodule ℂ SuzukiPositiveL2 :=
  (fourierL2SobolevDomain n).comap suzukiPositiveLogUnitary.toLinearEquiv.toLinearMap

/-- Transported `H¹` domain on `L²((0,∞), dt)`. -/
abbrev weightOnePositiveH1 : Submodule ℂ SuzukiPositiveL2 :=
  weightOnePositiveSobolevDomain 1

/-- Transported `H²` domain on `L²((0,∞), dt)`. -/
abbrev weightOnePositiveH2 : Submodule ℂ SuzukiPositiveL2 :=
  weightOnePositiveSobolevDomain 2

/-- Closed centered scale generator on the positive ray, obtained from the weak log derivative. -/
def weightOnePositiveCenteredGenerator : SuzukiPositiveL2 →ₗ.[ℂ] SuzukiPositiveL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap suzukiPositiveLogUnitary
    weightOneLogDerivative

/-- Weight-one inversion `J`, transported from reflection in logarithmic coordinates. -/
def weightOnePositiveInversion : SuzukiPositiveL2 →L[ℂ] SuzukiPositiveL2 :=
  suzukiPositiveLogUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    l2Reflection ∘L
      suzukiPositiveLogUnitary.toLinearIsometry.toContinuousLinearMap

@[simp] theorem weightOnePositiveInversion_apply (f : SuzukiPositiveL2) :
    weightOnePositiveInversion f =
      suzukiPositiveLogUnitary.symm (l2Reflection (suzukiPositiveLogUnitary f)) := rfl

/-- Positive-ray inversion is an involution. -/
@[simp] theorem weightOnePositiveInversion_involutive (f : SuzukiPositiveL2) :
    weightOnePositiveInversion (weightOnePositiveInversion f) = f := by
  apply suzukiPositiveLogUnitary.injective
  simp only [weightOnePositiveInversion_apply, LinearIsometryEquiv.apply_symm_apply,
    l2Reflection_involutive]

/-- Positive-ray inversion preserves the `L²` norm. -/
theorem weightOnePositiveInversion_norm (f : SuzukiPositiveL2) :
    ‖weightOnePositiveInversion f‖ = ‖f‖ := by
  calc
    ‖weightOnePositiveInversion f‖ = ‖l2Reflection (suzukiPositiveLogUnitary f)‖ := by
      rw [weightOnePositiveInversion_apply, suzukiPositiveLogUnitary.symm.norm_map]
    _ = ‖suzukiPositiveLogUnitary f‖ := by
      change ‖l2ReflectionIsometry (suzukiPositiveLogUnitary f)‖ = _
      exact l2ReflectionIsometry.norm_map _
    _ = ‖f‖ := suzukiPositiveLogUnitary.norm_map f

/-- Positive-ray inversion is symmetric, hence bounded self-adjoint in the Hilbert-space sense. -/
theorem weightOnePositiveInversion_symmetric :
    weightOnePositiveInversion.toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner ℂ (weightOnePositiveInversion f) g =
        inner ℂ (suzukiPositiveLogUnitary (weightOnePositiveInversion f))
          (suzukiPositiveLogUnitary g) :=
      (suzukiPositiveLogUnitary.inner_map_map _ _).symm
    _ = inner ℂ (l2Reflection (suzukiPositiveLogUnitary f))
          (suzukiPositiveLogUnitary g) := by
      rw [weightOnePositiveInversion_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ (suzukiPositiveLogUnitary f)
          (l2Reflection (suzukiPositiveLogUnitary g)) :=
      l2Reflection_symmetric _ _
    _ = inner ℂ (suzukiPositiveLogUnitary f)
          (suzukiPositiveLogUnitary (weightOnePositiveInversion g)) := by
      rw [weightOnePositiveInversion_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ f (weightOnePositiveInversion g) :=
      suzukiPositiveLogUnitary.inner_map_map _ _

/-- Reciprocal transport of the positive-ray measure is quasi-measure-preserving. -/
theorem positiveReciprocal_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : ℝ => x⁻¹)
      (volume.restrict (Ioi (0 : ℝ))) volume := by
  have hcomp := realExp_quasiMeasurePreserving.comp
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
      realLog_restrict_Ioi_quasiMeasurePreserving)
  apply hcomp.congr measurable_inv
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Function.comp_apply]
  rw [Real.exp_neg, Real.exp_log hx]

/-- Exact physical representative of positive-ray inversion:
`(Jf)(x) = x⁻¹ f(x⁻¹)` for almost every positive `x`. -/
theorem weightOnePositiveInversion_ae (f : SuzukiPositiveL2) :
    (weightOnePositiveInversion f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x => (x⁻¹ : ℂ) * (f : ℝ → ℂ) x⁻¹ := by
  let q : SoninL2 := suzukiPositiveLogUnitary f
  have hcarrier : suzukiPositiveLogUnitary.symm q = f := by
    exact suzukiPositiveLogUnitary.symm_apply_apply f
  have hout := suzukiPositiveHalfLineUnitary_logEven_symm_ae (l2Reflection q)
  change (suzukiPositiveLogUnitary.symm (l2Reflection q) : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] _ at hout
  have hJ : weightOnePositiveInversion f =
      suzukiPositiveLogUnitary.symm (l2Reflection q) := rfl
  rw [← hJ] at hout
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  have hcarrierPhysical :
      suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) = f := by
    change suzukiPositiveLogUnitary.symm q = f
    exact hcarrier
  rw [hcarrierPhysical] at hcoord
  have hcoordWhole := (ae_restrict_iff' measurableSet_Ioi).mp hcoord
  have hcoordInv := positiveReciprocal_quasiMeasurePreserving.ae hcoordWhole
  have hrepRLog := realLog_restrict_Ioi_quasiMeasurePreserving.ae
    (l2MeasurableRep_ae (l2Reflection q))
  have hrefLog := realLog_restrict_Ioi_quasiMeasurePreserving.ae (l2Reflection_ae q)
  have hrepNegLog :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
      realLog_restrict_Ioi_quasiMeasurePreserving).ae (l2MeasurableRep_ae q)
  filter_upwards [hout, hcoordInv, hrepRLog, hrefLog, hrepNegLog,
    ae_restrict_mem measurableSet_Ioi] with x hout hin hrepR href hrepq hx
  have hrepq' : l2MeasurableRep q (-Real.log x) = (q : ℝ → ℂ) (-Real.log x) := by
    simpa only [Function.comp_apply] using hrepq
  rw [hout, hrepR, href, ← hrepq']
  have hin' : (f : ℝ → ℂ) x⁻¹ =
      (Real.exp (Real.log x / 2) : ℂ) * l2MeasurableRep q (-Real.log x) := by
    have hxinv : x⁻¹ ∈ Ioi (0 : ℝ) := by
      show 0 < x⁻¹
      exact inv_pos.mpr (show 0 < x from hx)
    have hinAtInv := hin hxinv
    rw [Real.log_inv x] at hinAtInv
    simpa only [neg_neg] using hinAtInv
  rw [hin']
  have hweight : Real.exp (-(Real.log x) / 2) =
      x⁻¹ * Real.exp (Real.log x / 2) := by
    calc
      Real.exp (-(Real.log x) / 2) =
          Real.exp (-Real.log x) * Real.exp (Real.log x / 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ = x⁻¹ * Real.exp (Real.log x / 2) := by
            rw [Real.exp_neg, Real.exp_log (show 0 < x from hx)]
  push_cast [hweight]
  ring

@[simp] theorem weightOnePositiveDirac_domain (a : ℝ) :
    (weightOnePositiveDirac a).domain =
      (weightOneLogDirac a).domain.comap
        suzukiPositiveLogUnitary.toLinearEquiv.toLinearMap := rfl

@[simp] theorem weightOnePositiveSquare_domain (a : ℝ) :
    (weightOnePositiveSquare a).domain =
      (weightOneLogSquare a).domain.comap
        suzukiPositiveLogUnitary.toLinearEquiv.toLinearMap := rfl

/-- Exact transported first-order domain of the positive-ray Dirac operator. -/
theorem weightOnePositiveDirac_domain_eq_H1 (a : ℝ) :
    (weightOnePositiveDirac a).domain = weightOnePositiveH1 := by
  rw [weightOnePositiveDirac_domain, weightOneLogDirac_domain_eq_fourierL2H1]
  rfl

/-- Exact transported second-order domain of the positive-ray self-adjoint square. -/
theorem weightOnePositiveSquare_domain_eq_H2 (a : ℝ) :
    (weightOnePositiveSquare a).domain = weightOnePositiveH2 := by
  rw [weightOnePositiveSquare_domain, weightOneLogSquare_domain_eq_fourierL2H2]
  rfl

/-- The positive-ray square domain is independent of the real Clifford mass. -/
theorem weightOnePositiveSquare_domain_eq_zero (a : ℝ) :
    (weightOnePositiveSquare a).domain = (weightOnePositiveSquare 0).domain := by
  rw [weightOnePositiveSquare_domain, weightOnePositiveSquare_domain,
    weightOneLogSquare_domain_eq_zero]

/-- Exact positive-ray mass shift: `Q_a² = Q_0² + a²` on the common transported `H²`
domain. -/
theorem weightOnePositiveSquare_apply_eq_zero_add_mass (a : ℝ)
    (f : (weightOnePositiveSquare a).domain) :
    let hf₀ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveSquare 0).domain := by
      rw [← weightOnePositiveSquare_domain_eq_zero a]
      exact f.property
    weightOnePositiveSquare a f =
      weightOnePositiveSquare 0 ⟨(f : SuzukiPositiveL2), hf₀⟩ +
        (a ^ 2 : ℂ) • (f : SuzukiPositiveL2) := by
  dsimp only
  apply suzukiPositiveLogUnitary.injective
  rw [map_add, map_smul]
  simp only [weightOnePositiveSquare,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact weightOneLogSquare_apply_eq_zero_add_mass a
    ⟨suzukiPositiveLogUnitary (f : SuzukiPositiveL2), f.property⟩

/-- The centered scale generator has exactly the transported `H¹` domain. -/
theorem weightOnePositiveCenteredGenerator_domain_eq_H1 :
    weightOnePositiveCenteredGenerator.domain = weightOnePositiveH1 := by
  change weightOneLogDerivative.domain.comap
      suzukiPositiveLogUnitary.toLinearEquiv.toLinearMap = _
  rw [weightOneLogDerivative_domain_eq_fourierL2H1]
  rfl

theorem weightOnePositiveDirac_isClosed (a : ℝ) :
    (weightOnePositiveDirac a).IsClosed :=
  GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.unitaryConjugate
    (weightOneLogDirac_isClosed a)

theorem weightOnePositiveSquare_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (weightOnePositiveSquare a) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate suzukiPositiveLogUnitary
    (weightOneLogSquare_isSelfAdjoint a)

@[simp] theorem suzukiPositiveLogUnitary_weightOnePositiveDirac_apply (a : ℝ)
    (f : (weightOnePositiveDirac a).domain) :
    suzukiPositiveLogUnitary (weightOnePositiveDirac a f) =
      weightOneLogDirac a
        (GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
          suzukiPositiveLogUnitary (weightOneLogDirac a) f) := by
  simp only [weightOnePositiveDirac,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The transported closed Dirac operator is exactly `aJ + C` on its maximal first-order
domain, where `C` is the centered scale generator and `J` is positive-ray inversion. -/
theorem weightOnePositiveDirac_apply_eq_inversion_add_centeredGenerator (a : ℝ)
    (f : (weightOnePositiveDirac a).domain) :
    let hfC : (f : SuzukiPositiveL2) ∈ weightOnePositiveCenteredGenerator.domain := f.property
    weightOnePositiveDirac a f =
      (a : ℂ) • weightOnePositiveInversion (f : SuzukiPositiveL2) +
        weightOnePositiveCenteredGenerator ⟨(f : SuzukiPositiveL2), hfC⟩ := by
  dsimp only
  apply suzukiPositiveLogUnitary.injective
  rw [suzukiPositiveLogUnitary_weightOnePositiveDirac_apply]
  rw [map_add, map_smul]
  simp only [weightOnePositiveInversion_apply, LinearIsometryEquiv.apply_symm_apply,
    weightOnePositiveCenteredGenerator,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply]
  rw [weightOneLogDirac_apply_eq_derivative_add_reflection]
  congr 2

/-- At Clifford mass `a = 0`, the positive-ray Dirac operator is exactly the centered scale
generator. -/
theorem weightOnePositiveDirac_zero_apply
    (f : (weightOnePositiveDirac 0).domain) :
    weightOnePositiveDirac 0 f =
      weightOnePositiveCenteredGenerator ⟨(f : SuzukiPositiveL2), f.property⟩ := by
  simpa using
    (weightOnePositiveDirac_apply_eq_inversion_add_centeredGenerator 0 f)

theorem weightOnePositiveSquare_domain_le_dirac (a : ℝ) :
    (weightOnePositiveSquare a).domain ≤ (weightOnePositiveDirac a).domain := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_domain_le_of_domain_le
    suzukiPositiveLogUnitary (weightOneLogSquare_domain_le_dirac a)

/-- Exact natural-domain criterion on the literal positive ray. -/
theorem weightOnePositiveSquare_mem_iff_dirac_apply_mem (a : ℝ)
    (f : SuzukiPositiveL2) (hf : f ∈ (weightOnePositiveDirac a).domain) :
    f ∈ (weightOnePositiveSquare a).domain ↔
      weightOnePositiveDirac a ⟨f, hf⟩ ∈ (weightOnePositiveDirac a).domain := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_mem_iff_apply_mem
    suzukiPositiveLogUnitary
    (fun x hx => weightOneLogSquare_mem_iff_dirac_apply_mem a x hx) f hf

/-- On literal positive-ray `L²`, the natural composition of the closed Dirac operator is exactly
the transported self-adjoint square. -/
theorem weightOnePositiveDirac_sq_apply (a : ℝ)
    (f : (weightOnePositiveSquare a).domain)
    (hf : (f : SuzukiPositiveL2) ∈ (weightOnePositiveDirac a).domain)
    (hQ : weightOnePositiveDirac a ⟨(f : SuzukiPositiveL2), hf⟩ ∈
      (weightOnePositiveDirac a).domain) :
    weightOnePositiveDirac a
        ⟨weightOnePositiveDirac a ⟨(f : SuzukiPositiveL2), hf⟩, hQ⟩ =
      weightOnePositiveSquare a f := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_square_apply
    suzukiPositiveLogUnitary
    (fun x hx hQ => weightOneLogDirac_sq_apply a x hx hQ) f hf hQ

/-- The mass-zero square is exactly the natural second composition of the centered scale
generator on the transported `H²` domain. -/
theorem weightOnePositiveCenteredGenerator_sq_apply
    (f : (weightOnePositiveSquare 0).domain) :
    let hfC : (f : SuzukiPositiveL2) ∈ weightOnePositiveCenteredGenerator.domain := by
      rw [weightOnePositiveCenteredGenerator_domain_eq_H1,
        ← weightOnePositiveDirac_domain_eq_H1 0]
      exact weightOnePositiveSquare_domain_le_dirac 0 f.property
    let hC : weightOnePositiveCenteredGenerator
        ⟨(f : SuzukiPositiveL2), hfC⟩ ∈
          weightOnePositiveCenteredGenerator.domain := by
      have hfQ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveDirac 0).domain :=
        weightOnePositiveSquare_domain_le_dirac 0 f.property
      have hQ := (weightOnePositiveSquare_mem_iff_dirac_apply_mem 0
        (f : SuzukiPositiveL2) hfQ).1 f.property
      rw [weightOnePositiveDirac_zero_apply] at hQ
      exact hQ
    weightOnePositiveCenteredGenerator
        ⟨weightOnePositiveCenteredGenerator ⟨(f : SuzukiPositiveL2), hfC⟩, hC⟩ =
      weightOnePositiveSquare 0 f := by
  dsimp only
  have hfQ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveDirac 0).domain :=
    weightOnePositiveSquare_domain_le_dirac 0 f.property
  have hQ := (weightOnePositiveSquare_mem_iff_dirac_apply_mem 0
    (f : SuzukiPositiveL2) hfQ).1 f.property
  have hsq := weightOnePositiveDirac_sq_apply 0 f hfQ hQ
  simpa only [weightOnePositiveDirac_zero_apply] using hsq

/-- **Closed positive-ray Clifford square.** On the exact transported `H²` domain, the natural
composition of `Q_a = C + aJ` is `C² + a²`, with all first- and second-composition membership
proofs obtained from the domain itself. -/
theorem weightOnePositiveCliffordSquare_eq_centeredSquare_add_mass
    (a : ℝ) (f : (weightOnePositiveSquare a).domain) :
    let hfQ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveDirac a).domain :=
      weightOnePositiveSquare_domain_le_dirac a f.property
    let hQ : weightOnePositiveDirac a ⟨(f : SuzukiPositiveL2), hfQ⟩ ∈
        (weightOnePositiveDirac a).domain :=
      (weightOnePositiveSquare_mem_iff_dirac_apply_mem a
        (f : SuzukiPositiveL2) hfQ).1 f.property
    let hf₀ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveSquare 0).domain := by
      rw [← weightOnePositiveSquare_domain_eq_zero a]
      exact f.property
    let hfC : (f : SuzukiPositiveL2) ∈ weightOnePositiveCenteredGenerator.domain := by
      rw [weightOnePositiveCenteredGenerator_domain_eq_H1,
        ← weightOnePositiveDirac_domain_eq_H1 0]
      exact weightOnePositiveSquare_domain_le_dirac 0 hf₀
    let hC : weightOnePositiveCenteredGenerator
        ⟨(f : SuzukiPositiveL2), hfC⟩ ∈
          weightOnePositiveCenteredGenerator.domain := by
      have hfQ₀ : (f : SuzukiPositiveL2) ∈ (weightOnePositiveDirac 0).domain :=
        weightOnePositiveSquare_domain_le_dirac 0 hf₀
      have hQ₀ := (weightOnePositiveSquare_mem_iff_dirac_apply_mem 0
        (f : SuzukiPositiveL2) hfQ₀).1 hf₀
      rw [weightOnePositiveDirac_zero_apply] at hQ₀
      exact hQ₀
    weightOnePositiveDirac a
        ⟨weightOnePositiveDirac a ⟨(f : SuzukiPositiveL2), hfQ⟩, hQ⟩ =
      weightOnePositiveCenteredGenerator
          ⟨weightOnePositiveCenteredGenerator ⟨(f : SuzukiPositiveL2), hfC⟩, hC⟩ +
        (a ^ 2 : ℂ) • (f : SuzukiPositiveL2) := by
  dsimp only
  rw [weightOnePositiveDirac_sq_apply a f]
  rw [weightOnePositiveSquare_apply_eq_zero_add_mass]
  rw [← weightOnePositiveCenteredGenerator_sq_apply]

end RHTower
