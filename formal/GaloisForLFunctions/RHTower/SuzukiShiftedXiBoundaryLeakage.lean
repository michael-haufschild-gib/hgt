import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelOperator
import GaloisForLFunctions.HTGeometry.HardyHorizontalLayerLeakage
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# Actual shifted-Xi boundary leakage

The real boundary of Suzuki's shifted quotient is unimodular away from the discrete denominator
divisor. Assigning value `1` on that null set gives an everywhere-unimodular measurable symbol.
This file constructs literal whole-line multiplication and its anti-causal Hardy compression for
every real shift, without a zero-free half-plane assumption.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Boundary value of Suzuki's shifted-Xi quotient, with the denominator-zero set assigned the
unimodular value `1`. -/
def suzukiShiftedXiBoundary (omega : ℝ) (u : ℝ) : ℂ :=
  if suzukiCanonicalE omega (u : ℂ) = 0 then 1
  else suzukiCanonicalTheta omega (u : ℂ)

theorem suzukiShiftedXiBoundary_eq_of_ne
    {omega u : ℝ} (hE : suzukiCanonicalE omega (u : ℂ) ≠ 0) :
    suzukiShiftedXiBoundary omega u = suzukiCanonicalTheta omega (u : ℂ) := by
  simp [suzukiShiftedXiBoundary, hE]

theorem norm_suzukiShiftedXiBoundary (omega u : ℝ) :
    ‖suzukiShiftedXiBoundary omega u‖ = 1 := by
  by_cases hE : suzukiCanonicalE omega (u : ℂ) = 0
  · simp [suzukiShiftedXiBoundary, hE]
  · rw [suzukiShiftedXiBoundary_eq_of_ne hE,
      norm_suzukiCanonicalTheta_ofReal_eq_one omega u hE]

theorem measurable_suzukiShiftedXiBoundary (omega : ℝ) :
    Measurable (suzukiShiftedXiBoundary omega) := by
  have hE : Measurable (fun u : ℝ => suzukiCanonicalE omega (u : ℂ)) :=
    ((differentiable_suzukiCanonicalE omega).continuous.comp
      Complex.continuous_ofReal).measurable
  have hTheta : Measurable (fun u : ℝ => suzukiCanonicalTheta omega (u : ℂ)) := by
    rw [show (fun u : ℝ => suzukiCanonicalTheta omega (u : ℂ)) =
        fun u : ℝ => (starRingEnd ℂ) (suzukiCanonicalE omega (u : ℂ)) /
          suzukiCanonicalE omega (u : ℂ) by
      funext u
      exact suzukiCanonicalTheta_ofReal_eq_conj_E_div_E omega u]
    exact (Complex.continuous_conj.measurable.comp hE).div hE
  exact Measurable.ite (hE (measurableSet_singleton 0)) measurable_const hTheta

/-- The real denominator divisor is null for every shift. -/
theorem volume_suzukiCanonicalE_real_zeroSet (omega : ℝ) :
    volume {u : ℝ | suzukiCanonicalE omega (u : ℂ) = 0} = 0 := by
  exact HTGeometry.volume_real_setOf_eq_zero_eq_zero
    (fun z _ => (differentiable_suzukiCanonicalE omega).analyticAt z)
    ⟨0, suzukiCanonicalE_zero_ne_zero omega⟩

/-- The patched boundary symbol is the literal shifted-Xi quotient almost everywhere. -/
theorem suzukiShiftedXiBoundary_ae_eq_canonicalTheta (omega : ℝ) :
    suzukiShiftedXiBoundary omega =ᵐ[volume]
      fun u => suzukiCanonicalTheta omega (u : ℂ) := by
  have hne : ∀ᵐ u : ℝ, suzukiCanonicalE omega (u : ℂ) ≠ 0 :=
    ae_iff.mpr (by
      simpa only [not_ne_iff] using volume_suzukiCanonicalE_real_zeroSet omega)
  filter_upwards [hne] with u hu
  exact suzukiShiftedXiBoundary_eq_of_ne hu

/-- Literal unitary whole-line multiplication by the shifted-Xi boundary quotient, valid at every
real shift without RH or a zero-free half-plane assumption. -/
def suzukiShiftedXiBoundaryMulUnitary (omega : ℝ) :
    RealLineL2 ≃ₗᵢ[ℂ] RealLineL2 :=
  unimodularMulUnitary (suzukiShiftedXiBoundary omega)
    (measurable_suzukiShiftedXiBoundary omega).aestronglyMeasurable
    (norm_suzukiShiftedXiBoundary omega)

theorem suzukiShiftedXiBoundaryMulUnitary_ae
    (omega : ℝ) (f : RealLineL2) :
    suzukiShiftedXiBoundaryMulUnitary omega f =ᵐ[volume]
      fun u => suzukiShiftedXiBoundary omega u * f u :=
  unimodularMulUnitary_ae _
    (measurable_suzukiShiftedXiBoundary omega).aestronglyMeasurable _ f

/-- Actual anti-causal Hardy compression `P₋ M_{Theta_omega}|H²₊`. -/
def suzukiShiftedXiHardyLeakage (omega : ℝ) :
    UpperHardyL2 →L[ℂ] LowerHardyL2 :=
  hardyLeakage
    (suzukiShiftedXiBoundaryMulUnitary omega).toLinearIsometry.toContinuousLinearMap

theorem norm_suzukiShiftedXiHardyLeakage_le_one (omega : ℝ) :
    ‖suzukiShiftedXiHardyLeakage omega‖ ≤ 1 := by
  rw [suzukiShiftedXiHardyLeakage]
  exact le_trans (norm_hardyLeakage_le _)
    (by simp)

end

end RHTower
