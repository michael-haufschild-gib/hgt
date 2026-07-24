import GaloisForLFunctions.RHTower.XiWardIntegerWindowMassCriterion
import GaloisForLFunctions.RHTower.XiWardZeroFreeMarginPrimeLogSampling

/-!
# The Ward edge measure and the quantitative Schur defect

The nonnegative edge density `Re r` of the continued Ward response defines a
positive Borel measure on the Euler edge.  Its total mass is the quantized
count `4π` per strict-right pair, its integer-window masses are the localized
detectors, and RH is exactly its vanishing as a measure.

At the adapted node of any strict-right pair the one-node four-unit Schur
defect is moreover quantitatively negative: at most `-8` times the zero-free
margin at the pair's height.  Failure of `W_P`-positivity is therefore bounded
away from zero by an a-priori polylogarithmic amount.
-/

open Complex Filter MeasureTheory Real
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The Ward edge measure: the positive boundary measure with density `Re r`
along the Euler edge. -/
def xiWardEdgeMeasure : Measure ℝ :=
  volume.withDensity fun t =>
    ENNReal.ofReal
      ((continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re)

/-- The total Ward edge mass is the quantized pair count. -/
theorem xiWardEdgeMeasure_univ :
    xiWardEdgeMeasure Set.univ =
      ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (4 * π) := by
  rw [xiWardEdgeMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    MeasureTheory.setLIntegral_univ]
  exact lintegral_re_continuedXiAntiCausalWardResponse_eulerEdge

/-- The integer-window masses are the measures of the integer windows. -/
theorem xiWardEdgeMeasure_integerWindow (k : ℤ) :
    xiWardEdgeMeasure (Set.Ioc ((k : ℝ) - 1) ((k : ℝ) + 1)) =
      xiWardIntegerWindowMass k := by
  rw [xiWardEdgeMeasure, MeasureTheory.withDensity_apply _ measurableSet_Ioc]
  rfl

/-- **RH as vanishing of one positive measure.** -/
theorem riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero :
    RiemannHypothesis ↔ xiWardEdgeMeasure = 0 := by
  constructor
  · intro hRH
    have hpt : (fun t : ℝ =>
        ENNReal.ofReal
          ((continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))).re)) = fun _ => 0 := by
      funext t
      have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
        norm_num [Complex.add_re, Complex.mul_re]
      rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
        hRH hw]
      simp
    rw [xiWardEdgeMeasure, hpt]
    exact MeasureTheory.withDensity_zero
  · intro h0
    rw [riemannHypothesis_iff_forall_xiWardIntegerWindowMass_eq_zero]
    intro k
    rw [← xiWardEdgeMeasure_integerWindow, h0]
    simp

/-- **Quantitative Schur defect law.**  At the adapted node of a strict-right
pair, the one-node four-unit Schur defect of `W_P` is strictly below `-8`
times the zero-free margin at the pair's height: PSD failure is bounded away
from zero by an a-priori polylogarithmic amount. -/
theorem continuedXiWardFourUnitSchurDefect_adaptedNode_re_lt_neg_margin
    (q : XiRightUpperZeroCopy) :
    (continuedXiWardFourUnitSchurDefect
      (fun _ : Fin 1 =>
        (1 / 2 : ℂ) + I * ((-(xiRightCenteredZero q.1).im : ℝ) : ℂ)) 0 0).re <
      -(8 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) := by
  set node : ℂ :=
    (1 / 2 : ℂ) + I * ((-(xiRightCenteredZero q.1).im : ℝ) : ℂ) with hnodedef
  set r : ℂ := continuedXiAntiCausalWardResponse node with hrdef
  have hnorm : 4 + 8 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im <
      Complex.normSq r := by
    have h := normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_relaxed q
    rw [xiWardZeroFreeMargin_neg] at h
    rw [hrdef, hnodedef]
    exact h
  change (4 * (1 / (node + star node)) - r * star r).re <
    -(8 * xiWardZeroFreeMargin (xiRightCenteredZero q.1).im)
  have hden : node + star node = (1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, RCLike.star_def, Complex.conj_re,
        Complex.one_re]
      rw [hnodedef]
      norm_num [Complex.add_re, Complex.mul_re]
    · simp only [Complex.add_im, RCLike.star_def, Complex.conj_im,
        Complex.one_im]
      ring
  rw [hden, div_one]
  rw [show r * star r = (Complex.normSq r : ℂ) from Complex.mul_conj r]
  norm_num
  linarith

end

end RHTower
