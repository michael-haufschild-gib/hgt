import GaloisForLFunctions.BiarithmeticGeometry.PowerTailCoefficients
import GaloisForLFunctions.BiarithmeticGeometry.CriticalGoldenClosure

/-!
# The power-tail family inside actual critical golden payment

Each positive tail exponent gives a norm-two critical Wiener kernel with
zero evaluation. Every such kernel lies in the closure of the actual paid
ideal, and it belongs to the ideal exactly above the half-exponent threshold.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem summable_norm_complexCriticalPowerCoeff (α : ℝ) (hα : 0 < α) :
    Summable (fun r => ‖(criticalPowerCoeff α r : ℂ)‖) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using summable_abs_criticalPowerCoeff α hα.le

/-- The actual critical Wiener kernel attached to a positive power-tail exponent. -/
def powerTailWiener (α : ℝ) (hα : 0 < α) : WienerAlgebraAt (1 / 2) :=
  fiveComplexCriticalWienerLift (fun r => (criticalPowerCoeff α r : ℂ))
    (summable_norm_complexCriticalPowerCoeff α hα)

theorem powerTailWiener_pow (α : ℝ) (hα : 0 < α) (r : ℕ) :
    (powerTailWiener α hα).toFn (5 ^ r) =
      (Real.sqrt 5 : ℂ) ^ r * (criticalPowerCoeff α r : ℂ) :=
  fiveComplexCriticalWienerLift_pow _ _ r

theorem powerTailWiener_off_support (α : ℝ) (hα : 0 < α) (n : ℕ)
    (hn : n ∉ Set.range (fun r : ℕ => 5 ^ r)) :
    (powerTailWiener α hα).toFn n = 0 :=
  fiveComplexCriticalWienerLift_off_support _ _ n hn

/-- Every positive exponent has actual Wiener norm two. -/
theorem norm_powerTailWiener (α : ℝ) (hα : 0 < α) : ‖powerTailWiener α hα‖ = 2 := by
  rw [powerTailWiener, norm_fiveComplexCriticalWienerLift]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact tsum_abs_criticalPowerCoeff α hα

/-- Actual critical golden payment has the exact half-exponent boundary on this family. -/
theorem powerTailWiener_mem_paidIdeal_iff (α : ℝ) (hα : 0 < α) :
    powerTailWiener α hα ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) ↔ (1 : ℝ) / 2 < α := by
  rw [powerTailWiener, mem_golden_critical_fiveComplexCriticalWienerLift_iff]
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact summable_sq_criticalPowerCoeff_partialSum_iff α

/-- Every member lies in the full actual payment closure, including the unpaid exponent interval. -/
theorem powerTailWiener_mem_closure_paidIdeal (α : ℝ) (hα : 0 < α) :
    powerTailWiener α hα ∈ closure
      ((paidIdeal (goldenArithmeticSource goldenCriticalParameter)
        (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
          goldenCriticalParameter_bounds.2.le)) : Set (WienerAlgebraAt (1 / 2))) := by
  apply fiveComplexCriticalWienerLift_mem_closure_paidIdeal
  have hs := Complex.ofRealCLM.hasSum (summable_abs_criticalPowerCoeff α hα.le).of_abs.hasSum
  change HasSum (fun r => (criticalPowerCoeff α r : ℂ))
    ((∑' r, criticalPowerCoeff α r : ℝ) : ℂ) at hs
  rw [tsum_criticalPowerCoeff α hα, Complex.ofReal_zero] at hs
  exact hs.tsum_eq

end GaloisForLFunctions.BiarithmeticGeometry

