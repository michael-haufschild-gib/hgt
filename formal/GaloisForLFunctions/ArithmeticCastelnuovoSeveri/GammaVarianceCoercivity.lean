import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaVarianceCapacity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroEnergy
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolePreservingSmoothing

/-!
# Logarithmic Gamma payment of local oscillation

Every disjoint interval contributes its reciprocal-width logarithm times
its actual variance. No local mean-zero restriction is imposed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
open LogCells MeanZeroIntervals

/-- The original Gamma form pays the logarithmic cost of every local variance. -/
theorem levyEnergy_ge_sum_log_variance {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ i, a i < b i) (hw : ∀ i, b i - a i ≤ 1)
    (hsep : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ i, Real.log (1 / (b i - a i)) * intervalVariance (a i) (b i) f) ≤ levyEnergy f := by
  have hm (i : ι) : 0 ≤ intervalVariance (a i) (b i) f := intervalVariance_nonneg _ _ _
  have hl (i : ι) : 0 ≤ Real.log (1 / (b i - a i)) :=
    Real.log_nonneg ((one_le_div (sub_pos.mpr (hab i))).mpr (hw i))
  have h := gamma_coherent_variance_farCharge a b hab hsep
    (HTGeometry.measurable_of_boundedVariation_univ hv) (memLp_compact_bv hv hc)
  rw [gammaDifference_eq_two_levyEnergy hv hc] at h
  have hsmall : ENNReal.ofReal
      (∑ i, Real.log (1 / (b i - a i)) * intervalVariance (a i) (b i) f) ≤
      ∑ i, ENNReal.ofReal (intervalVariance (a i) (b i) f) *
        ∫⁻ y, gammaFarCharge (a i) (b i) y := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hl i) (hm i)]
    apply Finset.sum_le_sum
    intro i _hi
    rw [ENNReal.ofReal_mul (hl i), mul_comm]
    exact mul_le_mul_right (log_width_le_gammaFarCharge (hab i) (hw i)) _
  have htwo := (mul_le_mul_right hsmall 2).trans h
  have hcancel := (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp htwo
  exact (ENNReal.ofReal_le_ofReal_iff (levyEnergy_nonneg_bv hv hc)).mp hcancel

#print axioms levyEnergy_ge_sum_log_variance

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
