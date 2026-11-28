import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Interference
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ThermalPhaseAttainment

/-! # Interference trace of the emitted vacuum after Gibbs preparation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open ModeCapacities
open scoped NNReal

def prepared (A : Response) (β : TraceTemperature) (t : ℝ≥0) : Gas →L[ℂ] Gas :=
  evolution A t ∘L gibbsOperator ⟨(β.val:ℂ),β.property⟩

/-- Splitting the Gibbs preparation into two Hilbert–Schmidt factors
exhibits the physical trace for an arbitrary response, even without continuity. -/
theorem prepared_trace (A : Response) (β : TraceTemperature) (t : ℝ≥0) :
    ContinuousLinearMap.opTrace (prepared A β t) =
      ∑' n, survivalAmplitude A n t * (thermalWeight β n : ℂ) := by
  let h := heat ((β.val:ℂ)/2)
  have hs : Summable (fun n => ‖h n‖ ^ 2) := (summable_heat_sq_iff _).mpr (by
    rw [Complex.div_ofNat_re, Complex.ofReal_re]
    linarith only [β.property])
  let v (n : ℕ+) := survivalAmplitude A n t * h n
  have vs : Summable (fun n => ‖v n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) hs
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    exact (norm_mul _ _).le.trans (mul_le_of_le_one_left (norm_nonneg _) (survival_bound A n t))
  have pair (n : ℕ+) : h n * h n = heat (β.val:ℂ) n := by
    change heat _ n * heat _ n = _
    rw [← heat_add, add_halves]
  have factor : prepared A β t = HilbertSchmidt.diagOp v vs ∘L HilbertSchmidt.diagOp h hs := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    simp only [prepared, ContinuousLinearMap.comp_apply, evolution_apply, gibbsOperator_apply,
      HilbertSchmidt.diagOp_apply, v, mul_assoc, ← pair]
  rw [factor, HilbertSchmidt.opTrace_diagOp_comp]
  apply tsum_congr
  intro n
  rw [show v n * h n = survivalAmplitude A n t * heat (β.val:ℂ) n from
    (mul_assoc _ _ _).trans (congrArg _ (pair n))]
  congr 1
  rw [heat, thermalWeight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]

theorem prepared_real (A : Response) (β : TraceTemperature) (t : ℝ≥0) :
    (ContinuousLinearMap.opTrace (prepared A β t)).re = weightedReturn A (thermalWeight β) t := by
  have sm : Summable (fun n => survivalAmplitude A n t * (thermalWeight β n : ℂ)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (thermalWeight_summable β)
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (thermalWeight_pos β n).le]
    exact mul_le_of_le_one_left (thermalWeight_pos β n).le (survival_bound A n t)
  rw [prepared_trace, Complex.re_tsum sm, weightedReturn]
  exact tsum_congr fun n => by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem prepared_origin (A : Response) (β : TraceTemperature) :
    ContinuousLinearMap.opTrace (prepared A β 0) = riemannZeta (β.val:ℂ) := by
  rw [prepared_trace]
  simp only [survival_zero, one_mul, ← Complex.ofReal_tsum, thermalWeight_partition]

#print axioms prepared_trace
#print axioms prepared_real
#print axioms prepared_origin

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
