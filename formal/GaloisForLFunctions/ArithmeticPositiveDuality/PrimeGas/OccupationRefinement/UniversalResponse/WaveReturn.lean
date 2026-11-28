import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Interference
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate.Readout

/-! # Interference with the actual no-emission output on an arbitrary wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Filter Topology ModeCapacities CoherentRay
open scoped NNReal

def waveReturn (A : Response) (f : Gas) (t : ℝ≥0) :=
  (inner ℂ f (evolution A t f)).re

theorem wave_weighted (A : Response) (f : Gas) (t : ℝ≥0) :
    waveReturn A f t = weightedReturn A (fun n => ‖f n‖ ^ 2) t := by
  symm
  apply HasSum.tsum_eq
  refine (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) f (evolution A t f))).congr_fun fun n => ?_
  rw [RCLike.inner_apply, evolution_apply, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem wave_origin (A : Response) (f : Gas) : waveReturn A f 0 = ‖f‖ ^ 2 := by
  rw [wave_weighted, weighted_zero, (EmissionRate.mass_sum f).tsum_eq]

/-- Every wave with a nonvacuum component distinguishes continuous powers
from all other conserving responses. Vacuum support is the unique exception. -/
theorem wave_iff (A : Response) (f : Gas) :
    ContinuousAt (waveReturn A f) 0 ↔
      (∀ n : ℕ+, 0 < energy n → f n = 0) ∨
      ∃! s : Conserving, ∀ x ∈ Shares, A.val x = power s.val x := by
  rw [show waveReturn A f = weightedReturn A (fun n => ‖f n‖ ^ 2) from funext (wave_weighted A f)]
  by_cases vacuumOnly : ∀ n : ℕ+, 0 < energy n → f n = 0
  · have allTime (t : ℝ≥0) : weightedReturn A (fun n => ‖f n‖ ^ 2) t = ‖f‖ ^ 2 := by
      rw [weightedReturn, ← (EmissionRate.mass_sum f).tsum_eq]
      apply tsum_congr
      intro n
      by_cases hn : 0 < energy n
      · rw [vacuumOnly n hn, norm_zero, zero_pow two_ne_zero, mul_zero]
      · have zero := le_antisymm (not_lt.mp hn) (EmissionRate.energy_nonneg n)
        rw [survivalAmplitude, zero, mul_zero, Real.exp_zero, response_at_one, Complex.one_re, one_mul]
    rw [show weightedReturn A (fun n => ‖f n‖ ^ 2) = fun _ => ‖f‖ ^ 2 from funext allTime]
    exact ⟨fun _ => Or.inl vacuumOnly,fun _ => continuousAt_const⟩
  · have existsMode : ∃ n : ℕ+, 0 < energy n ∧ 0 < ‖f n‖ ^ 2 := by
      by_contra! h
      exact vacuumOnly fun n hn => norm_eq_zero.mp ((sq_eq_zero_iff).mp
        (le_antisymm (h n hn) (sq_nonneg _)))
    rw [or_iff_right vacuumOnly]
    exact weighted_iff A (fun _ => sq_nonneg _) (EmissionRate.mass_sum f).summable existsMode

#print axioms wave_weighted
#print axioms wave_origin
#print axioms wave_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
