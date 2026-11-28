import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Partition

/-! # Norm loss of the no-emission branch at a positive observation time -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate

open ModeCapacities Filter Topology

/-- Missing squared norm per unit time in the emitted-vacuum branch. -/
def loss (s : Conserving) (f : Gas) (t : Duration) : ℝ :=
  (‖f‖ ^ 2 - ‖noEmission s t f‖ ^ 2) / t.val

def increment (t E : ℝ) := (1 - Real.exp (-t * E)) / t

theorem increment_nonneg {t E : ℝ} (ht : 0 < t) (hE : 0 ≤ E) : 0 ≤ increment t E :=
  div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) hE))) ht.le

theorem increment_le {t : ℝ} (ht : 0 < t) (E : ℝ) : increment t E ≤ E := by
  apply (div_le_iff₀ ht).mpr
  linarith only [Real.add_one_le_exp (-t * E)]

theorem increment_limit (E : ℝ) : Tendsto (fun t => increment t E) (𝓝[>] 0) (𝓝 E) := by
  have deriv : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t * E)) E 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).neg.mul_const E).exp.const_sub 1)
  simpa only [increment, zero_add, neg_zero, zero_mul, Real.exp_zero, sub_self, sub_zero,
    smul_eq_mul, div_eq_inv_mul] using
    (hasDerivAt_iff_tendsto_slope_zero.mp deriv).mono_left (nhdsGT_le_nhdsNE 0)

theorem mass_sum (f : Gas) : HasSum (fun n : ℕ+ => ‖f n‖ ^ 2) (‖f‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (p := 2) (by norm_num) f

theorem energy_nonneg (n : ℕ+) : 0 ≤ energy n := Real.log_nonneg (by exact_mod_cast n.pos)

/-- At every duration the imaginary exponent disappears from each
coordinate probability, even on a superposition of infinitely many energies. -/
theorem coordinate_mass (s : Conserving) (f : Gas) (t : Duration) (n : ℕ+) :
    ‖noEmission s t f n‖ ^ 2 = Real.exp (-t.val * energy n) * ‖f n‖ ^ 2 := by
  rw [noEmission_apply, norm_mul, mul_pow, norm_heat, sq, ← Real.exp_add]
  congr 2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, s.property]
  ring

theorem loss_sum (s : Conserving) (f : Gas) (t : Duration) :
    HasSum (fun n : ℕ+ => increment t.val (energy n) * ‖f n‖ ^ 2) (loss s f t) := by
  apply (((mass_sum f).sub (mass_sum (noEmission s t f))).div_const t.val).congr_fun
  intro n
  rw [coordinate_mass, increment]
  ring

#print axioms increment_limit
#print axioms coordinate_mass
#print axioms loss_sum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate
