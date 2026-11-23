import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.TraceBound
import GaloisForLFunctions.HTGeometry.BlockDiagonalGap

/-! # Spectral gaps in the two heat moments

The squared amplitudes are the reciprocals of the positive integers.
A quadratic polynomial with roots at consecutive reciprocals is therefore
nonnegative on every occupation. Summing that inequality compares two
moments of an arbitrary wave.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Squared amplitude on occupation number `k+1`. -/
def occupationWeight (k : ℕ) : ℝ := attenuation (number k)^2

theorem occupationWeight_eq (k : ℕ) : occupationWeight k = ((k:ℝ)+1)⁻¹ := by
  rw [occupationWeight,attenuation,inv_pow,gain_sq]
  change ((↑(k+1):ℝ))⁻¹ = ((k:ℝ)+1)⁻¹
  rw [Nat.cast_add,Nat.cast_one]

theorem occupationWeight_pos (k : ℕ) : 0 < occupationWeight k :=
  sq_pos_of_pos (attenuation_pos _)

theorem occupationWeight_zero : occupationWeight 0 = 1 := by norm_num [occupationWeight_eq]

theorem occupationWeight_antitone : Antitone occupationWeight := by
  intro i j hij
  rw [occupationWeight_eq,occupationWeight_eq]
  have h : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
  exact inv_anti₀ (by positivity) (add_le_add h (le_refl 1))

theorem occupationWeight_tendsto : Tendsto occupationWeight atTop (𝓝 0) := by
  simp only [funext occupationWeight_eq]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))

private theorem gap_polynomial (k : ℕ) (n : ℕ+) :
    (occupationWeight k+occupationWeight (k+1))*attenuation n^2 ≤
      (attenuation n^2)^2+occupationWeight k*occupationWeight (k+1) := by
  obtain ⟨j,rfl⟩ := number_surjective n
  change (_+_)*occupationWeight j ≤ (occupationWeight j)^2+_*_
  have hgap : 0 ≤ (occupationWeight j-occupationWeight k)*(occupationWeight j-occupationWeight (k+1)) := by
    rcases le_or_gt j k with h | h
    · exact mul_nonneg (sub_nonneg.mpr (occupationWeight_antitone h))
        (sub_nonneg.mpr (occupationWeight_antitone (h.trans (Nat.le_succ k))))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (occupationWeight_antitone h.le))
        (sub_nonpos.mpr (occupationWeight_antitone h))
  linarith only [hgap]

private theorem weighted_coordinate (f : Gas) (n : ℕ+) :
    ‖criticalOperator f n‖^2 = attenuation n^2*‖f n‖^2 := by
  rw [critical_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le,mul_pow]

/-- Every pair of adjacent energy shells gives a quadratic-form inequality on the whole gas. -/
theorem occupation_moment_gap (k : ℕ) (f : Gas) :
    (occupationWeight k+occupationWeight (k+1))*‖criticalOperator f‖^2 ≤
      ‖squareHeat.val f‖^2+occupationWeight k*occupationWeight (k+1)*‖f‖^2 := by
  let a := occupationWeight k
  let b := occupationWeight (k+1)
  have h (n : ℕ+) : (a+b)*‖criticalOperator f n‖^2 ≤ ‖squareHeat.val f n‖^2+a*b*‖f n‖^2 := by
    change (a+b)*‖criticalOperator f n‖^2 ≤ ‖criticalOperator (criticalOperator f) n‖^2+a*b*‖f n‖^2
    rw [weighted_coordinate (criticalOperator f),weighted_coordinate]
    have hg := mul_le_mul_of_nonneg_right (gap_polynomial k n) (sq_nonneg ‖f n‖)
    change ((a+b)*attenuation n^2)*‖f n‖^2 ≤ ((attenuation n^2)^2+a*b)*‖f n‖^2 at hg
    simpa only [add_mul,pow_two (attenuation n^2),mul_assoc] using hg
  exact hasSum_le h ((HTGeometry.hasSum_sq_norm_lp (criticalOperator f)).mul_left (a+b))
    ((HTGeometry.hasSum_sq_norm_lp (squareHeat.val f)).add ((HTGeometry.hasSum_sq_norm_lp f).mul_left (a*b)))

#print axioms occupationWeight_tendsto
#print axioms occupation_moment_gap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
