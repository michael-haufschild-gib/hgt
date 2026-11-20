import GaloisForLFunctions.goldbach.LiLiu.OperatorSpectralBounds
import GaloisForLFunctions.goldbach.LiLiu.SingularDensity

/-! # The target-dependent scales of the two spectral hypotheses -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter
open scoped Topology
noncomputable section

/-- Squared scale δ² = S(N) (log N)³ / N. -/
def spectralScale (N : ℕ) : ℝ := Real.sqrt (singularSeries N * Real.log N ^ 3 / N)

/-- Width in the open half-space prescribed by S(h). -/
def exclusionWidth (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  h N ^ 2 * Real.log N ^ 3 / ((N : ℝ) * singularSeries N)

theorem spectralScale_pos {N : ℕ} (hN : 1 < N) : 0 < spectralScale N :=
  Real.sqrt_pos.mpr (div_pos (mul_pos (singularSeries_pos _)
    (pow_pos (Real.log_pos (by exact_mod_cast hN)) _)) (by exact_mod_cast (by omega : 0 < N)))

theorem spectralScale_sq (N : ℕ) :
    spectralScale N ^ 2 = singularSeries N * Real.log N ^ 3 / N := by
  apply Real.sq_sqrt
  exact div_nonneg (mul_nonneg (singularSeries_pos _).le
    (pow_nonneg (Real.log_natCast_nonneg N) _)) (Nat.cast_nonneg N)

theorem spectralScale_eq_paper (N : ℕ) :
    spectralScale N = Real.sqrt (singularSeries N / N) * Real.log N ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = (3 : ℕ) * (1 / 2 : ℝ) by norm_num,
    Real.rpow_mul (Real.log_natCast_nonneg N), Real.rpow_natCast, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (div_nonneg (singularSeries_pos _).le (Nat.cast_nonneg _))]
  unfold spectralScale
  congr 1
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Substitution of the prescribed width gives a bound with absolute constant one. -/
theorem norm_le_singularSeries_div_of_exclusion {N : ℕ} (hN : 1 < N) {h : ℕ → ℝ} (hh : 0 < h N)
    (hw : exclusionWidth h N ≤ 1 / 4)
    {T : H →L[ℂ] H} [Fact (IsCompactOperator T)] (hs : T.IsSymmetric)
    (hex : ∀ z : ℂ, 1 - exclusionWidth h N < z.re → spectralProduct T (spectralScale N) z ≠ 0) :
    ‖T‖ ≤ singularSeries N / h N := by
  have hS := singularSeries_pos N
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N ^ 3 := pow_pos (Real.log_pos (by exact_mod_cast hN)) _
  have hη : 0 < exclusionWidth h N := div_pos (mul_pos (sq_pos_of_pos hh) hL) (mul_pos hNr hS)
  have hb := norm_bound_of_zeroFree hs (spectralScale_pos hN) hη (by linarith only [hw]) hex
  have hle : ‖T‖ ^ 2 * exclusionWidth h N ≤ spectralScale N ^ 2 := by
    have hmul := mul_nonneg (mul_nonneg (sq_nonneg ‖T‖) hη.le)
      (show 0 ≤ 4 * (1 - exclusionWidth h N) - 1 by linarith only [hw])
    linarith only [hb, hmul]
  rw [spectralScale_sq, exclusionWidth, ← mul_div_assoc, le_div_iff₀ hNr] at hle
  have hre : ‖T‖ ^ 2 * (h N ^ 2 * Real.log N ^ 3) / ((N : ℝ) * singularSeries N) * N =
      (‖T‖ * h N) ^ 2 * Real.log N ^ 3 / singularSeries N := by
    field_simp [hNr.ne', hS.ne']
  rw [hre, div_le_iff₀ hS] at hle
  have hsq : (‖T‖ * h N) ^ 2 ≤ singularSeries N ^ 2 :=
    (mul_le_mul_iff_left₀ hL).mp (by linarith only [hle])
  exact (le_div_iff₀ hh).mpr (le_of_sq_le_sq hsq hS.le)

/-- Critical-line zeros exclude every admissible open half-space. -/
theorem zeroFree_of_critical {N : ℕ} {h : ℕ → ℝ} (hw : exclusionWidth h N ≤ 1 / 4)
    {T : H →L[ℂ] H} [Fact (IsCompactOperator T)]
    (hc : ∀ z : ℂ, spectralProduct T (spectralScale N) z = 0 → z.re = 1 / 2) :
    ∀ z : ℂ, 1 - exclusionWidth h N < z.re → spectralProduct T (spectralScale N) z ≠ 0 := by
  intro z hz hf
  linarith only [hz, hc z hf, hw]

#print axioms norm_le_singularSeries_div_of_exclusion
#print axioms zeroFree_of_critical
end
end GaloisForLFunctions.Goldbach.LiLiu
