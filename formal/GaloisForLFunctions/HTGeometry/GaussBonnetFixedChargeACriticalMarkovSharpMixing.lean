import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovPowers

/-!
Sharpness of mixing for the Markov kernel derived from the critical Gibbs
profile of arXiv:2609.00025. Diagonal transition entries attain the complete
uniform error bound and isolate the exact leading relaxation rate.
-/
namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- Diagonal transitions attain the sum of both decaying harmonic amplitudes. -/
theorem egbFixedChargeACriticalMarkovMatrix_diagonal_error
    (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    (2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i i).re - 1 =
      2 * (2 / 3 : ℝ) ^ (m + 1) + 2 * (1 / 6 : ℝ) ^ (m + 1) := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_real]
  simp only [sub_self, mul_zero, Real.cos_zero, mul_one]
  ring

/-- Exact classification of every uniform entrywise error bound. -/
theorem egbFixedChargeACriticalMarkovMatrix_sharp_bound
    (n m : ℕ) (B : ℝ) :
    (∀ i j : Fin (2 ^ (n + 3)),
      |(2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re - 1| ≤ B) ↔
        2 * (2 / 3 : ℝ) ^ (m + 1) + 2 * (1 / 6 : ℝ) ^ (m + 1) ≤ B := by
  constructor
  · intro h
    have hd := h 0 0
    rw [egbFixedChargeACriticalMarkovMatrix_diagonal_error, abs_of_nonneg (by positivity)] at hd
    exact hd
  · intro h i j
    exact (egbFixedChargeACriticalMarkovMatrix_mixing_bound n m i j).trans h

/-- Dividing by the slow rate leaves an explicit quarter-rate correction. -/
theorem egbFixedChargeACriticalMarkovMatrix_scaled_diagonal_error
    (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    ((2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i i).re - 1) /
      (2 / 3 : ℝ) ^ (m + 1) = 2 + 2 * (1 / 4 : ℝ) ^ (m + 1) := by
  rw [egbFixedChargeACriticalMarkovMatrix_diagonal_error]
  have he : (1 / 6 : ℝ) ^ (m + 1) =
      (1 / 4 : ℝ) ^ (m + 1) * (2 / 3 : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    norm_num
  rw [he]
  field_simp
  <;> ring

/-- The leading mixing coefficient is exactly two, independently of grid size. -/
theorem egbFixedChargeACriticalMarkovMatrix_scaled_diagonal_limit
    (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    Tendsto (fun m : ℕ =>
      ((2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i i).re - 1) /
        (2 / 3 : ℝ) ^ (m + 1)) atTop (𝓝 2) := by
  have h : Tendsto (fun m : ℕ => (1 / 4 : ℝ) ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hc := (h.const_mul 2).const_add 2
  simpa only [egbFixedChargeACriticalMarkovMatrix_scaled_diagonal_error,
    mul_zero, add_zero] using hc

/-- The transition error cannot be little-o of the slow Fourier rate. -/
theorem egbFixedChargeACriticalMarkovMatrix_not_faster
    (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    ¬ Tendsto (fun m : ℕ =>
      ((2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i i).re - 1) /
        (2 / 3 : ℝ) ^ (m + 1)) atTop (𝓝 0) := by
  intro h
  have he := tendsto_nhds_unique (egbFixedChargeACriticalMarkovMatrix_scaled_diagonal_limit n i) h
  norm_num at he

end

end GaloisForLFunctions.HTGeometry
