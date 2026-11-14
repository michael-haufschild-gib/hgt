import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianHeat
import GaloisForLFunctions.HTGeometry.RoundingVarianceFloor

/-!
# Exact continuous and discrete quadratic truncation scales

For a growing quadratic instanton family `exp (b*l² - N*A*l)` with `b = exp s`, completing the
square extracts the scale `exp (-(N*A)²/(4b))`. The remaining factor is the reciprocal of the
translated Gaussian centered at `N*A/(2b)`. Integer truncation is therefore a nearest-lattice-point
problem, including the half-integer ties.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Magnitude of a quadratic instanton sector with growing annulus factor. -/
def quadraticInstantonMagnitude (A s N l : ℝ) : ℝ :=
  Real.exp (Real.exp s * l ^ 2 - N * A * l)

/-- Continuous optimal instanton number. -/
def quadraticInstantonCenter (A s N : ℝ) : ℝ := N * A / (2 * Real.exp s)

/-- Exponential precision scale supplied by the continuous quadratic minimum. -/
def quadraticPrecisionScale (A s N : ℝ) : ℝ :=
  Real.exp (-((N * A) ^ 2 / (4 * Real.exp s)))

/-- The full sector magnitude splits into its least scale and a Gaussian reciprocal. -/
theorem quadraticInstantonMagnitude_factorization (A s N l : ℝ) :
    quadraticInstantonMagnitude A s N l = quadraticPrecisionScale A s N *
      Real.exp (Real.exp s * (l - quadraticInstantonCenter A s N) ^ 2) := by
  unfold quadraticInstantonMagnitude quadraticPrecisionScale quadraticInstantonCenter
  rw [← Real.exp_add]
  congr 1
  field_simp [Real.exp_ne_zero]
  ring

/-- The continuous precision scale bounds every individual term from below. -/
theorem quadraticPrecisionScale_le_term (A s N l : ℝ) :
    quadraticPrecisionScale A s N ≤ quadraticInstantonMagnitude A s N l := by
  rw [quadraticInstantonMagnitude_factorization]
  exact le_mul_of_one_le_right (Real.exp_pos _).le
    (Real.one_le_exp (mul_nonneg (Real.exp_pos s).le (sq_nonneg _)))

/-- The continuous minimum is attained at exactly the stationary instanton number. -/
theorem quadraticInstantonMagnitude_eq_scale_iff (A s N l : ℝ) :
    quadraticInstantonMagnitude A s N l = quadraticPrecisionScale A s N ↔
      l = quadraticInstantonCenter A s N := by
  have hscale : quadraticPrecisionScale A s N ≠ 0 := Real.exp_ne_zero _
  rw [quadraticInstantonMagnitude_factorization,
    mul_eq_left₀ hscale, Real.exp_eq_one_iff,
    mul_eq_zero, or_iff_right (Real.exp_ne_zero s), sq_eq_zero_iff, sub_eq_zero]

/-- The existing heat Gaussian is exactly the inverse normalized sector magnitude. -/
theorem quadraticInstantonMagnitude_mul_translatedGaussian (A s N l : ℝ) :
    quadraticInstantonMagnitude A s N l *
      RiemannGaussian.translatedGaussian (Real.exp s) (quadraticInstantonCenter A s N) l =
        quadraticPrecisionScale A s N := by
  rw [quadraticInstantonMagnitude_factorization, RiemannGaussian.translatedGaussian,
    mul_assoc, ← Real.exp_add]
  rw [show Real.exp s * (l - quadraticInstantonCenter A s N) ^ 2 +
      -(Real.exp s) * (l - quadraticInstantonCenter A s N) ^ 2 = 0 by ring,
    Real.exp_zero, mul_one]

/-- Rounding the stationary number gives a global minimum over every integer sector. -/
theorem quadraticInstantonMagnitude_round_min (A s N : ℝ) (l : ℤ) :
    quadraticInstantonMagnitude A s N (round (quadraticInstantonCenter A s N)) ≤
      quadraticInstantonMagnitude A s N l := by
  rw [quadraticInstantonMagnitude_factorization, quadraticInstantonMagnitude_factorization]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos s).le
  have h := _root_.HTGeometry.abs_sub_round_le_abs_sub (quadraticInstantonCenter A s N) l
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [sq_abs, sub_sq_comm] using hsq

/-- Integer truncation changes the continuous least term by at most `exp (b/4)`. -/
theorem quadraticInstantonMagnitude_round_bounds (A s N : ℝ) :
    quadraticPrecisionScale A s N ≤
        quadraticInstantonMagnitude A s N (round (quadraticInstantonCenter A s N)) ∧
      quadraticInstantonMagnitude A s N (round (quadraticInstantonCenter A s N)) ≤
        quadraticPrecisionScale A s N * Real.exp (Real.exp s / 4) := by
  refine ⟨quadraticPrecisionScale_le_term A s N _, ?_⟩
  rw [quadraticInstantonMagnitude_factorization]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (_root_.HTGeometry.sq_abs_sub_round_le (quadraticInstantonCenter A s N))
    (Real.exp_pos s).le
  simpa only [sq_abs, sub_sq_comm, mul_one_div] using h

/-- The same rounded integer maximizes the sampled heat Gaussian. -/
theorem translatedGaussian_round_max (s x : ℝ) (l : ℤ) :
    RiemannGaussian.translatedGaussian (Real.exp s) x l ≤
      RiemannGaussian.translatedGaussian (Real.exp s) x (round x) := by
  unfold RiemannGaussian.translatedGaussian
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (Real.exp_pos s).le)
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (_root_.HTGeometry.abs_sub_round_le_abs_sub x l) 2
  simpa only [sq_abs, sub_sq_comm] using h

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.quadraticInstantonMagnitude_factorization
#print axioms GaloisForLFunctions.HTGeometry.quadraticPrecisionScale_le_term
#print axioms GaloisForLFunctions.HTGeometry.quadraticInstantonMagnitude_eq_scale_iff
#print axioms GaloisForLFunctions.HTGeometry.quadraticInstantonMagnitude_mul_translatedGaussian
#print axioms GaloisForLFunctions.HTGeometry.quadraticInstantonMagnitude_round_min
#print axioms GaloisForLFunctions.HTGeometry.quadraticInstantonMagnitude_round_bounds
#print axioms GaloisForLFunctions.HTGeometry.translatedGaussian_round_max
