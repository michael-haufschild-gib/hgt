import GaloisForLFunctions.RHTower.XiGaussianWeightedFloorPhase

/-!
# The explicit three-node independent energy floor

The denominator retains all three heat rates and all nine squared cofactors.
This is a symbolic identity in arbitrary nodes; no zero heights or moment
values are approximated.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiThirdSamplingHeatDenominator (x y z t : ℝ) : ℝ :=
  (y - z) ^ 2 * (1 + (y + z) ^ 2 + (y * z) ^ 2) * Real.exp (t * x) +
    (x - z) ^ 2 * (1 + (x + z) ^ 2 + (x * z) ^ 2) * Real.exp (t * y) +
    (x - y) ^ 2 * (1 + (x + y) ^ 2 + (x * y) ^ 2) * Real.exp (t * z)

theorem polynomialSamplingHeatCapacity_three_real (x : Fin 3 → ℝ) (t : ℝ) :
    polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t =
      xiThirdSamplingHeatDenominator (x 0) (x 1) (x 2) t := by
  unfold polynomialSamplingHeatCapacity
  rw [Matrix.adjugate_fin_three]
  simp [Fin.sum_univ_three, Matrix.vandermonde_apply, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_neg,
    ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  unfold xiThirdSamplingHeatDenominator
  ring

/-- The exact closed form of the paired floor for the actual complete three-by-three form. -/
theorem xiCriticalSamplingHeatFloor_third (γ : Fin 3 → ℝ) (t : ℝ) :
    xiCriticalSamplingHeatFloor γ t =
      2 * ((γ 1 ^ 2 - γ 0 ^ 2) * (γ 2 ^ 2 - γ 0 ^ 2) *
        (γ 2 ^ 2 - γ 1 ^ 2)) ^ 2 /
          xiThirdSamplingHeatDenominator (γ 0 ^ 2) (γ 1 ^ 2) (γ 2 ^ 2) t := by
  have hdet : (Matrix.vandermonde (fun i => ((γ i : ℝ) : ℂ) ^ 2)).det =
      ((((γ 1 ^ 2 - γ 0 ^ 2) * (γ 2 ^ 2 - γ 0 ^ 2) *
        (γ 2 ^ 2 - γ 1 ^ 2)) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.vandermonde_apply]
    push_cast
    ring
  unfold xiCriticalSamplingHeatFloor
  rw [hdet]
  simp only [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [polynomialSamplingHeatCapacity_three_real]

end RHTower
