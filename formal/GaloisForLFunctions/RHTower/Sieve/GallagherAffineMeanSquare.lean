import GaloisForLFunctions.RHTower.Sieve.GallagherMeanValue
import GaloisForLFunctions.RHTower.Sieve.DirichletPolyAffineMeanSquare

/-!
# Gallagher's base case with the affine mean square

The frequency mean square of the Gallagher polynomial is a rescaled Dirichlet-polynomial mean square,
so the affine estimate applies to it:

`∫_{|w| ≤ W} ‖logPoly a w‖² dw ≤ (2π)⁻¹(5πe∑_m(m+1)|a_{m+1}|² + (5π/2)(∑_m |a_{m+1}|²)·max(2πW, 1))`,

where the previous bound was `(2πW + 4N(1 + log N))/π · ∑_m |a_{m+1}|²`.  The height-linear parts agree
up to a constant; the height-free parts are `∑_m (m+1)|a_{m+1}|²` against `N(1 + log N)∑_m|a_{m+1}|²` —
a whole logarithm for coefficients of constant size, and a factor `N/k` when the mass sits below `k`.

`gallagher_split_integral` takes the frequency mean square as a parameter, so Gallagher's
short-interval bound inherits the improvement verbatim.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- **The frequency mean square of the Gallagher polynomial, affine form.** -/
theorem integral_Icc_normSq_logPoly_le_affine (a : ℕ → ℂ) (N : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a (Finset.Icc 1 N) w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * (5 * Real.pi * Real.exp 1
              * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ 2)
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2)
              * max (2 * Real.pi * W) 1) := by
  rw [integral_Icc_normSq_logPoly_eq a N hW]
  exact mul_le_mul_of_nonneg_left
    (integral_Icc_normSq_dirPoly_le_affine_max (fun n : Fin N => a ((n : ℕ) + 1))
      (2 * Real.pi * W)) (by positivity)

/-- **Gallagher's short-interval mean square with the affine frequency mean square.** -/
theorem gallagher_meanValue_le_affine (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    (∫ u : ℝ, ‖logWindowSum a (Finset.Icc 1 N) δ u‖ ^ 2)
      ≤ 2 * δ ^ 2
          * ((2 * Real.pi)⁻¹
            * (5 * Real.pi * Real.exp 1
                  * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ 2)
              + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2)
                * max (2 * Real.pi * W) 1))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2 * (2 / (Real.pi ^ 2 * W)) := by
  have hI := integral_Icc_normSq_logPoly_le_affine a N hW.le
  have hM₂ : ∀ w : ℝ, ‖logPoly a (Finset.Icc 1 N) w‖ ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2 := by
    intro w
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a (Finset.Icc 1 N) w) 2
  exact gallagher_split_integral a (Finset.Icc 1 N) hδ hW (by positivity) hI hM₂

end RHTower.Sieve
end
