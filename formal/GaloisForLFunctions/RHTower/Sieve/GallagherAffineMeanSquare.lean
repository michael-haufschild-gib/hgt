import GaloisForLFunctions.RHTower.Sieve.GallagherMeanValue
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail
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
    (∫ w in Set.Icc (-W) W, ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ))
      ≤ (2 * Real.pi)⁻¹
        * (5 * Real.pi * Real.exp 1
              * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
              * max (2 * Real.pi * W) 1) := by
  rw [integral_Icc_normSq_logPoly_eq a N hW]
  exact mul_le_mul_of_nonneg_left
    (integral_Icc_normSq_dirPoly_le_affine_max (fun n : Fin N => a ((n : ℕ) + 1))
      (2 * Real.pi * W)) (by positivity)

/-- **Gallagher's short-interval mean square with the affine frequency mean square.** -/
theorem gallagher_meanValue_le_affine (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    (∫ u : ℝ, ‖logWindowSum a (Finset.Icc 1 N) δ u‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((2 * Real.pi)⁻¹
            * (5 * Real.pi * Real.exp 1
                  * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
              + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
                * max (2 * Real.pi * W) 1))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) * (2 / (Real.pi ^ (2 : ℕ) * W)) := by
  have hI := integral_Icc_normSq_logPoly_le_affine a N hW.le
  have hM₂ : ∀ w : ℝ, ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ)
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) := by
    intro w
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a (Finset.Icc 1 N) w) 2
  exact gallagher_split_integral a (Finset.Icc 1 N) hδ hW (by positivity) hI hM₂

/-- **The affine majorant of the frequency mean square.**  `max(2πT, 1) ≤ 2πT + 1` turns the affine
form into the shape the dyadic tail consumes, with no condition on `W` beyond positivity. -/
theorem integral_Icc_normSq_logPoly_le_affine_majorant (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ)) * T
        + ((5 * Real.exp 1 / 2) * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
          + (5 / 4) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))) := by
  have hS : (0 : ℝ) ≤ ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hW' : (0 : ℝ) ≤ ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hbase := integral_Icc_normSq_logPoly_le_affine a N hT
  have hmax : max (2 * Real.pi * T) 1 ≤ 2 * Real.pi * T + 1 := by
    refine max_le ?_ ?_
    · have : (0 : ℝ) ≤ 2 * Real.pi * T := by positivity
      linarith
    · have : (0 : ℝ) ≤ 2 * Real.pi * T := by positivity
      linarith
  have hstep : (2 * Real.pi)⁻¹
        * (5 * Real.pi * Real.exp 1
              * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
              * max (2 * Real.pi * T) 1)
      ≤ (2 * Real.pi)⁻¹
        * (5 * Real.pi * Real.exp 1
              * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
              * (2 * Real.pi * T + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmul : (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
          * max (2 * Real.pi * T) 1
        ≤ (5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ)) * (2 * Real.pi * T + 1) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    linarith
  refine le_trans (le_trans hbase hstep) (le_of_eq ?_)
  field_simp
  ring

/-- **Gallagher's dyadic tail with the affine mean square.**  The rate is `(5π/2)` times the plain
mass and the constant is `(5e/2)` times the `n`-weighted mass, where the previous instance carried
`4N(1 + log N)/π` times the plain mass. -/
theorem gallagher_meanValue_dyadic_le_affine (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ)
    (hW : 0 < W) :
    (∫ u : ℝ, ‖logWindowSum a (Finset.Icc 1 N) δ u‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ)) * W
            + ((5 * Real.exp 1 / 2)
                * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
              + (5 / 4) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))))
        + (4 * ((5 * Real.pi / 2) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))) / (Real.pi ^ (2 : ℕ) * W)
            + 4 * ((5 * Real.exp 1 / 2)
                  * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
                + (5 / 4) * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ)))
              / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))) := by
  refine gallagher_split_integral_dyadic a (Finset.Icc 1 N) hδ hW ?_
  intro T hT
  exact integral_Icc_normSq_logPoly_le_affine_majorant a N (le_trans hW.le hT)

end RHTower.Sieve
end
