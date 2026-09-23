import GaloisForLFunctions.RHTower.Sieve.PrimeWindowSharpLevel

/-!
# The mean square is translation invariant

A shift of the frequency multiplies each coefficient of a Dirichlet polynomial by a unimodular
factor, so every mean-square bound holds on *every* interval of the admissible length, not only on
the one centred at the origin.

This is what lets a vertical integral be cut into cells: the mean square of the polynomial is the
same on each cell, and only the envelope varies.
-/

noncomputable section

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Translating the frequency twists the coefficients.** -/
theorem logPoly_add_right (a : ℕ → ℂ) (s : Finset ℕ) (u w : ℝ) :
    logPoly a s (w + u)
      = logPoly (fun n => a n
          * Complex.exp (((2 * Real.pi * (u * Real.log n) : ℝ) : ℂ) * Complex.I)) s w := by
  rw [logPoly, logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsplit : ((2 * Real.pi * ((w + u) * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * (u * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I
        + ((2 * Real.pi * (w * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  ring

/-- The twist does not change the coefficients' sizes. -/
theorem norm_twist (a : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    ‖a n * Complex.exp (((2 * Real.pi * (u * Real.log n) : ℝ) : ℂ) * Complex.I)‖ = ‖a n‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The sharp prime mean square on an arbitrary cell.**  The bound of
`integral_Icc_normSq_logPoly_le_prime_sharp` holds on every interval of the admissible length. -/
theorem integral_Icc_normSq_logPoly_shift_le_prime_sharp (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m.Prime) (u : ℝ) {W : ℝ} (hW0 : 0 ≤ W) (hW : 2 * Real.pi * 1 * W ≤ 1) :
    (∫ w in Set.Icc (u - W) (u + W), ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / 4) * ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖a q‖ ^ (2 : ℕ) := by
  set b : ℕ → ℂ := fun n => a n
    * Complex.exp (((2 * Real.pi * (u * Real.log n) : ℝ) : ℂ) * Complex.I) with hb
  have hWle : u - W ≤ u + W := by linarith
  have hWle' : -W ≤ W := by linarith
  -- move to the interval integral and translate
  have hstep1 : (∫ w in Set.Icc (u - W) (u + W), ‖logPoly a s w‖ ^ (2 : ℕ))
      = ∫ w in (u - W)..(u + W), ‖logPoly a s w‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le hWle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hshift : (∫ w in (-W)..W, ‖logPoly a s (w + u)‖ ^ (2 : ℕ))
      = ∫ w in (u - W)..(u + W), ‖logPoly a s w‖ ^ (2 : ℕ) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := -W) (b := W) (fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ)) u
    rw [h]
    congr 1 <;> ring
  have hcongr : (∫ w in (-W)..W, ‖logPoly a s (w + u)‖ ^ (2 : ℕ))
      = ∫ w in (-W)..W, ‖logPoly b s w‖ ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr ?_
    intro w _
    simp only []
    rw [logPoly_add_right a s u w, hb]
  have hstep2 : (∫ w in (-W)..W, ‖logPoly b s w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-W) W, ‖logPoly b s w‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le hWle', MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hmain := integral_Icc_normSq_logPoly_le_prime_sharp b s hs hW
  have hnorms : ∀ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖b q‖ ^ (2 : ℕ)
      = (700 * ((q : ℝ) / Real.log q) + 1) * ‖a q‖ ^ (2 : ℕ) := by
    intro q _
    rw [hb, norm_twist]
  rw [Finset.sum_congr rfl hnorms] at hmain
  rw [hstep1, ← hshift, hcongr, hstep2]
  exact hmain

end RHTower.Sieve

end
