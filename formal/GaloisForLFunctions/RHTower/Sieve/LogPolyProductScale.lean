import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly
import GaloisForLFunctions.RHTower.Sieve.DirichletPowerProductSplit

/-!
# Products of Gallagher polynomials, in Dirichlet-polynomial coordinates

The frequency mean square of a *product* of two Gallagher polynomials is the rescaled mean square
of the corresponding product of Dirichlet polynomials, by the same substitution `t = 2πw` that
`integral_Icc_normSq_logPoly_eq` uses for a single factor.  Restricting a Gallagher polynomial to a
subset of its index range is free — extend the coefficients by zero.

Together these put the threshold split and the free-exponent large-values estimate at the disposal
of the Ramaré ladder, whose blocks are Gallagher polynomials over finite sets of primes.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The substitution `t = 2πw` on a symmetric interval. -/
theorem integral_Icc_comp_scale (g : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, g (2 * Real.pi * w))
      = (2 * Real.pi)⁻¹ * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W), g t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : -W ≤ W := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_comp_mul_left g (ne_of_gt hpi)]
  have hsub : (∫ t in (2 * Real.pi * -W : ℝ)..(2 * Real.pi * W), g t)
      = ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W), g t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith : -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
    congr 1
    ring
  rw [hsub, smul_eq_mul]

/-- Restricting the index set of a Gallagher polynomial is a zero extension of its coefficients. -/
theorem logPoly_restrict (a : ℕ → ℂ) {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.Icc 1 N) (w : ℝ) :
    logPoly a S w = logPoly (fun n => if n ∈ S then a n else 0) (Finset.Icc 1 N) w := by
  classical
  rw [logPoly, logPoly]
  have h1 : ∀ n ∈ S, a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)
      = (if n ∈ S then a n else 0)
        * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) := by
    intro n hn
    rw [if_pos hn]
  rw [Finset.sum_congr rfl h1]
  exact Finset.sum_subset hS (fun n _ hn => by rw [if_neg hn, zero_mul])

/-- **The mean square of a product of Gallagher polynomials, rescaled.** -/
theorem integral_Icc_normSq_logPoly_mul_eq (a b : ℕ → ℂ) (N₁ N₂ : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly a (Finset.Icc 1 N₁) w * logPoly b (Finset.Icc 1 N₂) w‖ ^ (2 : ℕ))
      = (2 * Real.pi)⁻¹ * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W),
          ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ)
            * ‖dirPoly N₂ (fun n : Fin N₂ => b ((n : ℕ) + 1)) t‖ ^ (2 : ℕ) := by
  set g : ℝ → ℝ := fun t =>
    ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ)
      * ‖dirPoly N₂ (fun n : Fin N₂ => b ((n : ℕ) + 1)) t‖ ^ (2 : ℕ) with hgdef
  have hpt : ∀ w : ℝ,
      ‖logPoly a (Finset.Icc 1 N₁) w * logPoly b (Finset.Icc 1 N₂) w‖ ^ (2 : ℕ)
        = g (2 * Real.pi * w) := by
    intro w
    rw [hgdef, norm_mul, mul_pow, logPoly_eq_dirPoly a N₁ w, logPoly_eq_dirPoly b N₂ w]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun w _ => hpt w)]
  exact integral_Icc_comp_scale g hW

/-- **The threshold split for a product of Gallagher polynomials, at a free exponent.**  The second
factor is prime-supported, so its exceptional set is measured with no power of its length. -/
theorem integral_Icc_normSq_logPoly_mul_le_pow_prime_support (a b : ℕ → ℂ) (N₁ N₂ : ℕ)
    (k : ℕ) (hk : 1 ≤ k)
    (hsupp : ∀ n : Fin N₂, b ((n : ℕ) + 1) ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {W V Bf Bg : ℝ} (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hBf : ∀ t : ℝ, ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ≤ Bf)
    (hBg : ∀ t : ℝ, ‖dirPoly N₂ (fun n : Fin N₂ => b ((n : ℕ) + 1)) t‖ ≤ Bg) :
    V ^ (2 * k) * (∫ w in Set.Icc (-W) W,
        ‖logPoly a (Finset.Icc 1 N₁) w * logPoly b (Finset.Icc 1 N₂) w‖ ^ (2 : ℕ))
      ≤ (2 * Real.pi)⁻¹
          * (V ^ (2 * k + 2)
              * (∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W),
                  ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ))
            + Bf ^ (2 : ℕ) * Bg ^ (2 : ℕ)
              * (2 * ((2 * Real.pi * W
                    + 4 * ((N₂ ^ k : ℕ) : ℝ) * (1 + Real.log ((N₂ ^ k : ℕ) : ℝ)))
                  * ((k : ℝ) ^ k
                    * (∑ n : Fin N₂, ‖b ((n : ℕ) + 1)‖ ^ (2 : ℕ)) ^ k)))) := by
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hWt : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
  have hbase := integral_normSq_mul_symm_le_pow_prime_support N₁ N₂
    (fun n : Fin N₁ => a ((n : ℕ) + 1)) (fun n : Fin N₂ => b ((n : ℕ) + 1)) k hk hsupp
    (T := 2 * Real.pi * W) hWt hV hBf hBg
  rw [integral_Icc_normSq_logPoly_mul_eq a b N₁ N₂ hW]
  have hmul := mul_le_mul_of_nonneg_left hbase hpi.le
  calc V ^ (2 * k) * ((2 * Real.pi)⁻¹
        * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W),
            ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ)
              * ‖dirPoly N₂ (fun n : Fin N₂ => b ((n : ℕ) + 1)) t‖ ^ (2 : ℕ))
      = (2 * Real.pi)⁻¹ * (V ^ (2 * k)
          * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W),
              ‖dirPoly N₁ (fun n : Fin N₁ => a ((n : ℕ) + 1)) t‖ ^ (2 : ℕ)
                * ‖dirPoly N₂ (fun n : Fin N₂ => b ((n : ℕ) + 1)) t‖ ^ (2 : ℕ)) := by ring
    _ ≤ _ := hmul

end RHTower.Sieve
