import GaloisForLFunctions.RHTower.Sieve.DirichletSymmSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

/-!
# The mean square of a factorized Dirichlet polynomial

A convolution of two coefficient vectors has a Dirichlet polynomial that factors, so the threshold
split applies to it directly.  Combining the split with the mean value theorem for the long factor
and the sixth-moment level-set bound for the short one gives, for every threshold `V`,

    V⁶∫_{|t| ≤ T}|(p*q)^(t)|²
      ≤ 2V⁸(T + 4N₁(1+log N₁))∑|p_j|²
        + 2(sup|P|)²(sup|Q|)²(T + 4N₂³(1+log N₂³))·D·(∑_k|q_k|²)³ .

Only the second factor is ever raised to the sixth power, so a short second factor with spread-out
coefficients — a prime-supported polynomial over a dyadic range — makes the exceptional term small
while the first term keeps the diagonal.  That asymmetry is the point of factorizing.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The threshold split for a factorized polynomial.** -/
theorem integral_Icc_normSq_dirConv_split (N₁ N₂ : ℕ) (p : Fin N₁ → ℂ) (q : Fin N₂ → ℂ)
    {T V Bf Bg : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N₁ p t‖ ≤ Bf)
    (hBg : ∀ t : ℝ, ‖dirPoly N₂ q t‖ ≤ Bg) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly (N₁ * N₂) (dirConv N₁ N₂ p q) t‖ ^ 2)
      ≤ V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly N₁ p t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N₂ q t‖} := by
  have hfac : ∀ t : ℝ, ‖dirPoly (N₁ * N₂) (dirConv N₁ N₂ p q) t‖ ^ 2
      = ‖dirPoly N₁ p t‖ ^ 2 * ‖dirPoly N₂ q t‖ ^ 2 := by
    intro t
    rw [← dirPoly_mul_eq_dirPoly N₁ N₂ p q t, norm_mul, mul_pow]
  simp only [hfac]
  exact integral_normSq_mul_split_symm N₁ N₂ p q hBf hBg

/-- **The mean square of a factorized Dirichlet polynomial.**  The long factor pays the diagonal of
the mean value theorem; the short one pays the sixth moment of its exceptional set. -/
theorem integral_Icc_normSq_dirConv_le (N₁ N₂ : ℕ) (p : Fin N₁ → ℂ) (q : Fin N₂ → ℂ)
    {T V Bf Bg D : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hBf : ∀ t : ℝ, ‖dirPoly N₁ p t‖ ≤ Bf) (hBg : ∀ t : ℝ, ‖dirPoly N₂ q t‖ ≤ Bg)
    (hD : ∀ j : Fin (N₂ ^ 3), ((cubeFibre N₂ j).card : ℝ) ≤ D) :
    V ^ 6 * (∫ t in Set.Icc (-T) T, ‖dirPoly (N₁ * N₂) (dirConv N₁ N₂ p q) t‖ ^ 2)
      ≤ V ^ 8 * (2 * ((T + 4 * (N₁ : ℝ) * (1 + Real.log N₁)) * ∑ j : Fin N₁, ‖p j‖ ^ 2))
        + Bf ^ 2 * Bg ^ 2
            * (2 * ((T + 4 * ((N₂ ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N₂ ^ 3 : ℕ) : ℝ)))
                * (D * (∑ k : Fin N₂, ‖q k‖ ^ 2) ^ 3))) := by
  have hsplit := integral_Icc_normSq_dirConv_split N₁ N₂ p q (V := V) (T := T) hBf hBg
  have hV6 : (0 : ℝ) ≤ V ^ 6 := by positivity
  have hV8 : (0 : ℝ) ≤ V ^ 8 := by positivity
  have hK : (0 : ℝ) ≤ Bf ^ 2 * Bg ^ 2 := by positivity
  have hlong := integral_Icc_normSq_dirPoly_symm_le N₁ p hT
  have hshort := volume_largeValues_sixth_symm_le N₂ q hT hV hD
  have hmul' : V ^ 6 * (∫ t in Set.Icc (-T) T, ‖dirPoly (N₁ * N₂) (dirConv N₁ N₂ p q) t‖ ^ 2)
      ≤ V ^ 8 * (∫ t in Set.Icc (-T) T, ‖dirPoly N₁ p t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * (V ^ 6 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N₂ q t‖}) := by
    calc V ^ 6 * (∫ t in Set.Icc (-T) T, ‖dirPoly (N₁ * N₂) (dirConv N₁ N₂ p q) t‖ ^ 2)
        ≤ V ^ 6 * (V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly N₁ p t‖ ^ 2)
            + Bf ^ 2 * Bg ^ 2
                * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N₂ q t‖}) :=
          mul_le_mul_of_nonneg_left hsplit hV6
      _ = V ^ 8 * (∫ t in Set.Icc (-T) T, ‖dirPoly N₁ p t‖ ^ 2)
            + Bf ^ 2 * Bg ^ 2
                * (V ^ 6 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N₂ q t‖}) := by
          ring
  have hlong' := mul_le_mul_of_nonneg_left hlong hV8
  have hshort' := mul_le_mul_of_nonneg_left hshort hK
  linarith [hmul', hlong', hshort']

end RHTower.Sieve
