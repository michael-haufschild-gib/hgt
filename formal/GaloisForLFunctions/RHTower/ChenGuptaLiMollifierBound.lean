/-
# Chen--Gupta--Li detector mollifier bound

Uniform elementary control of the finite Möbius--Dirichlet-character detector
on the closed right half-plane, including its critical-line specialization.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiTailCoefficientBounds

open ArithmeticFunction

namespace RHTower

noncomputable section

/-- The finite detector mollifier has norm at most its inclusive cutoff on the
certified right half-plane. -/
theorem norm_zeroDetectionMobiusPolynomial_le_cutoff (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : CGLRightHalfPlanePoint) :
    ‖zeroDetectionMobiusPolynomial X q χ s.1‖ ≤ (X + 1 : ℕ) := by
  unfold zeroDetectionMobiusPolynomial
  calc
    ‖∑ d ∈ Finset.Icc 1 (X + 1), (moebius d : ℂ) * χ d * (d : ℂ) ^ (-s.1)‖ ≤
        ∑ d ∈ Finset.Icc 1 (X + 1), ‖(moebius d : ℂ) * χ d * (d : ℂ) ^ (-s.1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 (X + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hmu : ‖(moebius d : ℂ) * χ d‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖(moebius d : ℂ)‖ * ‖χ d‖ ≤ 1 * ‖χ d‖ :=
            mul_le_mul_of_nonneg_right (by
              rw [Complex.norm_intCast]
              exact_mod_cast abs_moebius_le_one) (norm_nonneg _)
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (χ.norm_le_one d) (by norm_num)
          _ = 1 := one_mul _
      have hpow : ‖(d : ℂ) ^ (-s.1)‖ ≤ 1 := by
        rw [show (d : ℂ) = ((d : ℝ) : ℂ) by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · exact_mod_cast hd1
        · simp only [Complex.neg_re]
          exact neg_nonpos.mpr (le_trans (by norm_num) s.2)
      calc
        ‖(moebius d : ℂ) * χ d‖ * ‖(d : ℂ) ^ (-s.1)‖ ≤
            1 * ‖(d : ℂ) ^ (-s.1)‖ :=
          mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 1 := one_mul _
    _ = ((Finset.Icc 1 (X + 1)).card : ℝ) := by simp
    _ = (X + 1 : ℕ) := by
      rw [Nat.card_Icc]
      norm_cast

/-- Certified point on the critical line used by the class-II source integral. -/
def cglCriticalLinePoint (t : ℝ) : CGLRightHalfPlanePoint :=
  ⟨(1 / 2 : ℂ) + (t : ℂ) * Complex.I, by norm_num⟩

/-- The source's elementary critical-line bound for the finite detector
mollifier, with a closed inclusive-cutoff constant. -/
theorem norm_zeroDetectionMobiusPolynomial_criticalLine_le_cutoff (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖zeroDetectionMobiusPolynomial X q χ (cglCriticalLinePoint t).1‖ ≤ (X + 1 : ℕ) :=
  norm_zeroDetectionMobiusPolynomial_le_cutoff X q χ (cglCriticalLinePoint t)

end

end RHTower
