import GaloisForLFunctions.HTGeometry.BoundedRandomEntireStructure

/-!
# The tail of the bounded random entire series

Beyond any index the clamped series is a monomial factor times another clamped series, whose
coefficients obey the same factorial bound.  The tail is therefore entire and depends only on the
shifted coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shifted coefficients of the tail. -/
def tailCoeff (N : ℕ) (y : ℕ → ℂ) (n : ℕ) : ℂ :=
  clampComplexSquare (y n) / ((4 : ℂ) * ((Nat.factorial (n + N) : ℕ) : ℂ))

theorem norm_tailCoeff_le (N : ℕ) (y : ℕ → ℂ) (n : ℕ) :
    ‖tailCoeff N y n‖ ≤ 1 / ((Nat.factorial n : ℕ) : ℝ) := by
  have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by positivity
  have hfacN : (0 : ℝ) < ((Nat.factorial (n + N) : ℕ) : ℝ) := by positivity
  have hle : ((Nat.factorial n : ℕ) : ℝ) ≤ ((Nat.factorial (n + N) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n N)
  rw [tailCoeff, norm_div, norm_mul, Complex.norm_natCast, show ‖(4 : ℂ)‖ = 4 by norm_num]
  rw [div_le_div_iff₀ (by positivity) hfac]
  have hc := norm_clampComplexSquare_le_four (y n)
  nlinarith [norm_nonneg (clampComplexSquare (y n))]

theorem tailCoeff_orderTwo (N : ℕ) (y : ℕ → ℂ) :
    ∀ R : ℝ, 0 < R → ∀ n, ‖tailCoeff N y n‖ ≤ Real.exp (R ^ 2 * 2 / 2) / R ^ n :=
  orderTwo_bound_of_factorial_bound (norm_tailCoeff_le N y)

theorem boundedRandomEntireTail_eq (N : ℕ) (y : ℕ → ℂ) (z : ℂ) :
    boundedRandomEntireTail N y z = z ^ N * entireOfCoeffs (tailCoeff N y) z := by
  rw [boundedRandomEntireTail, entireOfCoeffs, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [tailCoeff, pow_add]
  ring

theorem differentiable_boundedRandomEntireTail (N : ℕ) (y : ℕ → ℂ) :
    Differentiable ℂ (boundedRandomEntireTail N y) := by
  have heq : boundedRandomEntireTail N y
      = fun z => z ^ N * entireOfCoeffs (tailCoeff N y) z :=
    funext (boundedRandomEntireTail_eq N y)
  rw [heq]
  exact (differentiable_pow N).mul (differentiable_entireOfCoeffs (tailCoeff_orderTwo N y))

end

end GaloisForLFunctions.HTGeometry
