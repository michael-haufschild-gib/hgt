import GaloisForLFunctions.BezoutValuationIncidence.FlatSelbergRowAndExactQuadraticSandwichOrder
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveWithTheMontgomeryVaughanConstant

/-!
# The window sandwich with the Montgomery–Vaughan constant

The response of a sieve row is a trigonometric polynomial over the roots of unity of order at most
`N`, and these are `1/(N(N−1))`-separated. The two-sided Montgomery–Vaughan window bound therefore
gives, at every phase `A` and length `K`,

`|Σ_{A<k≤A+K} s(k)² − K Q_Sel| ≤ N(N − 1) Q_Sel`          (`abs_window_sum_sq_sub_le_mv`),

so `N(N − 1)` is an admissible window sandwich constant (`isWindowSandwichConstant_mv`), half the
trapezoid constant `2N² − 1`. With the flat Selberg row at a common return, the optimal constant lies
in `[Φ(N) − 2, N(N − 1)]`, `Φ(N) = Σ_{q ≤ N} φ(q) ~ 3N²/π²` (`windowSandwichConstant_between`).
-/

open Finset GaloisForLFunctions.BiScaleUncertainty RHTower.Sieve

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- **The window sandwich with constant `N(N − 1)`.** -/
theorem abs_window_sum_sq_sub_le_mv {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c k ^ 2 - K * selbergTotientDiagonalForm N c| ≤
      ((N : ℝ) * ((N : ℝ) - 1)) * selbergTotientDiagonalForm N c := by
  have h := abs_window_rootsOfUnity_sub_le hN (T := responseRoots N)
    (fun ζ hζ => exists_pow_eq_one_of_mem_responseRoots hζ)
    (fun ζ => (selbergMultiplesCoord N c (orderOf ζ) : ℂ)) A K
  simp only [← sieveSeq_sq_eq_norm_sq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sum_responseRoots_selberg_sq] using h

/-- The predicate form: `N(N − 1)` is an admissible window sandwich constant. -/
theorem isWindowSandwichConstant_mv {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N ((N : ℝ) * ((N : ℝ) - 1)) := by
  intro A K c κ
  have h := abs_window_sum_sq_sub_le_mv hN (sieveRowShift c κ) A K
  rw [selbergTotientDiagonalForm_sieveRowShift (by omega)] at h
  simpa only [sieveSeq_sieveRowShift (by omega : 1 ≤ N)] using h

/-- **The optimal window sandwich constant lies in `[Φ(N) − 2, N(N − 1)]`.** -/
theorem windowSandwichConstant_between {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N ((N : ℝ) * ((N : ℝ) - 1)) ∧
      ∀ S : ℝ, IsWindowSandwichConstant N S → (cyclotomicIncidenceOrder N : ℝ) - 2 ≤ S :=
  ⟨isWindowSandwichConstant_mv hN,
    fun _ hS => cyclotomicIncidenceOrder_sub_two_le_of_isWindowSandwichConstant hN hS⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
