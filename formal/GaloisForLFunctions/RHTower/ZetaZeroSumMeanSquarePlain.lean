import GaloisForLFunctions.RHTower.ZetaZeroSumMeanSquare

/-!
# The plain second moment of a finite zero sum on a dyadic range

`ZetaZeroSumMeanSquare` bounds `∫_X^{2X} ‖Σ_q c_q x^ρ‖² / x³`, the shape in which the mean square of
a zero sum is cheapest to prove.  For the block reduction of a short-interval count one needs the
plain second moment `∫_X^{2X} ‖Σ_q c_q x^ρ‖²`, which differs by at most the factor `(2X)³` because
`x³ ≤ (2X)³` on the range.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory intervalIntegral

noncomputable section

/-- The zero sum is continuous on `[X, 2X]` for `0 < X`. -/
theorem continuousOn_zeroSum {X : ℝ} (hX : 0 < X) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ) :
    ContinuousOn (fun x : ℝ => ∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)) (Set.Icc X (2 * X)) := by
  refine continuousOn_finsetSum _ fun q _ => continuousOn_const.mul ?_
  refine continuousOn_of_forall_continuousAt fun x hx => ?_
  exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx.1]))

/-- **The plain second moment of a finite zero sum.**  `x³ ≤ (2X)³` on `[X, 2X]`, so the cube-weighted
mean square of `ZetaZeroSumMeanSquare` gives the unweighted one up to that factor. -/
theorem integral_norm_sq_zeroSum_le {X W : ℝ} (hX : 0 < X) (F : Finset XiZeroCopy)
    (c : XiZeroCopy → ℂ)
    (hW : ∀ q ∈ F, ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤ W) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
      ≤ (2 * X) ^ 3 * (4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hcont := continuousOn_zeroSum hX F c
  -- both integrands are continuous on the range, hence interval integrable
  have hi1 : IntervalIntegrable (fun x : ℝ => ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2)
      volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX2]
    exact (hcont.norm.pow 2).integrableOn_Icc
  have hi2 : IntervalIntegrable
      (fun x : ℝ => ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 * (2 * X) ^ 3)
      volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX2]
    refine (((hcont.norm.pow 2).div (continuousOn_pow 3) fun x hx => ?_).mul
      continuousOn_const).integrableOn_Icc
    have : 0 < x := by linarith [hx.1]
    positivity
  -- pointwise `‖S‖² ≤ (‖S‖²/x³) (2X)³`
  have hpt : ∀ x ∈ Set.Icc X (2 * X),
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
        ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 * (2 * X) ^ 3 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx3 : x ^ 3 ≤ (2 * X) ^ 3 := by
      have := hx.2
      gcongr
    have hx30 : (0 : ℝ) < x ^ 3 := by positivity
    have hs0 : (0 : ℝ) ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 := sq_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ hx30]
    nlinarith [hs0, hx3]
  calc ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
      ≤ ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 * (2 * X) ^ 3 :=
        integral_mono_on hX2 hi1 hi2 hpt
    _ = (∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) * (2 * X) ^ 3 := by
        rw [intervalIntegral.integral_mul_const]
    _ ≤ (4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)) * (2 * X) ^ 3 := by
        have h := integral_norm_sq_zeroSum_div_cube_le hX F c hW
        have h0 : (0 : ℝ) ≤ (2 * X) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right h h0
    _ = _ := by ring

end

end RHTower
