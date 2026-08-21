import GaloisForLFunctions.HTGeometry.WeierstrassLogDerivMittagLeffler

/-!
# Concrete Mittag-Leffler applications at the negative integers

The pole sequence `-1, -2, ...` satisfies the hypotheses of the corpus's
Mittag-Leffler/Weierstrass approximation theorem. This module records closed
instances for its canonical product and for a shifted prescribed divisor.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The simple pole sequence at the negative nonzero integers. -/
def negativeIntegerPole (n : ℕ) : ℂ := -(((n : ℝ) + 1 : ℝ) : ℂ)

theorem norm_negativeIntegerPole (n : ℕ) : ‖negativeIntegerPole n‖ = n + 1 := by
  rw [negativeIntegerPole, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

theorem tendsto_norm_negativeIntegerPole :
    Filter.Tendsto (fun n => ‖negativeIntegerPole n‖) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [norm_negativeIntegerPole]
  exact le_trans hN (by exact_mod_cast Nat.le_trans hn (Nat.le_succ n))

theorem negativeIntegerPole_ne_zero (n : ℕ) : negativeIntegerPole n ≠ 0 := by
  rw [negativeIntegerPole]
  apply neg_ne_zero.mpr
  exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < (n : ℝ) + 1)

theorem negativeIntegerPole_re_lt_one (n : ℕ) : (negativeIntegerPole n).re < 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp [negativeIntegerPole]
  linarith

/-- The corrected simple-pole series at the negative integers converges at the origin. -/
theorem summable_negativeIntegerMittagLeffler_terms :
    Summable fun n => (1 : ℂ) / (0 - negativeIntegerPole n)
      - weierstrassMittagLefflerCorrection negativeIntegerPole n 0 :=
  summable_weierstrassMittagLefflerTerm tendsto_norm_negativeIntegerPole
    negativeIntegerPole_ne_zero 0

/-- The negative-integer Weierstrass product has the closed-half-plane
Mittag-Leffler approximation required by the logarithmic-derivative construction. -/
theorem exists_entire_approx_sq_logDeriv_negativeIntegerProduct :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖s ^ 2 * logDeriv (weierstrassGenusProduct negativeIntegerPole) s - G s‖ ≤ 1 := by
  obtain ⟨G, hGd, hGb⟩ := exists_entire_approx_sq_logDeriv_weierstrassGenusProduct 0
    tendsto_norm_negativeIntegerPole negativeIntegerPole_ne_zero negativeIntegerPole_re_lt_one
    zero_lt_one
  exact ⟨G, hGd, fun s hs => by simpa using hGb s hs⟩

/-- The shifted negative-integer divisor has the same closed-half-plane
Mittag-Leffler approximation. -/
theorem exists_entire_approx_sq_logDeriv_negativeIntegerDivisor :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖s ^ 2 * logDeriv
          (divisorFunction negativeIntegerPole (fun n => negativeIntegerPole (n + 1))) s - G s‖ ≤ 1 := by
  have hshift : Filter.Tendsto (fun n => ‖negativeIntegerPole (n + 1)‖)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    rw [norm_negativeIntegerPole]
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  obtain ⟨G, hGd, hGb⟩ := exists_entire_approx_sq_logDeriv_divisorFunction 0
    tendsto_norm_negativeIntegerPole negativeIntegerPole_ne_zero hshift
    (fun n => negativeIntegerPole_ne_zero (n + 1)) negativeIntegerPole_re_lt_one
    (fun n => negativeIntegerPole_re_lt_one (n + 1)) zero_lt_one
  exact ⟨G, hGd, fun s hs => by simpa using hGb s hs⟩

end GaloisForLFunctions.HTGeometry
