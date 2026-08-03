import GaloisForLFunctions.RHTower.Sieve.GallagherSum

/-!
# Splitting the mixed term

The mixed term `2|S||S'|` of Gallagher's bound is separated by the elementary inequality

`2ab ≤ ε a² + ε^{-1} b²`,

valid for every `ε > 0` because `(εa - b)² ≥ 0`.  Integrating it turns the mixed integral into a
combination of the two energies, which `TrigParseval.lean` and `TrigDerivative.lean` evaluate.

Using the pointwise inequality rather than Cauchy–Schwarz for integrals keeps the argument
elementary and leaves `ε` free, to be chosen at the end so that the two contributions balance.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The weighted arithmetic–geometric mean inequality.** -/
theorem two_mul_le_amgm (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + (1 / ε) * b ^ 2 := by
  have key : (0 : ℝ) ≤ (ε * a - b) ^ 2 := sq_nonneg _
  have hexp : (ε * a - b) ^ 2 = ε ^ 2 * a ^ 2 - 2 * ε * a * b + b ^ 2 := by ring
  rw [hexp] at key
  have h2 : 2 * ε * a * b ≤ ε ^ 2 * a ^ 2 + b ^ 2 := by linarith
  have hdiv : (2 * ε * a * b) / ε ≤ (ε ^ 2 * a ^ 2 + b ^ 2) / ε := by gcongr
  have hl : (2 * ε * a * b) / ε = 2 * a * b := by
    field_simp
  have hr : (ε ^ 2 * a ^ 2 + b ^ 2) / ε = ε * a ^ 2 + (1 / ε) * b ^ 2 := by
    field_simp
  rw [hl, hr] at hdiv
  exact hdiv

/-- **The mixed integral split into the two energies.** -/
theorem integral_mixed_le (N : ℕ) (c : Fin N → ℂ) {A B ε : ℝ} (hAB : A ≤ B) (hε : 0 < ε) :
    (∫ t in A..B, 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖)
      ≤ ε * (∫ t in A..B, ‖expSum N c t‖ ^ 2)
        + (1 / ε) * (∫ t in A..B, ‖expSum N (derivCoeff N c) t‖ ^ 2) := by
  have hc1 : Continuous (fun t : ℝ => ‖expSum N c t‖ ^ 2) :=
    ((continuous_expSum N c).norm).pow 2
  have hc2 : Continuous (fun t : ℝ => ‖expSum N (derivCoeff N c) t‖ ^ 2) :=
    ((continuous_expSum N (derivCoeff N c)).norm).pow 2
  have hcmix : Continuous (fun t : ℝ =>
      2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) :=
    (continuous_const.mul (continuous_expSum N c).norm).mul
      (continuous_expSum N (derivCoeff N c)).norm
  have hcrhs : Continuous (fun t : ℝ =>
      ε * ‖expSum N c t‖ ^ 2 + (1 / ε) * ‖expSum N (derivCoeff N c) t‖ ^ 2) :=
    (continuous_const.mul hc1).add (continuous_const.mul hc2)
  have hmono : (∫ t in A..B, 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖)
      ≤ ∫ t in A..B, (ε * ‖expSum N c t‖ ^ 2
          + (1 / ε) * ‖expSum N (derivCoeff N c) t‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hAB (hcmix.intervalIntegrable _ _)
      (hcrhs.intervalIntegrable _ _) ?_
    intro t _
    exact two_mul_le_amgm _ _ hε
  have hi1 : IntervalIntegrable (fun t : ℝ => ε * ‖expSum N c t‖ ^ 2) volume A B :=
    (continuous_const.mul hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 / ε) * ‖expSum N (derivCoeff N c) t‖ ^ 2) volume A B :=
    (continuous_const.mul hc2).intervalIntegrable _ _
  have hsplit : (∫ t in A..B, (ε * ‖expSum N c t‖ ^ 2
        + (1 / ε) * ‖expSum N (derivCoeff N c) t‖ ^ 2))
      = ε * (∫ t in A..B, ‖expSum N c t‖ ^ 2)
        + (1 / ε) * (∫ t in A..B, ‖expSum N (derivCoeff N c) t‖ ^ 2) := by
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hmono
  exact hmono

end RHTower.Sieve
