import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalDeepRowsPayTheFirstBand

/-!
# The critical Schur pairing retains the collar weight

The low-conductor residual meets three different reserves. Deep rows pay its
pairing with the first band; the full residual pays the second band and the
far prefix; the dual seventh-power mass pays the far collar. Keeping these
payments separate avoids charging the full residual against the collar floor.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- Rowwise Schur payment with distinct deep, prefix, and weighted collar masses. -/
theorem pairing_sum_le_deep_prefix_weighted_collar
    {M N : ℕ} {s : Finset ℕ} {E : ℕ → ℝ}
    {r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N)} {X Ψ Ψ_D Ψ_7 ρ : ℝ}
    (hMN : M ≤ N) (hE : ∀ m ∈ s, 0 < E m)
    (u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (htop : (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) ≤ ρ * ‖u₀‖ ^ 2)
    (hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ Ψ)
    (hΨD : (∑ m ∈ s, deepMass X (r m) / E m) ≤ Ψ_D)
    (hΨ7 : (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) ≤ Ψ_7) :
    (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      (6 * Ψ * ρ + 6 * Ψ_D) * ‖u₀‖ ^ 2 + 3 * Ψ * ‖u₁‖ ^ 2 +
        6 * Ψ * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        6 * Ψ_7 * topCollarSeventhMass M N (primeHorizonExtension w) := by
  let T := ∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2
  let S := topCollarSeventhMass M N (primeHorizonExtension w)
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sq_nonneg _
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := topCollarSeventhMass_nonneg _ _ _
  have hrow (m : ℕ) : ⟪r m, u₀ + u₁ + w⟫ ^ 2 ≤
      (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * ‖r m‖ ^ 2 +
        6 * ‖u₀‖ ^ 2 * deepMass X (r m) +
        6 * S * topCollarDualSeventhMass M N (r m) := by
    have h₀ := inner_sq_le_deep_add_top X (r m) u₀
    have h₁ : ⟪r m, u₁⟫ ^ 2 ≤ ‖r m‖ ^ 2 * ‖u₁‖ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (r m) u₁) 2
      simpa only [sq_abs, mul_pow] using h
    have hw := inner_sq_le_prefix_add_topCollarSeventh hMN (r m) w
    have hpref : (∑ n ∈ Icc 1 M, primeHorizonExtension (r m) n ^ 2) ≤ ‖r m‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN)
        fun _ _ _ => sq_nonneg _
    have hp := mul_le_mul_of_nonneg_right hpref hP
    have hthree : (⟪r m, u₀⟫ + ⟪r m, u₁⟫ + ⟪r m, w⟫) ^ 2 ≤
        3 * (⟪r m, u₀⟫ ^ 2 + ⟪r m, u₁⟫ ^ 2 + ⟪r m, w⟫ ^ 2) := by
      nlinarith only [sq_nonneg (⟪r m, u₀⟫ - ⟪r m, u₁⟫),
        sq_nonneg (⟪r m, u₀⟫ - ⟪r m, w⟫),
        sq_nonneg (⟪r m, u₁⟫ - ⟪r m, w⟫)]
    rw [inner_add_right, inner_add_right]
    change ⟪r m, u₀⟫ ^ 2 ≤ 2 * (‖r m‖ ^ 2 * T) +
      2 * (deepMass X (r m) * ‖u₀‖ ^ 2) at h₀
    change ⟪r m, w⟫ ^ 2 ≤ 2 * _ * P +
      2 * topCollarDualSeventhMass M N (r m) * S at hw
    nlinarith only [h₀, h₁, hw, hp, hthree]
  have hsum : (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * Ψ +
        6 * ‖u₀‖ ^ 2 * Ψ_D + 6 * S * Ψ_7 := by
    calc
      _ ≤ ∑ m ∈ s, ((6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * (‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
          6 * S * (topCollarDualSeventhMass M N (r m) / E m)) := by
        refine sum_le_sum fun m hm => ?_
        convert div_le_div_of_nonneg_right (hrow m) (hE m hm).le using 1 <;> ring
      _ = (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
          6 * S * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      _ ≤ _ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hΨ (by positivity))
          (mul_le_mul_of_nonneg_left hΨD (by positivity)))
        (mul_le_mul_of_nonneg_left hΨ7 (by positivity))
  have hΨ0 : 0 ≤ Ψ := (sum_nonneg fun m hm =>
    div_nonneg (sq_nonneg _) (hE m hm).le).trans hΨ
  have hpaid := mul_le_mul_of_nonneg_right htop hΨ0
  change T * Ψ ≤ (ρ * ‖u₀‖ ^ 2) * Ψ at hpaid
  change _ ≤ (6 * Ψ * ρ + 6 * Ψ_D) * ‖u₀‖ ^ 2 + 3 * Ψ * ‖u₁‖ ^ 2 +
    6 * Ψ * P + 6 * Ψ_7 * S
  linarith only [hsum, hpaid]


end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
