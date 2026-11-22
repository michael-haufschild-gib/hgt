import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExceptionalZeroInSharpSum

/-! Sum the sharpened formula over the character group with the exceptional term removed. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

/-- A uniform ramp error and a weighted sum of nonexceptional zeros bound the total
character error after taking a short difference. -/
theorem psi_total_from_zero_packets {M : ℕ} [NeZero M] (hM3 : 3 ≤ M)
    (hS : SharpenS) (Z : DirichletCharacter ℂ M → Finset ℂ)
    (m : DirichletCharacter ℂ M → ℂ → ℕ) (K : DirichletCharacter ℂ M → ℂ)
    (y κ T δ E : ℝ) (hy : 2 ≤ y) (hT : 0 ≤ T) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hE0 : 0 ≤ E)
    (hcover : ∀ χ ρ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z χ)
    (hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1)
    (hm : ∀ χ, ∀ ρ ∈ Z χ, 1 ≤ m χ ρ)
    (herror : ∀ χ : DirichletCharacter ℂ M, ∀ u : ℝ, (u = y ∨ u = (1 + δ) * y) →
      ‖WindowedLandauTheory.HC.An.sumLamChi χ u / (u : ℂ) - K χ -
        (if χ = 1 then ((Real.log u - 1 : ℝ) : ℂ) else 0) +
        ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (u : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤ E) :
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) +
      22 * y * (∑ χ : DirichletCharacter ℂ M,
        ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1)) +
      (20 * δ * y + 2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  let t := y ^ (-(κ / 2))
  have ht0 : 0 ≤ t := by positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    exact hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ (herror χ)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (hm χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT (hcover χ) (fun ρ hρ => (hre χ ρ hρ).1) (hm χ) (hsharp χ)
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  simpa only [hW, t] using hsum

end QH.PrimeProgressions
