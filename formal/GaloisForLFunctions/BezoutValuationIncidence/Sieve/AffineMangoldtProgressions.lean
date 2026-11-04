import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffinePrimeProgressions
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimePowerTails

/-!
# Reciprocal Mangoldt mass in an affine congruence

Above the modulus square, prime multipliers cost one reciprocal modulus
times the logarithmic interval width. Proper prime powers contribute a
uniform fractional-power tail, with no congruence distribution assumption.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Removing the affine condition only enlarges the proper-prime-power remainder. -/
theorem proper_prime_power_Icc_tail {H X : ℕ} (hH : 1 ≤ H) :
    (∑ k ∈ (Icc H X).filter (fun k => ¬k.Prime), vonMangoldt k / (k : ℝ)) ≤
      576 * (H : ℝ) ^ (-(7 / 16 : ℝ)) := by
  have hsub : (Icc H X).filter (fun k => ¬k.Prime) ⊆
      (Icc 1 X).filter (fun k => ¬k.Prime ∧ (H : ℝ) ≤ k) := by
    intro k hk
    obtain ⟨hkHX, hkp⟩ := mem_filter.mp hk
    obtain ⟨hHk, hkX⟩ := mem_Icc.mp hkHX
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hH.trans hHk, hkX⟩, hkp, by exact_mod_cast hHk⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans ?_
  exact proper_prime_power_tail (by exact_mod_cast hH) X

/-- The affine prime bound plus the full proper-power tail controls every Mangoldt multiplier. -/
theorem exists_weighted_affine_mangoldt_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X b d : ℕ, p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X →
      p.Coprime b →
      (∑ k ∈ (Icc H X).filter (fun k => b * k ≡ d [MOD p]),
        vonMangoldt k / (k : ℝ)) ≤
          (1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) +
            576 * (H : ℝ) ^ (-(7 / 16 : ℝ)) := by
  obtain ⟨p₀, hp₀, hprime⟩ := exists_weighted_affine_prime_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X b d hp hpp hpH hHX hpb
  have hH : 1 ≤ H := (Nat.one_le_pow 2 p hp.pos).trans hpH
  have hsplit :
      (∑ k ∈ (Icc H X).filter (fun k => b * k ≡ d [MOD p]), vonMangoldt k / (k : ℝ)) ≤
        (∑ k ∈ (Icc H X).filter (fun k => k.Prime ∧ b * k ≡ d [MOD p]), Real.log k / (k : ℝ)) +
          ∑ k ∈ (Icc H X).filter (fun k => ¬k.Prime), vonMangoldt k / (k : ℝ) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro k _
    by_cases hkp : k.Prime
    · rw [vonMangoldt_apply_prime hkp]
      by_cases hcong : b * k ≡ d [MOD p] <;> simp [hkp, hcong]
    · by_cases hcong : b * k ≡ d [MOD p] <;> simp [hkp, hcong]
      exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  exact hsplit.trans (add_le_add (hprime p H X b d hp hpp hpH hHX hpb)
    (proper_prime_power_Icc_tail hH))

#print axioms proper_prime_power_Icc_tail
#print axioms exists_weighted_affine_mangoldt_upper

end GaloisForLFunctions.BezoutValuationIncidence
