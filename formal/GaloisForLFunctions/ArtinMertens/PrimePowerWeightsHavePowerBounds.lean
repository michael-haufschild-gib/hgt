import GaloisForLFunctions.ArtinMertens.TheMertensTheoremForPrimeIdealsHasABoundedError

/-!
# Subcritical power weights on prime ideals

The established prime-power Chebyshev comparison and the integer power-sum
bound give `sum log N(p) / N(p)^(k*sigma) = O(N^(1-sigma))` for `0<sigma<1`.
The bound includes every positive integer cutoff.
-/

noncomputable section
open Finset NumberField Ideal
open scoped Classical
namespace GaloisForLFunctions.ArtinMertens
variable {K : Type*} [Field K] [NumberField K]

/-- Every subcritical inverse-power prime-power sum has the expected positive power bound. -/
theorem exists_sum_primePowersLe_log_rpow_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ pk ∈ primePowersLe K N, Real.log (absNorm pk.1) *
        ((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ) ≤ B * (N : ℝ) ^ (1 - σ) := by
  let C := (Module.finrank ℤ (𝓞 K) : ℝ) ^ 2 * (Real.log 4 + 4)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (sq_nonneg _) (by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith)
  refine ⟨C * (2 + (1 - σ)⁻¹), mul_nonneg hC (by positivity), fun N hN => ?_⟩
  refine (sum_log_mul_rpow_neg_le hσ0.le N).trans ?_
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N : ℝ) ^ (1 - σ) := Real.one_le_rpow hN1 (by linarith)
  have hn : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hs : ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ) ≤ (2 + (1 - σ)⁻¹) * (N : ℝ) ^ (1 - σ) := by
    rcases eq_or_lt_of_le hN with hN | hN
    · subst N
      simp only [Icc_self, sum_singleton, Nat.cast_one, Real.one_rpow, mul_one]
      have : 0 ≤ (1 - σ)⁻¹ := by positivity
      linarith
    · have hb := RHTower.Sieve.sum_rpow_neg_le_of_lt_one hσ0 hσ1 (show 2 ≤ N by omega)
      have hi : 0 ≤ (1 - σ)⁻¹ := by positivity
      rw [div_eq_mul_inv] at hb
      nlinarith
  exact (mul_le_mul_of_nonneg_left hs hC).trans_eq (mul_assoc _ _ _).symm


end GaloisForLFunctions.ArtinMertens
