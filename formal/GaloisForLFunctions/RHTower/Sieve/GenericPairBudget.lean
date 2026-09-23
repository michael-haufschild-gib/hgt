import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp
import GaloisForLFunctions.RHTower.Sieve.SieveRemainderBound

/-!
# The shifted-pair budget of an arbitrary prime range

`Sieve/MultiPairBudget` fixes the sieve parameters in terms of one particular marker base.  The same
choices — level the fourth root, sifting bound the `144`-th root — work for any base, and the level
condition `h^(18 : ℕ) ≤ √z` holds exactly because `18/144 = 1/8 = (1/4)/2`.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The level of the pair sieve at base `M₀`. -/
def sieveLevel (M₀ : ℕ) : ℝ := ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 4)

/-- The sifting bound of the pair sieve at base `M₀`. -/
def sieveSift (M₀ : ℕ) : ℕ := ⌊((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144)⌋₊

theorem one_le_sieveLevel {M₀ : ℕ} (hM : 1 ≤ M₀) : 1 ≤ sieveLevel M₀ := by
  rw [sieveLevel]
  refine Real.one_le_rpow ?_ (by norm_num)
  exact_mod_cast hM

theorem sieveSift_le {M₀ : ℕ} (hM : 1 ≤ M₀) : sieveSift M₀ ≤ M₀ := by
  have hMR : (1 : ℝ) ≤ ((M₀ : ℕ) : ℝ) := by exact_mod_cast hM
  have hle : ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144) ≤ ((M₀ : ℕ) : ℝ) := by
    calc ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144)
        ≤ ((M₀ : ℕ) : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = ((M₀ : ℕ) : ℝ) := Real.rpow_one _
  rw [sieveSift]
  simpa using Nat.floor_le_of_le hle

/-- **The level condition of the pair sieve.** -/
theorem sieveSift_pow_le {M₀ : ℕ} (hM : 1 ≤ M₀) :
    ((sieveSift M₀ : ℕ) : ℝ) ^ (18 : ℝ) ≤ Real.sqrt (sieveLevel M₀) := by
  have hMR : (1 : ℝ) ≤ ((M₀ : ℕ) : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ ((M₀ : ℕ) : ℝ) := by linarith
  have hfloor : ((sieveSift M₀ : ℕ) : ℝ) ≤ ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144) := by
    rw [sieveSift]
    exact Nat.floor_le (Real.rpow_nonneg hM0 _)
  have hstep : ((sieveSift M₀ : ℕ) : ℝ) ^ (18 : ℝ)
      ≤ (((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144)) ^ (18 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor (by norm_num)
  have hval : (((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 144)) ^ (18 : ℝ)
      = ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_mul hM0]
    norm_num
  have hsq : Real.sqrt (sieveLevel M₀) = ((M₀ : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [sieveLevel, Real.sqrt_eq_rpow, ← Real.rpow_mul hM0]
    norm_num
  rw [hsq, ← hval]
  exact hstep

/-- **The shifted-pair budget of an arbitrary prime range.** -/
theorem generic_pair_le {M₀ b K : ℕ} (hM : 1 ≤ M₀) (hs3 : 3 ≤ sieveSift M₀)
    (hlog : 20 * mertensFirstConst ≤ Real.log (sieveSift M₀)) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ b).filter (fun p => p + d ∈ bigPrimeSet M₀ b)).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * (b : ℝ)
            / (Real.exp (mertensS (sieveSift M₀) - mertensS 3)) ^ 2
        + (K : ℝ) * (2 * (sieveLevel M₀) ^ 3) := by
  have hbase := sum_card_shift_bigPrimeSet_le_sieve_sharp (M₀ := M₀) (b := b) (P₁ := 3)
    (by norm_num) (h := sieveSift M₀) K (z := sieveLevel M₀) (one_le_sieveLevel hM)
    (by omega) hs3 (sieveSift_le hM) (sieveSift_pow_le hM) hlog
  have hrem := sieve_remainder_le (P₁ := 3) (h := sieveSift M₀) (by norm_num)
    (one_le_sieveLevel hM)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrem hK0
  linarith [hbase, hmul]

end

end RHTower.Sieve
