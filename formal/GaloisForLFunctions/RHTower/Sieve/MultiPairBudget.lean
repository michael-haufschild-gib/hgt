import GaloisForLFunctions.RHTower.Sieve.MultiBlockFrame
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp
import GaloisForLFunctions.RHTower.Sieve.SieveRemainderBound

/-!
# The shifted-pair budget of the marker family

The sifting bound is the `144`-th root of the marker base and the level its fourth root, so the
level condition `h^18 ≤ √z` of `Sieve/PrimePairAverageSharp` holds with room to spare, the saving
`exp(mertensS h − mertensS 3)` is a fixed fraction of `log M₀`, and the remainder — at most twice
the cube of the level by `Sieve/SieveRemainderBound` — is `M₀^{3/4}`.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The level of the pair sieve. -/
def multiLevel (K₀ v : ℕ) : ℝ := ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)

/-- The sifting bound of the pair sieve. -/
def multiSift (K₀ v : ℕ) : ℕ := ⌊((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144)⌋₊

/-- The shift range of the device. -/
def multiPairK (K₀ v : ℕ) : ℕ := 4 ^ (K₀ + 1) * multiFactor K₀ v

theorem one_le_multiLevel {K₀ v : ℕ} (hM : 1 ≤ multiBase K₀ v) : 1 ≤ multiLevel K₀ v := by
  rw [multiLevel]
  refine Real.one_le_rpow ?_ (by norm_num)
  exact_mod_cast hM

theorem multiSift_le_base {K₀ v : ℕ} (hM : 1 ≤ multiBase K₀ v) :
    multiSift K₀ v ≤ multiBase K₀ v := by
  have hMR : (1 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM
  have hle : ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by
    calc ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144)
        ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = ((multiBase K₀ v : ℕ) : ℝ) := Real.rpow_one _
  rw [multiSift]
  simpa using Nat.floor_le_of_le hle

/-- **The level condition of the pair sieve.** -/
theorem multiSift_pow_le {K₀ v : ℕ} (hM : 1 ≤ multiBase K₀ v) :
    ((multiSift K₀ v : ℕ) : ℝ) ^ (18 : ℝ) ≤ Real.sqrt (multiLevel K₀ v) := by
  have hMR : (1 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hfloor : ((multiSift K₀ v : ℕ) : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144) := by
    rw [multiSift]
    exact Nat.floor_le (Real.rpow_nonneg hM0 _)
  have hstep : ((multiSift K₀ v : ℕ) : ℝ) ^ (18 : ℝ)
      ≤ (((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144)) ^ (18 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor (by norm_num)
  have hval : (((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144)) ^ (18 : ℝ)
      = ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_mul hM0]
    norm_num
  have hsq : Real.sqrt (multiLevel K₀ v) = ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [multiLevel, Real.sqrt_eq_rpow, ← Real.rpow_mul hM0]
    norm_num
  rw [hsq, ← hval]
  exact hstep

/-- **The shifted-pair budget of the marker family.** -/
theorem multi_pair_le {K₀ v : ℕ} (hM : 1 ≤ multiBase K₀ v) (hs3 : 3 ≤ multiSift K₀ v)
    (hlog : 20 * mertensFirstConst ≤ Real.log (multiSift K₀ v)) :
    ∑ d ∈ Finset.Icc 1 (multiPairK K₀ v),
        ((((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).filter
          (fun p => p + d ∈ bigPrimeSet (multiBase K₀ v)
            (2 ^ (K₀ + 1) * multiBase K₀ v))).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * ((multiPairK K₀ v : ℕ) : ℝ)
            * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
            / (Real.exp (mertensS (multiSift K₀ v) - mertensS 3)) ^ 2
        + ((multiPairK K₀ v : ℕ) : ℝ) * (2 * (multiLevel K₀ v) ^ 3) := by
  have hbase := sum_card_shift_bigPrimeSet_le_sieve_sharp (M₀ := multiBase K₀ v)
    (b := 2 ^ (K₀ + 1) * multiBase K₀ v) (P₁ := 3) (by norm_num) (h := multiSift K₀ v)
    (multiPairK K₀ v) (z := multiLevel K₀ v) (one_le_multiLevel hM) (by omega) hs3
    (multiSift_le_base hM) (multiSift_pow_le hM) hlog
  have hrem := sieve_remainder_le (P₁ := 3) (h := multiSift K₀ v) (by norm_num)
    (one_le_multiLevel hM)
  have hK0 : (0 : ℝ) ≤ ((multiPairK K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrem hK0
  linarith [hbase, hmul]

end

end RHTower.Sieve
