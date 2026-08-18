import GaloisForLFunctions.RHTower.Sieve.SiftingRangeTop
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The truncation depth and the sieve level

The bounding sum keeps the divisors with at most `k` prime factors, and the level `z` must dominate
`hN^{2k}`.  Taking `k` just above `4e·(mertensS hN − mertensS P₁)` and `z = x^{1/4}`, the constraint
reads `log log x ≲ (log x)^{1−β}`, which holds for every `β < 1`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The sieve level. -/
def siftLevel (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem one_le_siftLevel {x : ℝ} (hx : 1 ≤ x) : 1 ≤ siftLevel x := by
  rw [siftLevel]
  have h1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hx
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt h1

theorem log_siftLevel {x : ℝ} (hx : 0 < x) : Real.log (siftLevel x) = Real.log x / 4 := by
  rw [siftLevel, Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx.le]
  ring

/-- The Mertens sum is monotone. -/
theorem mertensS_mono {M N : ℕ} (h : M ≤ N) : mertensS M ≤ mertensS N := by
  rw [mertensS, mertensS]
  refine Finset.sum_le_sum_of_subset_of_nonneg (primesLE_subset h) fun p hp _ => ?_
  have hp0 : 0 < p := by
    rw [mem_primesLE] at hp
    exact hp.2.pos
  have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  positivity

theorem mertensS_nonneg (N : ℕ) : 0 ≤ mertensS N := by
  rw [mertensS]
  refine Finset.sum_nonneg fun p hp => ?_
  have hp0 : 0 < p := by
    rw [mem_primesLE] at hp
    exact hp.2.pos
  have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  positivity

/-- The truncation depth of the bounding sum. -/
def siftDepth (β a x : ℝ) : ℕ :=
  ⌈4 * Real.exp 1 * (mertensS (siftTop β x) - mertensS (siftStart (a * β) x)) + Real.log 2⌉₊

/-- **The truncation depth is of size `log log x`.** -/
theorem siftDepth_le {β a : ℝ} (hβ0 : 0 < β) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : ℝ in atTop,
      ((siftDepth β a x : ℕ) : ℝ)
        ≤ 4 * Real.exp 1 * (Real.log ((Real.log x) ^ β) + mertensUpperConst)
          + Real.log 2 + 1 := by
  filter_upwards [eventually_le_siftTop hβ0 2, Filter.eventually_gt_atTop (1 : ℝ),
    siftStart_le_siftTop hβ0 ha0 ha1] with x hN2 hx1 hPN
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hmert := mertensS_le_logLog_add hN2
  have hmono := mertensS_mono hPN
  have hlogN : Real.log ((siftTop β x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
    have hfl : ((siftTop β x : ℕ) : ℝ) ≤ cardLength β x := by
      rw [siftTop]
      exact Nat.floor_le (cardLength_pos β x).le
    have hN0 : (0 : ℝ) < ((siftTop β x : ℕ) : ℝ) := by
      have : (0 : ℕ) < siftTop β x := by omega
      exact_mod_cast this
    calc Real.log ((siftTop β x : ℕ) : ℝ) ≤ Real.log (cardLength β x) :=
          Real.log_le_log hN0 hfl
      _ = (Real.log x) ^ β := log_cardLength β x
  have hN2R : (2 : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by exact_mod_cast hN2
  have hlogpos : (0 : ℝ) < Real.log ((siftTop β x : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hloglog : logLog (siftTop β x) ≤ Real.log ((Real.log x) ^ β) := by
    rw [logLog]
    exact Real.log_le_log hlogpos hlogN
  have harg0 : (0 : ℝ)
      ≤ 4 * Real.exp 1 * (mertensS (siftTop β x) - mertensS (siftStart (a * β) x))
        + Real.log 2 := by
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hmono, he, hl2]
  have hceil : ((siftDepth β a x : ℕ) : ℝ)
      ≤ (4 * Real.exp 1 * (mertensS (siftTop β x) - mertensS (siftStart (a * β) x))
          + Real.log 2) + 1 := by
    rw [siftDepth]
    exact le_of_lt (Nat.ceil_lt_add_one harg0)
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : mertensS (siftTop β x) - mertensS (siftStart (a * β) x)
      ≤ Real.log ((Real.log x) ^ β) + mertensUpperConst := by
    have h0 := mertensS_nonneg (siftStart (a * β) x)
    linarith [hmert, hloglog]
  nlinarith [hceil, hstep, he]

/-- **The level dominates `hN^{2k}`.**  The constraint is `log log x ≲ (log x)^{1−β}`. -/
theorem siftTop_pow_le_siftLevel {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a)
    (ha1 : a < 1) :
    ∀ᶠ x : ℝ in atTop,
      ((siftTop β x : ℕ) : ℝ) ^ (2 * siftDepth β a x) ≤ siftLevel x := by
  have hδ : (0 : ℝ) < 1 - β := by linarith
  have hsmall := tendsto_logLog_div_logRpow hδ
  have hbig : Tendsto (fun x : ℝ => (Real.log x) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop
  set C : ℝ := 8 * (4 * Real.exp 1 * mertensUpperConst + Real.log 2 + 1) with hC
  set D : ℝ := 32 * Real.exp 1 * β with hD
  filter_upwards [siftDepth_le hβ0 ha0 ha1, eventually_le_siftTop hβ0 2,
    Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_gt_atTop (0 : ℝ),
    Filter.eventually_ge_atTop (Real.exp 1),
    Tendsto.eventually_le_const (by positivity : (0 : ℝ) < 1 / (2 * (|D| + 1))) hsmall,
    hbig.eventually_ge_atTop (2 * (|C| + 1))] with x hk hN2 hx1 hx0 hxe hsm hbg
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hpow0 : (0 : ℝ) < (Real.log x) ^ (1 - β) := Real.rpow_pos_of_pos hlogx _
  have hN2R : (2 : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < ((siftTop β x : ℕ) : ℝ) := by linarith
  have hlogN : Real.log ((siftTop β x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
    have hfl : ((siftTop β x : ℕ) : ℝ) ≤ cardLength β x := by
      rw [siftTop]
      exact Nat.floor_le (cardLength_pos β x).le
    calc Real.log ((siftTop β x : ℕ) : ℝ) ≤ Real.log (cardLength β x) :=
          Real.log_le_log hN0 hfl
      _ = (Real.log x) ^ β := log_cardLength β x
  have hlogN0 : 0 ≤ Real.log ((siftTop β x : ℕ) : ℝ) := (Real.log_pos (by linarith)).le
  have hlogrpow : Real.log ((Real.log x) ^ β) = β * Real.log (Real.log x) :=
    Real.log_rpow hlogx β
  -- the depth bound in explicit terms
  have hkexp : ((siftDepth β a x : ℕ) : ℝ)
      ≤ 4 * Real.exp 1 * β * Real.log (Real.log x)
        + (4 * Real.exp 1 * mertensUpperConst + Real.log 2 + 1) := by
    rw [hlogrpow] at hk
    linarith [hk]
  -- the product of the exponent and the logarithm
  have hsplit : (Real.log x) ^ β * (Real.log x) ^ (1 - β) = Real.log x := by
    rw [← Real.rpow_add hlogx]
    norm_num
  have hpowβ0 : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx _
  have hkey : 2 * ((siftDepth β a x : ℕ) : ℝ) * Real.log ((siftTop β x : ℕ) : ℝ)
      ≤ Real.log x / 4 := by
    have hstep : 2 * ((siftDepth β a x : ℕ) : ℝ) * Real.log ((siftTop β x : ℕ) : ℝ)
        ≤ 2 * ((siftDepth β a x : ℕ) : ℝ) * (Real.log x) ^ β := by
      have hk0 : (0 : ℝ) ≤ ((siftDepth β a x : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hlogN, hk0]
    have hbound : 8 * ((siftDepth β a x : ℕ) : ℝ) ≤ (Real.log x) ^ (1 - β) := by
      have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
      have hnum : Real.log (Real.log x) * (2 * (|D| + 1)) ≤ (Real.log x) ^ (1 - β) := by
        have hd : (0 : ℝ) < 2 * (|D| + 1) := by positivity
        rw [div_le_iff₀ hpow0] at hsm
        calc Real.log (Real.log x) * (2 * (|D| + 1))
            ≤ (1 / (2 * (|D| + 1)) * (Real.log x) ^ (1 - β)) * (2 * (|D| + 1)) :=
              mul_le_mul_of_nonneg_right hsm hd.le
          _ = (Real.log x) ^ (1 - β) := by field_simp
      have hDlog : D * Real.log (Real.log x) ≤ (Real.log x) ^ (1 - β) / 2 := by
        have hDabs : D ≤ |D| := le_abs_self D
        nlinarith [hnum, hDabs, hll0]
      have hCbound : C ≤ (Real.log x) ^ (1 - β) / 2 := by
        have hCabs : C ≤ |C| := le_abs_self C
        linarith [hbg]
      have h8k : 8 * ((siftDepth β a x : ℕ) : ℝ) ≤ D * Real.log (Real.log x) + C := by
        rw [hD, hC]
        linarith [hkexp]
      linarith [h8k, hDlog, hCbound]
    nlinarith [hstep, hbound, hsplit, hpowβ0, Nat.cast_nonneg (α := ℝ) (siftDepth β a x)]
  -- pass to the exponential form
  have hlogpow : Real.log (((siftTop β x : ℕ) : ℝ) ^ (2 * siftDepth β a x))
      = ((2 * siftDepth β a x : ℕ) : ℝ) * Real.log ((siftTop β x : ℕ) : ℝ) := by
    rw [Real.log_pow]
  have hlhs0 : (0 : ℝ) < ((siftTop β x : ℕ) : ℝ) ^ (2 * siftDepth β a x) := by positivity
  have hrhs0 : (0 : ℝ) < siftLevel x := by
    have := one_le_siftLevel (by linarith : (1 : ℝ) ≤ x)
    linarith
  rw [← Real.log_le_log_iff hlhs0 hrhs0, hlogpow, log_siftLevel hx0]
  push_cast
  linarith [hkey]

end

end RHTower.Sieve
