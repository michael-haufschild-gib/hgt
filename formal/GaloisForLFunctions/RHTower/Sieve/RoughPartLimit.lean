import GaloisForLFunctions.RHTower.Sieve.FibreRoughLog
import GaloisForLFunctions.RHTower.Sieve.RoughPartArith
import GaloisForLFunctions.RHTower.Sieve.RoughRemainderLimit
import GaloisForLFunctions.RHTower.Sieve.ShiftCorrectionPos
import GaloisForLFunctions.RHTower.Sieve.SelbergRemainderSum
import GaloisForLFunctions.RHTower.Sieve.PairClassSum

/-!
# The discarded part of the fibre mean square vanishes

For the sifting range `(P₁, hN]` with `log P₁ = (log x)^{aβ}` and `log hN = (log x)^β`, the integers
free of primes in that range contribute `O((log x)^{−2β(1−a)})` to the normalised fibre mean square.
Since `a < 1` this vanishes, so the whole discarded part is negligible.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- **The Mertens correction of a large modulus is small.** -/
theorem mertensErr_le_half {N : ℕ}
    (hN : 2 * (2 * mertensFirstConst + 1 / 2) ≤ Real.log N) : mertensErr N ≤ 1 / 2 := by
  have hM : Real.log 4 ≤ mertensFirstConst := le_max_left _ _
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hC : (0 : ℝ) < 2 * mertensFirstConst + 1 / 2 := by linarith
  have hlog : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  rw [mertensErr, div_le_div_iff₀ hlog (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **The Mertens correction is nonnegative.** -/
theorem mertensErr_nonneg {N : ℕ} (hN : 0 ≤ Real.log (N : ℝ)) : 0 ≤ mertensErr N := by
  have hM : Real.log 4 ≤ mertensFirstConst := le_max_left _ _
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rw [mertensErr]
  exact div_nonneg (by linarith) hN

/-- The discarded part of the fibre mean square for the chosen parameters. -/
def roughPartSum (β a x : ℝ) : ℝ :=
  ∑ A ∈ outerBlock x (cardLength β x),
    (((innerFibre x (cardLength β x) A
        ∩ roughSet (siftStart (a * β) x) (siftTop β x)
            ⌊Real.sqrt x + cardLength β x⌋₊).card : ℕ) : ℝ) ^ 2

/-- **The discarded part of the fibre mean square vanishes.** -/
theorem tendsto_roughPart {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : ℝ =>
        (2 * roughPartSum β a x) / (cardLength β x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hab : (0 : ℝ) < a * β := mul_pos ha0 hβ0
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (a * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  -- the majorant vanishes
  have hMaj : Tendsto (fun x : ℝ =>
      72 / cardLength β x + 72 / Real.sqrt x + 864 * (siftRatio a β x) ^ 2
        + 24 * ((2 * siftLevel x
            * (6 : ℝ) ^ (Real.log (siftLevel x)
                / Real.log ((siftStart (a * β) x : ℕ) : ℝ))) / Real.sqrt x))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun x : ℝ => 72 / cardLength β x) atTop (𝓝 0) :=
      (tendsto_cardLength hβ0).const_div_atTop 72
    have t2 : Tendsto (fun x : ℝ => 72 / Real.sqrt x) atTop (𝓝 0) :=
      Real.tendsto_sqrt_atTop.const_div_atTop 72
    have t3 : Tendsto (fun x : ℝ => 864 * (siftRatio a β x) ^ 2) atTop (𝓝 0) := by
      have h := ((tendsto_siftRatio hβ0 ha0 ha1).pow 2).const_mul (864 : ℝ)
      simpa using h
    have t4 : Tendsto (fun x : ℝ => 24 * ((2 * siftLevel x
        * (6 : ℝ) ^ (Real.log (siftLevel x)
            / Real.log ((siftStart (a * β) x : ℕ) : ℝ))) / Real.sqrt x)) atTop (𝓝 0) := by
      have h := (tendsto_selbergRemainder_div_sqrt hβ0 ha0).const_mul (24 : ℝ)
      simpa using h
    have h := ((t1.add t2).add t3).add t4
    simpa using h
  refine squeeze_zero' ?_ ?_ hMaj
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    have hden : (0 : ℝ) < cardLength β x ^ 2 * Real.sqrt x := by
      have := cardLength_pos β x
      positivity
    have hnum : (0 : ℝ) ≤ roughPartSum β a x :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact div_nonneg (by linarith) hden.le
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    cardLength_le_sqrt hβ0 hβ1,
    eventually_le_siftStart hab 4, eventually_le_siftTop hβ0 2,
    siftStart_le_siftTop hβ0 ha0 ha1,
    siftTop_pow_le_siftLevel hβ0 hβ1 ha0 ha1,
    shiftCorrection_ge_half hβ0 ha0,
    hpowA.eventually_ge_atTop (2 * (2 * mertensFirstConst + 1 / 2))]
    with x hx4 hh1 hhs hP4 hN2 hPN hlev hcorr hCbig
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hP2 : 2 ≤ siftStart (a * β) x := by omega
  have hP1 : 1 ≤ siftStart (a * β) x := by omega
  have hPR : (2 : ℝ) ≤ ((siftStart (a * β) x : ℕ) : ℝ) := by exact_mod_cast hP2
  have hNR : (2 : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by exact_mod_cast hN2
  have hlogP : (0 : ℝ) < Real.log ((siftStart (a * β) x : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hlogN : (0 : ℝ) < Real.log ((siftTop β x : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hPNR : ((siftStart (a * β) x : ℕ) : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by exact_mod_cast hPN
  have hlogPN : Real.log ((siftStart (a * β) x : ℕ) : ℝ) ≤ Real.log ((siftTop β x : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hPNR
  have hz1 : (1 : ℝ) ≤ siftLevel x := one_le_siftLevel hx1
  -- the truncation depth is admissible
  have hk : ∀ d : ℕ, Real.exp 1
      * (∑ p ∈ rangePrimes (siftStart (a * β) x) (siftTop β x),
          pairClassCount d p / ((p : ℝ) - pairClassCount d p))
      + Real.log 2 ≤ ((siftDepth β a x : ℕ) : ℝ) := by
    intro d
    have h1 := sum_pairClassTerm_le hP4 hPN d
    have h2 : Real.exp 1
        * (∑ p ∈ rangePrimes (siftStart (a * β) x) (siftTop β x),
            pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        ≤ Real.exp 1 * (4 * (mertensS (siftTop β x) - mertensS (siftStart (a * β) x))) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
    have h3 : 4 * Real.exp 1 * (mertensS (siftTop β x) - mertensS (siftStart (a * β) x))
        + Real.log 2 ≤ ((siftDepth β a x : ℕ) : ℝ) := by
      rw [siftDepth]
      exact Nat.le_ceil _
    linarith
  -- the closed form
  have hbase := sum_sq_card_fibre_roughSet_log (x := x) (h := cardLength β x) hx4
    (cardLength_pos β x).le (Real.sqrt x + cardLength β x) hP2 (siftDepth β a x) hz1
    (by positivity) hN2 hPN hlev hk (by linarith [hcorr])
  -- the crude bounds on the corrections
  have hL0 : (0 : ℝ) ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ)
      / Real.log ((siftTop β x : ℕ) : ℝ) := div_nonneg hlogP.le hlogN.le
  have hL1 : Real.log ((siftStart (a * β) x : ℕ) : ℝ)
      / Real.log ((siftTop β x : ℕ) : ℝ) ≤ 1 := (div_le_one hlogN).2 hlogPN
  have hErrP : mertensErr (siftStart (a * β) x) ≤ 1 / 2 :=
    mertensErr_le_half (le_trans hCbig (log_siftStart_ge (a * β) x))
  have hErrN : mertensErr (siftTop β x) ≤ 1 / 2 :=
    mertensErr_le_half (by linarith [le_trans hCbig (log_siftStart_ge (a * β) x), hlogPN])
  have hErrP0 : 0 ≤ mertensErr (siftStart (a * β) x) := mertensErr_nonneg hlogP.le
  have hErrN0 : 0 ≤ mertensErr (siftTop β x) := mertensErr_nonneg hlogN.le
  have hE1 : (1 : ℝ)
      ≤ Real.exp (mertensErr (siftStart (a * β) x) + mertensErr (siftTop β x)) :=
    Real.one_le_exp (by linarith)
  have hE3 : Real.exp (mertensErr (siftStart (a * β) x) + mertensErr (siftTop β x)) ≤ 3 := by
    have hle : Real.exp (mertensErr (siftStart (a * β) x) + mertensErr (siftTop β x))
        ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_one_lt_d9, hle]
  have hR0 : (0 : ℝ) ≤ ∑ e ∈ (rangePrimorial (siftStart (a * β) x) (siftTop β x)).divisors,
      (if ((e : ℕ) : ℝ) ≤ siftLevel x then 2 * (6 : ℝ) ^ e.primeFactors.card else 0) := by
    refine Finset.sum_nonneg fun e _ => ?_
    split_ifs with hcase
    · positivity
    · exact le_rfl
  -- the normalised bound
  have hkey := roughPart_div_le (h := cardLength β x) (s := Real.sqrt x)
    (Y := Real.sqrt x + cardLength β x)
    (L := Real.log ((siftStart (a * β) x : ℕ) : ℝ) / Real.log ((siftTop β x : ℕ) : ℝ))
    (E := Real.exp (mertensErr (siftStart (a * β) x) + mertensErr (siftTop β x)))
    (c := 1 - Real.log ⌊cardLength β x⌋₊
      / (Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ)))
    (R := ∑ e ∈ (rangePrimorial (siftStart (a * β) x) (siftTop β x)).divisors,
      (if ((e : ℕ) : ℝ) ≤ siftLevel x then 2 * (6 : ℝ) ^ e.primeFactors.card else 0))
    (S := roughPartSum β a x)
    hh1 hhs hs0 rfl hL0 hL1 hE1 hE3 hcorr hR0 hbase
  -- the Selberg remainder
  have hRle : (∑ e ∈ (rangePrimorial (siftStart (a * β) x) (siftTop β x)).divisors,
      (if ((e : ℕ) : ℝ) ≤ siftLevel x then 2 * (6 : ℝ) ^ e.primeFactors.card else 0))
      ≤ 2 * siftLevel x * (6 : ℝ) ^ (Real.log (siftLevel x)
          / Real.log ((siftStart (a * β) x : ℕ) : ℝ)) := sum_selbergRemainder_le hP2 hz1
  have hRstep : 24 * (∑ e ∈ (rangePrimorial (siftStart (a * β) x) (siftTop β x)).divisors,
      (if ((e : ℕ) : ℝ) ≤ siftLevel x then 2 * (6 : ℝ) ^ e.primeFactors.card else 0))
        / Real.sqrt x
      ≤ 24 * ((2 * siftLevel x * (6 : ℝ) ^ (Real.log (siftLevel x)
          / Real.log ((siftStart (a * β) x : ℕ) : ℝ))) / Real.sqrt x) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hs0).mpr hRle) (by norm_num)
  have hLdef : siftRatio a β x
      = Real.log ((siftStart (a * β) x : ℕ) : ℝ) / Real.log ((siftTop β x : ℕ) : ℝ) := rfl
  rw [hLdef]
  linarith [hkey, hRstep]

end

end RHTower.Sieve
