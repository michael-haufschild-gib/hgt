import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLadderErrorSharp
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicTruncatedRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowLogPowerSchedule
import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh

/-!
# Log-power cost of the truncated harmonic ladder defect

Stopping the final designated-prime ladder at `X / (log X)^(20 : ℕ)` makes the exact hard-support
replacement error smaller than eight fixed powers of `log X`, uniformly for every receiver height
between zero and `X`.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- The literal `H`-adic increment is at most twice `H⁻¹`. -/
theorem eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten :
    ∀ᶠ x : ℝ in atTop,
      0 < menonFinalRangeLadderEta x ∧
      menonFinalRangeLadderEta x ≤ 2 / (Real.log x) ^ (10 : ℕ) ∧
      1 + menonFinalRangeLadderEta x ≤ 2 := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hxe hlog2
  have hx : 1 < x := by nlinarith [Real.exp_one_gt_d9]
  have hlog0 : 0 < Real.log x := Real.log_pos hx
  have hH : 0 < menonFinalRangeLadderH x := by
    rw [menonFinalRangeLadderH]
    positivity
  have hHtwo : 2 ≤ menonFinalRangeLadderH x := by
    rw [menonFinalRangeLadderH]
    have hp : (2 : ℝ) ^ (10 : ℕ) ≤ (Real.log x) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hlog2 10
    norm_num at hp ⊢
    linarith
  have hu0 : 0 ≤ 1 / menonFinalRangeLadderH x := by positivity
  have huhalf : 1 / menonFinalRangeLadderH x ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hHtwo
  have hexp := exp_le_one_add_two_mul hu0 huhalf
  have hetaPos : 0 < menonFinalRangeLadderEta x := by
    rw [menonFinalRangeLadderEta, sub_pos]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr
      (by positivity : (0 : ℝ) < 1 / menonFinalRangeLadderH x)
  have hetaLe : menonFinalRangeLadderEta x ≤ 2 / (Real.log x) ^ (10 : ℕ) := by
    rw [menonFinalRangeLadderH] at hexp
    rw [menonFinalRangeLadderEta, menonFinalRangeLadderH]
    have hsub := sub_le_sub_right hexp 1
    simpa [div_eq_mul_inv] using hsub
  have hetaOne : menonFinalRangeLadderEta x ≤ 1 := by
    rw [menonFinalRangeLadderEta]
    linarith
  exact ⟨hetaPos, hetaLe, by linarith⟩

/-- The truncated ceiling depth costs at most twice `log(X)^(11 : ℕ)`. -/
theorem eventually_menonTruncatedRangeLadderSteps_le_two_mul_log_pow_eleven :
    ∀ᶠ x : ℝ in atTop,
      (menonTruncatedRangeLadderSteps x : ℝ) ≤ 2 * (Real.log x) ^ (11 : ℕ) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_ge_atTop (Real.exp 1), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with
      x hx hxe hlogOne
  rcases hx with ⟨hxone, _, hH, hQ, htop, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have htop0 : 0 < (menonTruncatedPrimeTopNat x : ℝ) := lt_trans hbase0 htop
  have hratio1 : 1 < (menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x :=
    (one_lt_div hbase0).2 htop
  have harg0 : 0 ≤ menonFinalRangeLadderH x *
      Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) :=
    mul_nonneg hH.le (Real.log_nonneg hratio1.le)
  have hceil := Nat.ceil_lt_add_one harg0
  have htopX : (menonTruncatedPrimeTopNat x : ℝ) ≤ x := by
    rw [menonTruncatedPrimeTopNat]
    calc
      (⌊menonTruncatedPrimeTop x⌋₊ : ℝ) ≤ menonTruncatedPrimeTop x :=
        Nat.floor_le (by rw [menonTruncatedPrimeTop]; positivity)
      _ ≤ x := by
        rw [menonTruncatedPrimeTop]
        exact div_le_self (by linarith) (one_le_pow₀ hlogOne)
  have hratioX : (menonTruncatedPrimeTopNat x : ℝ) /
      menonFinalRangeLadderBase x ≤ x := by
    exact (div_le_self htop0.le (by linarith : 1 ≤ menonFinalRangeLadderBase x)).trans htopX
  have hlogRatio : Real.log ((menonTruncatedPrimeTopNat x : ℝ) /
      menonFinalRangeLadderBase x) ≤ Real.log x :=
    Real.log_le_log (div_pos htop0 hbase0) hratioX
  have hceil' : (menonTruncatedRangeLadderSteps x : ℝ) <
      menonFinalRangeLadderH x *
          Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) + 1 := by
    simpa only [menonTruncatedRangeLadderSteps] using hceil
  have hpow : menonFinalRangeLadderH x * Real.log x = (Real.log x) ^ (11 : ℕ) := by
    rw [menonFinalRangeLadderH, pow_succ]
    ring_nf
  have hmain : (menonTruncatedRangeLadderSteps x : ℝ) <
      (Real.log x) ^ (11 : ℕ) + 1 := by
    calc
      (menonTruncatedRangeLadderSteps x : ℝ) <
          menonFinalRangeLadderH x *
              Real.log ((menonTruncatedPrimeTopNat x : ℝ) /
                menonFinalRangeLadderBase x) + 1 := hceil'
      _ ≤ menonFinalRangeLadderH x * Real.log x + 1 := by gcongr
      _ = (Real.log x) ^ (11 : ℕ) + 1 := by rw [hpow]
  have hpone : 1 ≤ (Real.log x) ^ (11 : ℕ) := one_le_pow₀ hlogOne
  linarith

/-- Menon's lower cutoff beats thirty powers of the logarithm after natural flooring. -/
theorem eventually_inv_menonFinalRangeLadderBase_le_log_rpow_neg_thirty :
    ∀ᶠ x : ℝ in atTop,
      1 / menonFinalRangeLadderBase x ≤ (Real.log x) ^ (-(30 : ℝ)) := by
  filter_upwards [eventually_half_exp_sqrtLog_div_eighty_le_menonFinalRangeLadderBase,
    eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
      (B := 1) (c := (1 : ℝ) / 80) (K := (30 : ℝ)) (by norm_num) (by norm_num),
    eventually_menonTruncatedRangeLadder_basic] with x hbase hdecay hx
  rcases hx with ⟨hxone, _, _, hQ, _, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have hexp0 : 0 < Real.exp (Real.sqrt (Real.log x) / 80) := Real.exp_pos _
  have hinv : 1 / menonFinalRangeLadderBase x ≤
      2 * Real.exp (-(1 / 80 : ℝ) * Real.sqrt (Real.log x)) := by
    rw [div_le_iff₀ hbase0]
    have hexpInv : Real.exp (-(1 / 80 : ℝ) * Real.sqrt (Real.log x)) *
        Real.exp (Real.sqrt (Real.log x) / 80) = 1 := by
      rw [← Real.exp_add]
      rw [show -(1 / 80 : ℝ) * Real.sqrt (Real.log x) +
        Real.sqrt (Real.log x) / 80 = 0 by ring, Real.exp_zero]
    nlinarith [mul_le_mul_of_nonneg_left hbase
      (Real.exp_pos (-(1 / 80 : ℝ) * Real.sqrt (Real.log x))).le]
  exact hinv.trans (by simpa [mul_assoc] using hdecay)

/-- Logarithm of the natural lower cutoff retains half the square-root-log exponent. -/
theorem eventually_sqrtLog_div_one_sixty_le_log_menonFinalRangeLadderBase :
    ∀ᶠ x : ℝ in atTop,
      Real.sqrt (Real.log x) / 160 ≤ Real.log (menonFinalRangeLadderBase x) := by
  have hsqrtTop : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_half_exp_sqrtLog_div_eighty_le_menonFinalRangeLadderBase,
    hsqrtTop.eventually_ge_atTop (160 * Real.log 2),
    eventually_menonTruncatedRangeLadder_basic] with x hbase hsqrt hx
  rcases hx with ⟨_, _, _, hQ, _, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have hleft0 : 0 < Real.exp (Real.sqrt (Real.log x) / 80) / 2 := by positivity
  have hlog := Real.log_le_log hleft0 hbase
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at hlog
  nlinarith

/-- The logarithmic overlap quotient in the closed defect budget is at most `320 sqrt(log X)`. -/
theorem eventually_menonTruncatedRange_overlapQuotient_le :
    ∀ᶠ x : ℝ in atTop,
      Real.log ((⌊(menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) /
          Real.log (menonFinalRangeLadderBase x) ≤
        320 * Real.sqrt (Real.log x) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten,
    eventually_sqrtLog_div_one_sixty_le_log_menonFinalRangeLadderBase,
    eventually_ge_atTop (6 : ℝ)] with x hx heta hlogQ hx6
  rcases hx with ⟨hxone, hlogOne, _, hQ, _, _, _⟩
  rcases heta with ⟨_, _, hrTwo⟩
  have hx0 : 0 < x := lt_trans zero_lt_one hxone
  have hB : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hN : ((⌊(menonFinalRangeTopNat x : ℝ) *
      (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤ 6 * x := by
    calc
      ((⌊(menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤
          (menonFinalRangeTopNat x : ℝ) *
            (1 + menonFinalRangeLadderEta x) := Nat.floor_le (by positivity)
      _ ≤ 6 * x := by nlinarith
  have hNpos : 0 < ((⌊(menonFinalRangeTopNat x : ℝ) *
      (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) := by
    have hBnat : 1 ≤ menonFinalRangeTopNat x := by
      rw [menonFinalRangeTopNat]
      apply Nat.le_floor
      norm_num
      nlinarith
    have hprod : (1 : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) *
        (1 + menonFinalRangeLadderEta x) := by
      have hcast : (1 : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) := by exact_mod_cast hBnat
      nlinarith [hcast]
    have hprod' : ((1 : ℕ) : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) *
        (1 + menonFinalRangeLadderEta x) := by simpa using hprod
    have : 1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) *
        (1 + menonFinalRangeLadderEta x)⌋₊ := Nat.le_floor hprod'
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one this)
  have hlogN : Real.log ((⌊(menonFinalRangeTopNat x : ℝ) *
      (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤ 2 * Real.log x := by
    have hlogMono := Real.log_le_log hNpos hN
    have hlogSix : Real.log (6 * x) = Real.log 6 + Real.log x := by
      rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hx0)]
    have hlog6x : Real.log (6 * x) ≤ 2 * Real.log x := by
      rw [hlogSix]
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hx6
      linarith
    linarith
  have hlogQ0 : 0 < Real.log (menonFinalRangeLadderBase x) := Real.log_pos hQ
  rw [div_le_iff₀ hlogQ0]
  have hsqrt0 : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 (Real.log_pos hxone)
  have hsqrtSq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (Real.log_pos hxone).le
  nlinarith [mul_le_mul_of_nonneg_left hlogQ (by positivity : (0 : ℝ) ≤
    320 * Real.sqrt (Real.log x))]

set_option maxHeartbeats 2000000 in
/-- Uniform fixed-log-power bound for the exact truncated hard-support defect. -/
theorem eventually_menonTruncatedRange_ladderErrorBudget_le_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ x →
      menonHarmonicLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
          (menonTruncatedRangeLadderSteps x) ≤
        (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten,
    eventually_menonTruncatedRangeLadderSteps_le_two_mul_log_pow_eleven,
    eventually_inv_menonFinalRangeLadderBase_le_log_rpow_neg_thirty,
    eventually_menonTruncatedRange_overlapQuotient_le,
    eventually_menonTruncatedRangeLadder_overshoot,
    eventually_const_mul_one_add_log_pow_le_rpow
      (δ := (1 : ℝ)) (c := 1) (by norm_num) (by norm_num) 20,
    Real.tendsto_log_atTop.eventually_ge_atTop ((9011200 : ℝ) ^ 2),
    eventually_ge_atTop (1 : ℝ)] with x hx heta hL hQinv hK htop hlogX hhuge hx1
  intro W hW0 hWx
  rcases hx with ⟨hxone, hlogOne, _, hQ, _, heta0, _⟩
  rcases heta with ⟨_, hetaLe, hrTwo⟩
  have hx0 : 0 < x := lt_trans zero_lt_one hxone
  have hlog0 : 0 < Real.log x := Real.log_pos hxone
  have hlogPow0 : 0 < (Real.log x) ^ (20 : ℕ) := pow_pos hlog0 _
  have hAlo : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hAhi : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hceil := Nat.ceil_lt_add_one hx0.le
    linarith
  have hB : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hU : (menonTruncatedPrimeTopNat x : ℝ) *
      (1 + menonFinalRangeLadderEta x) ≤ 2 * x / (Real.log x) ^ (20 : ℕ) := by
    have htopNat : (menonTruncatedPrimeTopNat x : ℝ) ≤ menonTruncatedPrimeTop x := by
      rw [menonTruncatedPrimeTopNat]
      exact Nat.floor_le (by rw [menonTruncatedPrimeTop]; positivity)
    rw [menonTruncatedPrimeTop] at htopNat
    calc
      (menonTruncatedPrimeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x) ≤
        (x / (Real.log x) ^ (20 : ℕ)) * 2 :=
          mul_le_mul htopNat hrTwo (by linarith) (by positivity)
      _ = 2 * x / (Real.log x) ^ (20 : ℕ) := by ring
  have hqInvNat : 1 / menonFinalRangeLadderBase x ≤
      1 / (Real.log x) ^ (30 : ℕ) := by
    simpa [Real.rpow_neg hlog0.le, Real.rpow_natCast] using hQinv
  have hD :
      ((⌈x⌉₊ : ℝ) + (menonFinalRangeTopNat x : ℝ)) *
            menonFinalRangeLadderEta x ^ 2 +
          5 * menonFinalRangeLadderEta x *
            ((menonTruncatedPrimeTopNat x : ℝ) *
              (1 + menonFinalRangeLadderEta x)) +
          (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
            menonFinalRangeLadderEta x) / menonFinalRangeLadderBase x + 5 +
          (menonFinalRangeTopNat x : ℝ) / menonFinalRangeLadderBase x ^ 2 ≤
        64 * x / (Real.log x) ^ (20 : ℕ) := by
    have hetaSq : menonFinalRangeLadderEta x ^ 2 ≤
        4 / (Real.log x) ^ (20 : ℕ) := by
      have := pow_le_pow_left₀ heta0 hetaLe 2
      calc
        menonFinalRangeLadderEta x ^ 2 ≤ (2 / (Real.log x) ^ (10 : ℕ)) ^ 2 := this
        _ = 4 / (Real.log x) ^ (20 : ℕ) := by
          field_simp
          ring
    have hInvSq : 1 / menonFinalRangeLadderBase x ^ 2 ≤
        1 / (Real.log x) ^ (60 : ℕ) := by
      calc
        1 / menonFinalRangeLadderBase x ^ 2 =
            (1 / menonFinalRangeLadderBase x) ^ 2 := by ring
        _ ≤ (1 / (Real.log x) ^ (30 : ℕ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hqInvNat 2
        _ = 1 / (Real.log x) ^ (60 : ℕ) := by
          field_simp
    have hlogPowers :
        1 / (Real.log x) ^ (60 : ℕ) ≤ 1 / (Real.log x) ^ (20 : ℕ) ∧
        1 / (Real.log x) ^ (40 : ℕ) ≤ 1 / (Real.log x) ^ (20 : ℕ) ∧
        1 / (Real.log x) ^ (30 : ℕ) ≤ 1 / (Real.log x) ^ (20 : ℕ) := by
      have h60 : (Real.log x) ^ (20 : ℕ) ≤ (Real.log x) ^ (60 : ℕ) :=
        pow_le_pow_right₀ hlogOne (by omega)
      have h40 : (Real.log x) ^ (20 : ℕ) ≤ (Real.log x) ^ (40 : ℕ) :=
        pow_le_pow_right₀ hlogOne (by omega)
      have h30 : (Real.log x) ^ (20 : ℕ) ≤ (Real.log x) ^ (30 : ℕ) :=
        pow_le_pow_right₀ hlogOne (by omega)
      constructor
      · exact one_div_le_one_div_of_le (pow_pos hlog0 20) h60
      constructor
      · exact one_div_le_one_div_of_le (pow_pos hlog0 20) h40
      · exact one_div_le_one_div_of_le (pow_pos hlog0 20) h30
    have hfive : 5 ≤ 5 * x / (Real.log x) ^ (20 : ℕ) := by
      have hlogPowLeX : (Real.log x) ^ (20 : ℕ) ≤ x := by
        have hmono : (Real.log x) ^ (20 : ℕ) ≤ (1 + Real.log x) ^ (20 : ℕ) :=
          pow_le_pow_left₀ hlog0.le (by linarith) 20
        exact hmono.trans (by simpa only [one_mul, Real.rpow_one] using hlogX)
      rw [le_div_iff₀ hlogPow0]
      nlinarith
    have hterm1 : ((⌈x⌉₊ : ℝ) + (menonFinalRangeTopNat x : ℝ)) *
        menonFinalRangeLadderEta x ^ 2 ≤ 20 * x / (Real.log x) ^ (20 : ℕ) := by
      have hsum : (⌈x⌉₊ : ℝ) + (menonFinalRangeTopNat x : ℝ) ≤ 5 * x := by linarith
      calc
        ((⌈x⌉₊ : ℝ) + (menonFinalRangeTopNat x : ℝ)) *
            menonFinalRangeLadderEta x ^ 2 ≤ 5 * x *
              (4 / (Real.log x) ^ (20 : ℕ)) :=
          mul_le_mul hsum hetaSq (by positivity) (by positivity)
        _ = 20 * x / (Real.log x) ^ (20 : ℕ) := by ring
    have hterm2 : 5 * menonFinalRangeLadderEta x *
        ((menonTruncatedPrimeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x)) ≤
        20 * x / (Real.log x) ^ (20 : ℕ) := by
      have hraw := mul_le_mul hetaLe hU (by positivity) (by positivity)
      have hlogTen : 1 ≤ (Real.log x) ^ (10 : ℕ) := one_le_pow₀ hlogOne
      calc
        5 * menonFinalRangeLadderEta x *
            ((menonTruncatedPrimeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x)) ≤
          5 * (2 / (Real.log x) ^ (10 : ℕ)) *
            (2 * x / (Real.log x) ^ (20 : ℕ)) := by nlinarith
        _ ≤ 20 * x / (Real.log x) ^ (20 : ℕ) := by
          rw [show 5 * (2 / (Real.log x) ^ (10 : ℕ)) *
              (2 * x / (Real.log x) ^ (20 : ℕ)) =
            (20 * x / (Real.log x) ^ (20 : ℕ)) /
              (Real.log x) ^ (10 : ℕ) by ring]
          exact div_le_self (by positivity) hlogTen
    have hterm3 : (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
        menonFinalRangeLadderEta x) / menonFinalRangeLadderBase x ≤
        16 * x / (Real.log x) ^ (20 : ℕ) := by
      have hsum : (⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ) ≤ 8 * x := by linarith
      have hraw : (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
          menonFinalRangeLadderEta x) * (1 / menonFinalRangeLadderBase x) ≤
          (8 * x) * (2 / (Real.log x) ^ (10 : ℕ)) *
            (1 / (Real.log x) ^ (30 : ℕ)) := by gcongr
      calc
        (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
            menonFinalRangeLadderEta x) / menonFinalRangeLadderBase x =
          (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
            menonFinalRangeLadderEta x) * (1 / menonFinalRangeLadderBase x) := by ring
        _ ≤ (8 * x) * (2 / (Real.log x) ^ (10 : ℕ)) *
            (1 / (Real.log x) ^ (30 : ℕ)) := hraw
        _ = 16 * x / (Real.log x) ^ (40 : ℕ) := by
          rw [show (Real.log x) ^ (40 : ℕ) =
            (Real.log x) ^ (10 : ℕ) * (Real.log x) ^ (30 : ℕ) by ring]
          field_simp
          norm_num
        _ ≤ 16 * x / (Real.log x) ^ (20 : ℕ) := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hlogPowers.2.1 (by positivity : (0 : ℝ) ≤ 16 * x)
    have hterm5 : (menonFinalRangeTopNat x : ℝ) /
        menonFinalRangeLadderBase x ^ 2 ≤
        3 * x / (Real.log x) ^ (20 : ℕ) := by
      calc
        (menonFinalRangeTopNat x : ℝ) / menonFinalRangeLadderBase x ^ 2 =
            (menonFinalRangeTopNat x : ℝ) *
              (1 / menonFinalRangeLadderBase x ^ 2) := by ring
        _ ≤ 3 * x * (1 / (Real.log x) ^ (60 : ℕ)) :=
          mul_le_mul hB hInvSq (by positivity) (by positivity)
        _ ≤ 3 * x * (1 / (Real.log x) ^ (20 : ℕ)) :=
          mul_le_mul_of_nonneg_left hlogPowers.1 (by positivity)
        _ = 3 * x / (Real.log x) ^ (20 : ℕ) := by ring
    calc
      _ ≤ 20 * x / (Real.log x) ^ (20 : ℕ) +
            20 * x / (Real.log x) ^ (20 : ℕ) +
            16 * x / (Real.log x) ^ (20 : ℕ) +
            5 * x / (Real.log x) ^ (20 : ℕ) +
            3 * x / (Real.log x) ^ (20 : ℕ) := by gcongr
      _ = 64 * x / (Real.log x) ^ (20 : ℕ) := by ring
  have hsum :
      (menonTruncatedRangeLadderSteps x : ℝ) *
        (((⌈x⌉₊ : ℝ) + (menonFinalRangeTopNat x : ℝ)) *
              menonFinalRangeLadderEta x ^ 2 +
            5 * menonFinalRangeLadderEta x *
              ((menonTruncatedPrimeTopNat x : ℝ) *
                (1 + menonFinalRangeLadderEta x)) +
            (((⌈x⌉₊ : ℝ) + 2 * (menonFinalRangeTopNat x : ℝ)) *
              menonFinalRangeLadderEta x) / menonFinalRangeLadderBase x + 5 +
            (menonFinalRangeTopNat x : ℝ) / menonFinalRangeLadderBase x ^ 2) ≤
        128 * x / (Real.log x) ^ (9 : ℕ) := by
    have hmul := mul_le_mul hL hD (by positivity) (by positivity)
    calc
      _ ≤ (2 * (Real.log x) ^ (11 : ℕ)) *
          (64 * x / (Real.log x) ^ (20 : ℕ)) := hmul
      _ = 128 * x / (Real.log x) ^ (9 : ℕ) := by
        field_simp
        ring
  have hscale : ((1 + menonFinalRangeLadderEta x) / (⌈x⌉₊ : ℝ)) ^ 2 ≤
      4 / x ^ 2 := by
    have hquot : (1 + menonFinalRangeLadderEta x) / (⌈x⌉₊ : ℝ) ≤ 2 / x :=
      (div_le_div_iff₀ (by positivity : (0 : ℝ) < (⌈x⌉₊ : ℝ)) hx0).2 (by
        nlinarith [mul_le_mul hrTwo hAlo (by positivity) (by positivity)])
    calc
      ((1 + menonFinalRangeLadderEta x) / (⌈x⌉₊ : ℝ)) ^ 2 ≤ (2 / x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hquot 2
      _ = 4 / x ^ 2 := by ring
  have hN : ((⌊(menonFinalRangeTopNat x : ℝ) *
      (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤ 6 * x := by
    calc
      ((⌊(menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤
          (menonFinalRangeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x) :=
        Nat.floor_le (by positivity)
      _ ≤ 6 * x := by nlinarith
  have hmean : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 *
      ((⌊(menonFinalRangeTopNat x : ℝ) *
        (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) ≤ 55 * x := by
    have hpi := Real.pi_lt_four
    have he := Real.exp_one_lt_d9
    nlinarith
  have hclosed := menonHarmonicLadderErrorBudget_le_top
    (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (Q := menonFinalRangeLadderBase x) (eta := menonFinalRangeLadderEta x)
    (U := (menonTruncatedPrimeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x))
    (W := W) hQ heta0 hW0 htop
  have hraw : menonHarmonicLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
      (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
      (menonTruncatedRangeLadderSteps x) ≤
      (4 / x ^ 2) * (55 * x) * (320 * Real.sqrt (Real.log x)) *
        (128 * x / (Real.log x) ^ (9 : ℕ)) := by
    have hquotient0 : 0 ≤ Real.log ((⌊(menonFinalRangeTopNat x : ℝ) *
        (1 + menonFinalRangeLadderEta x)⌋₊ : ℕ) : ℝ) /
        Real.log (menonFinalRangeLadderBase x) := by
      have htopOneNat : 1 ≤ menonFinalRangeTopNat x := by
        rw [menonFinalRangeTopNat]
        apply Nat.le_floor
        norm_num
        nlinarith
      have hprod : (1 : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x) := by
        have hcast : (1 : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) := by
          exact_mod_cast htopOneNat
        nlinarith [hcast]
      have hprod' : ((1 : ℕ) : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x) := by simpa using hprod
      have hfloorOne : (1 : ℕ) ≤ ⌊(menonFinalRangeTopNat x : ℝ) *
          (1 + menonFinalRangeLadderEta x)⌋₊ := by
        exact Nat.le_floor hprod'
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hfloorOne))
        (Real.log_nonneg hQ.le)
    exact hclosed.trans (by gcongr)
  have hconst : (9011200 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [Real.le_sqrt (by norm_num)]
    · simpa only [sq] using hhuge
    · exact hlog0.le
  have hmajor : (4 / x ^ 2) * (55 * x) * (320 * Real.sqrt (Real.log x)) *
      (128 * x / (Real.log x) ^ (9 : ℕ)) ≤
      (Real.log x) ^ (-(8 : ℝ)) := by
    have hrpow : (Real.log x) ^ (-(8 : ℝ)) =
        1 / (Real.log x) ^ (8 : ℕ) := by
      rw [Real.rpow_neg hlog0.le]
      norm_num [Real.rpow_natCast]
    rw [hrpow]
    have hsqrtSq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hlog0.le
    have hsqrtBound : (9011200 : ℝ) * Real.sqrt (Real.log x) ≤ Real.log x := by
      have hmul := mul_le_mul_of_nonneg_right hconst
        (Real.sqrt_nonneg (Real.log x))
      nlinarith
    have hnormalize : (4 / x ^ 2) * (55 * x) * (320 * Real.sqrt (Real.log x)) *
        (128 * x / (Real.log x) ^ (9 : ℕ)) =
        (9011200 * Real.sqrt (Real.log x)) / (Real.log x) ^ (9 : ℕ) := by
      field_simp
      ring
    rw [hnormalize, div_le_iff₀ (pow_pos hlog0 9)]
    calc
      (9011200 : ℝ) * Real.sqrt (Real.log x) ≤ Real.log x := hsqrtBound
      _ = (1 / (Real.log x) ^ (8 : ℕ)) * (Real.log x) ^ (9 : ℕ) := by
        field_simp
  exact hraw.trans hmajor

end

end RHTower.Sieve
