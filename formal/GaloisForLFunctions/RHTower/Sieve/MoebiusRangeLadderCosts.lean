import GaloisForLFunctions.RHTower.Sieve.MoebiusRangeLadderSchedule
import GaloisForLFunctions.RHTower.Sieve.PowerWeightBound

/-!
# The cost of each range of the ladder

At the schedule of `Sieve/MoebiusRangeLadderSchedule`, every range contributes at most
`1500·M²/(2^j·log ν)` to the Möbius window: the rough class costs `90M²/log ν_j` (Turán, with
harmonic mass `≥ ½ log ν_j`), the ladder error `44M²(η_j + 6/R_j)`, and the cofactor term is
exponentially small — for `j = 0` by the mean value theorem below `M/W`, for `j + 1` because the
threshold gap `R_{j+1}^{-1/(8·2^j)} = exp(-ν_j⁸/(8·2^j))` beats the amplification
`(8ℓ+8)^ℓ`, `ℓ ≤ 3ν_j⁶ + 1`.  Summing the geometric series gives `3000·M²/log ν`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

theorem two_mul_le_exp_self (u : ℝ) : 2 * u ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u / 2)
  have hsq : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rcases le_or_gt 0 (u / 2 + 1) with h0 | h0
  · have := pow_le_pow_left₀ h0 h 2
    nlinarith [sq_nonneg (u / 2 - 1)]
  · have := Real.exp_pos u
    linarith

/-- A natural power as an exponential. -/
theorem pow_eq_exp_nat_mul_log {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n = Real.exp (n * Real.log t) := by
  rw [Real.exp_nat_mul, Real.exp_log ht]

/-- **The balance of one amplification step.**  For `t ≥ 2880` and `u = log t`, the
threshold gap `t⁸/(8u)` beats the amplification exponent `(3t⁶+1)(4+6u)` with room for every
polynomial factor. -/
theorem rangeLadder_succ_exponent_nonpos {t u : ℝ} (ht : 2880 ≤ t) (hu1 : 1 ≤ u) (hut : u ≤ t)
    (hu2 : u ^ 2 ≤ 4 * t) :
    10 + 30 * u + 3 * t + 3 * t ^ 5 + (3 * t ^ 6 + 1) * (4 + 6 * u) - t ^ 8 / (8 * u) ≤ 0 := by
  have ht1 : 1 ≤ t := by linarith
  have ht5 : 1 ≤ t ^ 5 := one_le_pow₀ ht1
  have ht6 : t ^ 5 ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht6u : t ^ 6 ≤ t ^ 6 * u := le_mul_of_one_le_right (by positivity) hu1
  have hsum : 10 + 30 * u + 3 * t + 3 * t ^ 5 + (3 * t ^ 6 + 1) * (4 + 6 * u)
      ≤ 90 * (t ^ 6 * u) := by
    have a1 : u ≤ t ^ 6 * u := by nlinarith
    have a2 : t ≤ t ^ 6 * u := by
      have : t ≤ t ^ 6 := by
        calc t = t ^ 1 := (pow_one t).symm
          _ ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
      linarith
    nlinarith
  have hu0 : 0 < u := by linarith
  have hbig : 90 * (t ^ 6 * u) ≤ t ^ 8 / (8 * u) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : 720 * u ^ 2 ≤ t ^ 2 := by nlinarith
    have h2 : t ^ 8 = t ^ 6 * t ^ 2 := by ring
    rw [h2]
    have ht6p : 0 ≤ t ^ 6 := by positivity
    nlinarith
  linarith

theorem log_ge_four_of_ge {ν : ℝ} (hν : 3000 ≤ ν) : 4 ≤ Real.log ν := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have : Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 4
  linarith

/-- The integer top of a range is at least its base. -/
theorem rangeLadderBase_le_top {ν : ℝ} (hν : 0 < ν) (j : ℕ) :
    rangeLadderBase ν j ≤ rangeLadderTop ν j := by
  refine Nat.le_floor ?_
  rw [rangeLadderTopReal]
  have h1 : (1 : ℝ) ≤ (1 + rangeLadderEta ν j) ^ rangeLadderSteps ν j :=
    one_le_pow₀ (by linarith [rangeLadderEta_pos ν j])
  have h0 := rangeLadderR_pos hν j
  rw [rangeLadderR] at h0 ⊢
  nlinarith

theorem two_le_rangeLadderBase {ν : ℝ} (hν : 0 < ν) (j : ℕ) : 2 ≤ rangeLadderBase ν j := by
  have h := one_lt_rangeLadderR hν j
  rw [rangeLadderR] at h
  exact_mod_cast h

theorem card_rangeLadderP_le_top (ν : ℝ) (j : ℕ) :
    ((rangeLadderP ν j).card : ℝ) ≤ (rangeLadderTop ν j : ℝ) := by
  classical
  have hsub : rangeLadderP ν j ⊆ Finset.Icc 1 (rangeLadderTop ν j) := by
    intro p hp
    rw [rangeLadderP, mem_primesRange] at hp
    exact Finset.mem_Icc.mpr ⟨hp.1.one_lt.le, hp.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc, add_tsub_cancel_right] at hc
  exact_mod_cast hc

/-- **The harmonic mass of range `j` is at least `½ log ν_j`.** -/
theorem rangeLadder_harmonic_ge {ν : ℝ} (hν : 3000 ≤ ν) (hc : 4 * mertensFirstConst + 1 ≤ ν)
    (j : ℕ) :
    Real.log (rangeLadderNu ν j) / 2 ≤ ∑ p ∈ rangeLadderP ν j, 1 / (p : ℝ) := by
  have hν0 : 0 < ν := by linarith
  set t := rangeLadderNu ν j with htdef
  have ht : ν ≤ t := le_rangeLadderNu (by linarith) j
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hmass := sum_inv_primesRange_ge_logLog_diff (two_le_rangeLadderBase hν0 j)
    (rangeLadderBase_le_top hν0 j)
  rw [← rangeLadderP] at hmass
  have hRlo := log_rangeLadderR_ge ν j
  have hRhi := log_rangeLadderR_le hν0 j
  rw [← htdef] at hRlo hRhi
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht1
  have ht4' : t ≤ t ^ 4 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
  -- the base
  have hz₀ : ((rangeLadderBase ν j : ℕ) : ℝ) = rangeLadderR ν j := rfl
  have hlogz₀pos : 0 < Real.log (rangeLadderR ν j) := by linarith
  have hll₀ : Real.log (Real.log (rangeLadderR ν j)) ≤ Real.log 2 + 4 * Real.log t := by
    have h1 : Real.log (rangeLadderR ν j) ≤ 2 * t ^ 4 := by linarith
    have h2 := Real.log_le_log hlogz₀pos h1
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  -- the top
  have hQ := log_rangeLadderTopReal_ge hν0.le hν0 j
  rw [← htdef] at hQ
  have hQ0 := rangeLadderTopReal_pos hν0 j
  have hQ2 : 2 ≤ rangeLadderTopReal ν j := by
    have : Real.log 2 ≤ Real.log (rangeLadderTopReal ν j) := by
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have : (0 : ℝ) ≤ t ^ 5 := by positivity
      linarith
    exact (Real.log_le_log_iff (by norm_num) hQ0).mp this
  have hztop : rangeLadderTopReal ν j / 2 ≤ (rangeLadderTop ν j : ℝ) := by
    have := Nat.lt_floor_add_one (rangeLadderTopReal ν j)
    rw [rangeLadderTop]
    linarith
  have hlogz : t ^ 5 ≤ Real.log (rangeLadderTop ν j : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hztop
    rw [Real.log_div hQ0.ne' (by norm_num)] at h1
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hll : 5 * Real.log t ≤ Real.log (Real.log (rangeLadderTop ν j : ℝ)) := by
    have := Real.log_le_log (by positivity) hlogz
    rwa [Real.log_pow] at this
  -- the error
  have herr : 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log (rangeLadderR ν j)) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hlogz₀pos]
    linarith
  have hlt : 4 ≤ Real.log t := by
    have := log_ge_four_of_ge hν
    linarith [Real.log_le_log hν0 ht]
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [hz₀] at hmass
  linarith

/-- **The rough class of range `j`.** -/
theorem rangeLadder_rough_le {ν : ℝ} (hν : 3000 ≤ ν) (hc : 4 * mertensFirstConst + 1 ≤ ν)
    (j : ℕ) (M : ℕ) {W : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M) (htop : (rangeLadderTop ν j : ℝ) ≤ M) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet (rangeLadderP ν j) M) w‖ ^ 2)
      ≤ 90 * (M : ℝ) ^ 2 / Real.log (rangeLadderNu ν j) := by
  have hν0 : 0 < ν := by linarith
  have hA := rangeLadder_harmonic_ge hν hc j
  have hlt : 4 ≤ Real.log (rangeLadderNu ν j) := by
    have := log_ge_four_of_ge hν
    linarith [Real.log_le_log hν0 (le_rangeLadderNu (by linarith) j)]
  set A := ∑ p ∈ rangeLadderP ν j, 1 / (p : ℝ) with hAdef
  have hA0 : 0 < A := by linarith
  have hbase := integral_Icc_normSq_roughPoly_le_harmonic (rangeLadderP_prime ν j) M hW hA0
  have hcard := card_rangeLadderP_le_top ν j
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hcoef : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) ≤ 15 * M := by nlinarith
  have hcoef0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos; have := Real.exp_pos 1; positivity
  have hfrac : (M : ℝ) / A + 2 * ((rangeLadderP ν j).card : ℝ) / A ≤ 3 * M / A := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hA0.le
  refine hbase.trans ?_
  calc (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
        * ((M : ℝ) / A + 2 * ((rangeLadderP ν j).card : ℝ) / A)
      ≤ (15 * M) * (3 * M / A) := mul_le_mul hcoef hfrac (by positivity) (by positivity)
    _ = 45 * (M : ℝ) ^ 2 / A := by ring
    _ ≤ 45 * (M : ℝ) ^ 2 / (Real.log (rangeLadderNu ν j) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hA
    _ = 90 * (M : ℝ) ^ 2 / Real.log (rangeLadderNu ν j) := by field_simp; ring

/-- **The ladder error of range `j`.** -/
theorem rangeLadder_error_le {ν : ℝ} (hν : 0 < ν) (j : ℕ) (M : ℕ) {W : ℝ} (hW : 1 ≤ W)
    (hWM : W ≤ M) :
    (∫ w in Set.Icc (-W) W,
        ‖ramareLadderError (rangeLadderP ν j) M (rangeLadderR ν j) (rangeLadderEta ν j)
          (rangeLadderSteps ν j) w‖ ^ 2)
      ≤ 44 * (M : ℝ) ^ 2 * (rangeLadderEta ν j + 6 / rangeLadderR ν j) := by
  have hR1 := one_lt_rangeLadderR hν j
  have hη := rangeLadderEta_pos ν j
  have hη1 := rangeLadderEta_le_one hν.le j
  have hbase := integral_normSq_ramareLadderError_le_sharp M hR1.le hη.le hW
    (rangeLadderSteps ν j) (rangeLadderP_prime ν j)
    (fun p hp => (rangeLadderP_bounds ν j p hp).1)
  refine hbase.trans ?_
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hfl : ((⌊(M : ℝ) * (1 + rangeLadderEta ν j)⌋₊ : ℕ) : ℝ) ≤ 2 * M := by
    have := Nat.floor_le (show 0 ≤ (M : ℝ) * (1 + rangeLadderEta ν j) by positivity)
    nlinarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hcoef : 5 * Real.pi / 2 * W
      + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + rangeLadderEta ν j)⌋₊ : ℕ) : ℝ) ≤ 22 * M := by
    have := Real.exp_pos 1
    nlinarith
  have hR0 : 0 < rangeLadderR ν j := by linarith
  have hsec : rangeLadderEta ν j * M + 6 * M / rangeLadderR ν j
      = M * (rangeLadderEta ν j + 6 / rangeLadderR ν j) := by ring
  rw [hsec]
  have hsec0 : 0 ≤ (M : ℝ) * (rangeLadderEta ν j + 6 / rangeLadderR ν j) := by positivity
  calc 2 * (5 * Real.pi / 2 * W
        + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + rangeLadderEta ν j)⌋₊ : ℕ) : ℝ))
        * ((M : ℝ) * (rangeLadderEta ν j + 6 / rangeLadderR ν j))
      ≤ 2 * (22 * M) * ((M : ℝ) * (rangeLadderEta ν j + 6 / rangeLadderR ν j)) := by gcongr
    _ = 44 * (M : ℝ) ^ 2 * (rangeLadderEta ν j + 6 / rangeLadderR ν j) := by ring

/-- **The cofactor cost of the first range.** -/
theorem rangeLadder_zero_cost_le {ν : ℝ} (hν : 0 < ν) (M : ℕ) :
    ∑ v ∈ Finset.range (rangeLadderSteps ν 0),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M 0 v
      ≤ rangeLadderSteps ν 0 * (15 * (M : ℝ) ^ 2 * Real.exp (-(ν ^ 4) / 4)) := by
  have hbound : ∀ v ∈ Finset.range (rangeLadderSteps ν 0),
      rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M 0 v
        ≤ 15 * (M : ℝ) ^ 2 * Real.exp (-(ν ^ 4) / 4) := by
    intro v _
    rw [rangeCofactorCost, rangeLadderAlpha_zero]
    have hR := rangeLadderR_pos hν 0
    have h1 : (1 : ℝ) ≤ (1 + rangeLadderEta ν 0) ^ v :=
      one_le_pow₀ (by linarith [rangeLadderEta_pos ν 0])
    have hS : rangeLadderR ν 0 ≤ rangeLadderR ν 0 * (1 + rangeLadderEta ν 0) ^ v :=
      le_mul_of_one_le_right hR.le h1
    have hexp : Real.exp (ν ^ 4) ≤ rangeLadderR ν 0 := by
      have := exp_le_rangeLadderR ν 0
      rwa [rangeLadderNu, pow_zero, pow_one] at this
    have hneg : (-2 * (1 / 8 : ℝ)) ≤ 0 := by norm_num
    have h2 := Real.rpow_le_rpow_of_nonpos hR hS hneg
    have h3 := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp hneg
    have h4 : Real.exp (ν ^ 4) ^ (-2 * (1 / 8 : ℝ)) = Real.exp (-(ν ^ 4) / 4) := by
      rw [← Real.exp_mul]; congr 1; ring
    rw [h4] at h3
    have hM : (0 : ℝ) ≤ 15 * (M : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (h2.trans h3) hM
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The amplification exponent of a pair of consecutive ranges is at most `⌈3ν_j⁶⌉`. -/
theorem rangeLadder_ceil_ratio_le {ν : ℝ} (hν : 2 ≤ ν) (j v r : ℕ)
    (hv : v ≤ rangeLadderSteps ν (j + 1)) :
    ⌈Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
        / Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r)⌉₊
      ≤ ⌈3 * rangeLadderNu ν j ^ 6⌉₊ := by
  have hν0 : 0 < ν := by linarith
  refine Nat.ceil_mono ?_
  have ht0 := rangeLadderNu_pos hν0 j
  have hη := rangeLadderEta_pos ν j
  have hη' := rangeLadderEta_pos ν (j + 1)
  have hRj := one_lt_rangeLadderR hν0 j
  have hRj' := one_lt_rangeLadderR hν0 (j + 1)
  have hSr : rangeLadderR ν j ≤ rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r :=
    le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith))
  have hlogS : rangeLadderNu ν j ^ 4 ≤ Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r) :=
    (log_rangeLadderR_ge ν j).trans (Real.log_le_log (by linarith) hSr)
  have hTv : rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v
      ≤ rangeLadderTopReal ν (j + 1) := by
    rw [rangeLadderTopReal]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hv)
      (rangeLadderR_pos hν0 _).le
  have hTv1 : 1 ≤ rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v := by
    have := le_mul_of_one_le_right (show 0 ≤ rangeLadderR ν (j + 1) by linarith)
      (one_le_pow₀ (show 1 ≤ 1 + rangeLadderEta ν (j + 1) by linarith) : (1 : ℝ) ≤ _ ^ v)
    linarith
  have hlogT : Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
      ≤ 3 * rangeLadderNu ν j ^ 10 := by
    have h1 := Real.log_le_log (by linarith) hTv
    have h2 := log_rangeLadderTopReal_le hν (j + 1)
    rw [rangeLadderNu_succ] at h2
    have : (rangeLadderNu ν j ^ 2) ^ 5 = rangeLadderNu ν j ^ 10 := by ring
    linarith
  have hlogT0 : 0 ≤ Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v) :=
    Real.log_nonneg hTv1
  have hS0 : 0 < rangeLadderNu ν j ^ 4 := by positivity
  calc Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
        / Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r)
      ≤ 3 * rangeLadderNu ν j ^ 10 / rangeLadderNu ν j ^ 4 :=
        div_le_div₀ (by positivity) hlogT hS0 hlogS
    _ = 3 * rangeLadderNu ν j ^ 6 := by field_simp




/-- **The cofactor cost of a later range.** -/
theorem rangeLadder_succ_cost_le {ν : ℝ} (hν : 2 ≤ ν) (M : ℕ) (j : ℕ) :
    ∑ v ∈ Finset.range (rangeLadderSteps ν (j + 1)),
        rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M
          (j + 1) v
      ≤ rangeLadderSteps ν (j + 1) * (rangeLadderSteps ν j
          * (15 * (8 * ⌈3 * rangeLadderNu ν j ^ 6⌉₊ + 8 : ℝ) ^ ⌈3 * rangeLadderNu ν j ^ 6⌉₊
            * rangeLadderTopReal ν j * (M : ℝ) ^ 2
            * Real.exp (-(rangeLadderNu ν j ^ 8 / (8 * 2 ^ j))))) := by
  have hν0 : 0 < ν := by linarith
  set ℓ := ⌈3 * rangeLadderNu ν j ^ 6⌉₊ with hℓdef
  have hη := rangeLadderEta_pos ν j
  have hη' := rangeLadderEta_pos ν (j + 1)
  have hR0 := rangeLadderR_pos hν0 j
  have hR0' := rangeLadderR_pos hν0 (j + 1)
  have hexp' : Real.exp (rangeLadderNu ν j ^ 8) ≤ rangeLadderR ν (j + 1) := by
    have := exp_le_rangeLadderR ν (j + 1)
    rwa [rangeLadderNu_succ, ← pow_mul] at this
  have hbound : ∀ v ∈ Finset.range (rangeLadderSteps ν (j + 1)),
      rangeCofactorCost (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν) rangeLadderAlpha M
          (j + 1) v
        ≤ rangeLadderSteps ν j
          * (15 * (8 * ℓ + 8 : ℝ) ^ ℓ * rangeLadderTopReal ν j * (M : ℝ) ^ 2
            * Real.exp (-(rangeLadderNu ν j ^ 8 / (8 * 2 ^ j)))) := by
    intro v hv
    have hv' : v ≤ rangeLadderSteps ν (j + 1) := (Finset.mem_range.mp hv).le
    rw [rangeCofactorCost]
    have hTv : rangeLadderR ν (j + 1) ≤ rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v :=
      le_mul_of_one_le_right hR0'.le (one_le_pow₀ (by linarith))
    have hneg : 2 * rangeLadderAlpha j - 2 * rangeLadderAlpha (j + 1) ≤ 0 := by
      rw [rangeLadderAlpha_sub]; have : (0 : ℝ) < 1 / (8 * 2 ^ j) := by positivity
      linarith
    have hT := (Real.rpow_le_rpow_of_nonpos hR0' hTv hneg).trans
      (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp' hneg)
    rw [← Real.exp_mul, rangeLadderAlpha_sub] at hT
    have hT' : Real.exp (rangeLadderNu ν j ^ 8 * -(1 / (8 * 2 ^ j)))
        = Real.exp (-(rangeLadderNu ν j ^ 8 / (8 * 2 ^ j))) := by congr 1; ring
    rw [hT', ← rangeLadderAlpha_sub] at hT
    have hterm : ∀ r ∈ Finset.range (rangeLadderSteps ν j),
        15 * (8 * ⌈Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
              / Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r)⌉₊ + 8 : ℝ)
            ^ ⌈Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
              / Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r)⌉₊
          * (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r) * (M : ℝ) ^ 2
          * (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
              ^ (2 * rangeLadderAlpha j - 2 * rangeLadderAlpha (j + 1))
        ≤ 15 * (8 * ℓ + 8 : ℝ) ^ ℓ * rangeLadderTopReal ν j * (M : ℝ) ^ 2
            * Real.exp (-(rangeLadderNu ν j ^ 8 / (8 * 2 ^ j))) := by
      intro r hr
      set a := ⌈Real.log (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
              / Real.log (rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r)⌉₊ with hadef
      have ha : a ≤ ℓ := rangeLadder_ceil_ratio_le hν j v r hv'
      have hpow : (8 * a + 8 : ℝ) ^ a ≤ (8 * ℓ + 8 : ℝ) ^ ℓ := by
        have haR : (a : ℝ) ≤ ℓ := by exact_mod_cast ha
        calc (8 * a + 8 : ℝ) ^ a ≤ (8 * ℓ + 8 : ℝ) ^ a :=
              pow_le_pow_left₀ (by positivity) (by linarith) a
          _ ≤ (8 * ℓ + 8 : ℝ) ^ ℓ :=
              pow_le_pow_right₀ (by have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith) ha
      have hS : rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r ≤ rangeLadderTopReal ν j := by
        rw [rangeLadderTopReal]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hr).le) hR0.le
      have hS0 : 0 ≤ rangeLadderR ν j * (1 + rangeLadderEta ν j) ^ r := by positivity
      have hTp : 0 ≤ (rangeLadderR ν (j + 1) * (1 + rangeLadderEta ν (j + 1)) ^ v)
          ^ (2 * rangeLadderAlpha j - 2 * rangeLadderAlpha (j + 1)) :=
        Real.rpow_nonneg (by positivity) _
      have hM : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
      have hQ0 := (rangeLadderTopReal_pos hν0 j).le
      have hB0 : (0 : ℝ) ≤ 15 * (8 * ℓ + 8 : ℝ) ^ ℓ := by positivity
      have hA0 : (0 : ℝ) ≤ 15 * (8 * a + 8 : ℝ) ^ a := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hS hS0 hB0) hM)
        hT hTp (by positivity)
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]




theorem exp_ten_ge : (12960 : ℝ) ≤ Real.exp 10 := by
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (12960 : ℝ) ≤ 2.7 ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) he 10

/-- **The numerical core of an amplification step.** -/
theorem rangeLadder_succ_numeric_core {t g lν ν : ℝ} (ht : 2880 ≤ t) (hg1 : 1 ≤ g)
    (hgu : g * lν = Real.log t) (hlν : 1 ≤ lν) (hνt : ν ≤ t) :
    12960 * t ^ 25 * g ^ 4 * lν * Real.exp (3 * ν)
        * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * Real.log t)) * Real.exp (3 * t ^ 5)
        * Real.exp (-(t ^ 8 / (8 * g))) ≤ 1 := by
  set u := Real.log t with hudef
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hu1 : 1 ≤ u := by nlinarith
  have hut : u ≤ t := by have := Real.log_le_sub_one_of_pos ht0; linarith
  have hu2 : u ^ 2 ≤ 4 * t := log_sq_le_four_mul ht1
  have hgu' : g ≤ u := by nlinarith
  have hlu : lν ≤ u := by nlinarith
  have hexp := rangeLadder_succ_exponent_nonpos ht hu1 hut hu2
  have h25 : t ^ 25 = Real.exp (25 * u) := by
    rw [pow_eq_exp_nat_mul_log ht0, hudef]; norm_num
  have h5 : g ^ 4 * lν ≤ Real.exp (5 * u) := by
    have a1 : g ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by linarith) hgu' 4
    have a2 : u ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by linarith) hut 5
    have a3 : t ^ 5 = Real.exp (5 * u) := by rw [pow_eq_exp_nat_mul_log ht0, hudef]; norm_num
    have a4 : g ^ 4 * lν ≤ u ^ 4 * u := mul_le_mul a1 hlu (by linarith) (by positivity)
    nlinarith
  have h3 : Real.exp (3 * ν) ≤ Real.exp (3 * t) := Real.exp_le_exp.mpr (by linarith)
  have hE : Real.exp (-(t ^ 8 / (8 * g))) ≤ Real.exp (-(t ^ 8 / (8 * u))) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hc := exp_ten_ge
  calc 12960 * t ^ 25 * g ^ 4 * lν * Real.exp (3 * ν)
        * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * u)) * Real.exp (3 * t ^ 5)
        * Real.exp (-(t ^ 8 / (8 * g)))
      = 12960 * t ^ 25 * (g ^ 4 * lν) * Real.exp (3 * ν)
        * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * u)) * Real.exp (3 * t ^ 5)
        * Real.exp (-(t ^ 8 / (8 * g))) := by ring
    _ ≤ Real.exp 10 * Real.exp (25 * u) * Real.exp (5 * u) * Real.exp (3 * t)
        * Real.exp ((3 * t ^ 6 + 1) * (4 + 6 * u)) * Real.exp (3 * t ^ 5)
        * Real.exp (-(t ^ 8 / (8 * u))) := by
        rw [h25]
        gcongr
    _ = Real.exp (10 + 30 * u + 3 * t + 3 * t ^ 5 + (3 * t ^ 6 + 1) * (4 + 6 * u)
          - t ^ 8 / (8 * u)) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hexp
    _ = 1 := Real.exp_zero

/-- **The numerical core of the first range.** -/
theorem rangeLadder_zero_numeric_core {ν : ℝ} (hν : 3000 ≤ ν) :
    540 * ν ^ 10 * Real.exp (2 * ν) * Real.exp (-(ν ^ 4) / 4) * Real.log ν ≤ 1 := by
  have hν0 : 0 < ν := by linarith
  have hlog : Real.log ν ≤ ν := by have := Real.log_le_sub_one_of_pos hν0; linarith
  have hν11 : ν ^ 10 * Real.log ν ≤ Real.exp (11 * ν) := by
    have h1 : ν ≤ Real.exp ν := by have := Real.add_one_le_exp ν; linarith
    have h2 : ν ^ 11 ≤ Real.exp ν ^ 11 := pow_le_pow_left₀ hν0.le h1 11
    rw [← Real.exp_nat_mul] at h2
    have h3 : ν ^ 10 * Real.log ν ≤ ν ^ 10 * ν :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h4 : ν ^ 10 * ν = ν ^ 11 := by ring
    push_cast at h2
    linarith
  have h540 : (540 : ℝ) ≤ Real.exp 7 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (540 : ℝ) ≤ 2.7 ^ 7 := by norm_num
      _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he 7
  have hpoly : 7 + 11 * ν + 2 * ν - ν ^ 4 / 4 ≤ 0 := by
    have h2 : 9000000 ≤ ν ^ 2 := by nlinarith
    have h3 : 64 ≤ ν ^ 3 := by nlinarith
    nlinarith
  calc 540 * ν ^ 10 * Real.exp (2 * ν) * Real.exp (-(ν ^ 4) / 4) * Real.log ν
      = 540 * (ν ^ 10 * Real.log ν) * Real.exp (2 * ν) * Real.exp (-(ν ^ 4) / 4) := by ring
    _ ≤ Real.exp 7 * Real.exp (11 * ν) * Real.exp (2 * ν) * Real.exp (-(ν ^ 4) / 4) := by
        have : 0 ≤ ν ^ 10 * Real.log ν :=
          mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
        gcongr
    _ = Real.exp (7 + 11 * ν + 2 * ν - ν ^ 4 / 4) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hpoly
    _ = 1 := Real.exp_zero

end

end RHTower.Sieve
