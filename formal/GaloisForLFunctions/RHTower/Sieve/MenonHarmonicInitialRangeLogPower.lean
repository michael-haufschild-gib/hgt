import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicInitialRangeDefect
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicInitialRangeFullInterval
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAssembly
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

set_option maxHeartbeats 800000 in
theorem eventually_integral_Icc_normSq_menonInitialRange_ladderDefect_le_log_rpow_neg_sixteen :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W : ℝ),
      (((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ) < (hN : ℝ)) →
      (hN : ℝ) ≤ x ^ ((1 : ℝ) / 4) → 1 ≤ W →
      W * ((hN : ℝ) + 1) ≤ 2 * x →
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect
          (menonInitialRangePrimes ((1 : ℝ) / 2) 20 x hN) ⌈x⌉₊
          (menonFinalRangeTopNat x)
          ((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ) (lowEta 20 x)
          (menonInitialRangeSteps ((1 : ℝ) / 2) 20 x hN) w‖ ^ 2) ≤
        (Real.log x) ^ (-(16 : ℝ)) := by
  have hdefect :=
    eventually_integral_Icc_normSq_menonInitialRange_ladderDefect_le_explicit
      (a := (1 : ℝ) / 2) (c := 20) (by norm_num)
  have hQpow := rpow_log_le_highBase (a := (1 : ℝ) / 2) (by norm_num) 100
  have hxpow := burnolEventually_log_pow_le_rpow (δ := (3 : ℝ) / 4) (by norm_num) 100
  have hlarge : ∀ᶠ x : ℝ in atTop, (74400 : ℝ) ≤ (Real.log x) ^ (2 : ℝ) := by
    have ht : Tendsto (fun x : ℝ => (Real.log x) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    exact ht.eventually_ge_atTop 74400
  filter_upwards [hdefect, hQpow, hxpow, hlarge,
    Filter.eventually_ge_atTop (Real.exp 2)] with
      x hdefectx hQpowx hxpowx hlarge hxlarge
  intro hN W hQh hhQuarter hW hWh
  let t := Real.log x
  let Q : ℝ := ((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ)
  let eta := lowEta 20 x
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hxlarge
  have hx1 : 1 < x := lt_of_lt_of_le (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)) hxlarge
  have ht1 : 1 ≤ t := by
    dsimp only [t]
    have htwo : (2 : ℝ) ≤ Real.log x := by
      simpa using Real.log_le_log (Real.exp_pos 2) hxlarge
    linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hQ100 : t ^ 100 ≤ Q := by
    have hp100 : t ^ (100 : ℝ) = t ^ (100 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 100
    rw [← hp100]
    simpa only [t, Q] using hQpowx
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity : 0 < t ^ 100) hQ100
  have hQ1 : 1 ≤ Q := le_trans (one_le_pow₀ ht1) hQ100
  have hh0 : 0 < (hN : ℝ) := lt_trans hQ0 hQh
  have hxQuarter : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hhx : (hN : ℝ) ≤ x := by
    have hquarter_le : x ^ ((1 : ℝ) / 4) ≤ x := by
      calc
        x ^ ((1 : ℝ) / 4) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
        _ = x := Real.rpow_one x
    exact hhQuarter.trans hquarter_le
  have hlogh : Real.log (hN : ℝ) ≤ t / 4 := by
    have hlog := Real.log_le_log hh0 hhQuarter
    rw [Real.log_rpow hx0] at hlog
    dsimp only [t]
    nlinarith
  have ht100x : t ^ 100 ≤ x ^ ((3 : ℝ) / 4) := by
    simpa only [t] using hxpowx
  have hratioHN100 : (hN : ℝ) / x ≤ 1 / t ^ 100 := by
    rw [div_le_div_iff₀ hx0 (by positivity : 0 < t ^ 100)]
    calc
      (hN : ℝ) * t ^ 100 ≤ x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) :=
        mul_le_mul hhQuarter ht100x (pow_nonneg ht0.le _) hxQuarter.le
      _ = x := by
        rw [← Real.rpow_add hx0]
        norm_num
      _ = 1 * x := by ring
  have ht40le100 : t ^ 40 ≤ t ^ 100 := by
    exact pow_le_pow_right₀ ht1 (by norm_num)
  have hratioHN : (hN : ℝ) / x ≤ 1 / t ^ 40 :=
    hratioHN100.trans (one_div_le_one_div_of_le (by positivity) ht40le100)
  have hQinv : 1 / Q ≤ 1 / t ^ 40 := by
    exact (one_div_le_one_div_of_le (by positivity) hQ100).trans
      (one_div_le_one_div_of_le (by positivity) ht40le100)
  have hxinv100 : 1 / x ≤ 1 / t ^ 100 := by
    exact one_div_le_one_div_of_le (by positivity) (ht100x.trans
      (by
        calc
          x ^ ((3 : ℝ) / 4) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
          _ = x := Real.rpow_one x))
  have hxinv : 1 / x ≤ 1 / t ^ 40 :=
    hxinv100.trans (one_div_le_one_div_of_le (by positivity) ht40le100)
  have hQsqInv : 1 / Q ^ 2 ≤ 1 / t ^ 40 := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith [hQ1]
    exact (one_div_le_one_div_of_le (by positivity) hQQ).trans hQinv
  have heta : eta = 1 / t ^ 20 := by
    dsimp only [eta, lowEta]
    rw [Real.rpow_neg ht0.le]
    norm_num
  have heta0 : 0 ≤ eta := by rw [heta]; positivity
  have hetaSq : eta ^ 2 = 1 / t ^ 40 := by
    rw [heta]
    field_simp
  have hetaRatioHN : eta * ((hN : ℝ) / x) ≤ 1 / t ^ 40 := by
    rw [heta]
    have hratio20 : (hN : ℝ) / x ≤ 1 / t ^ 20 := by
      exact hratioHN.trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num : 20 ≤ 40)))
    calc
      (1 / t ^ 20) * ((hN : ℝ) / x) ≤ (1 / t ^ 20) * (1 / t ^ 20) := by
        gcongr
      _ = 1 / t ^ 40 := by field_simp
  have hetaQ : eta / Q ≤ 1 / t ^ 40 := by
    rw [div_eq_mul_inv, heta]
    have hQ20 : 1 / Q ≤ 1 / t ^ 20 := hQinv.trans
      (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ ht1 (by norm_num : 20 ≤ 40)))
    calc
      (1 / t ^ 20) * Q⁻¹ ≤ (1 / t ^ 20) * (1 / t ^ 20) := by
        gcongr
        simpa only [one_div] using hQ20
      _ = 1 / t ^ 40 := by field_simp
  have hbracket :
      (5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
          8 * x * eta / Q + 5 + 3 * x / Q ^ 2) / x ≤
        31 * (1 / t ^ 40) := by
    have heq :
        (5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
            8 * x * eta / Q + 5 + 3 * x / Q ^ 2) / x =
          5 * eta ^ 2 + 10 * eta * ((hN : ℝ) / x) +
            8 * (eta / Q) + 5 * (1 / x) + 3 * (1 / Q ^ 2) := by
      field_simp
    rw [heq, hetaSq]
    nlinarith
  have hpiExp : 4 * (5 * Real.pi + 15 * Real.exp 1) ≤ (400 : ℝ) := by
    have hpi := Real.pi_lt_four
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith
  have hlog6 : Real.log (6 * x) ≤ 6 * t := by
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hx0)]
    have hlogSix : Real.log (6 : ℝ) ≤ 5 := by
      have hsix := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      norm_num at hsix
      exact hsix
    nlinarith
  have htHalf : 1 ≤ t ^ ((1 : ℝ) / 2) := Real.one_le_rpow ht1 (by norm_num)
  have hlogRatio : Real.log (6 * x) / t ^ ((1 : ℝ) / 2) ≤ 6 * t := by
    have hlog60 : 0 ≤ Real.log (6 * x) := Real.log_nonneg (by nlinarith)
    exact (div_le_self hlog60 htHalf).trans hlog6
  have hstep : 2 * Real.log (hN : ℝ) * t ^ (20 : ℝ) ≤ t ^ 21 := by
    have hp20 : t ^ (20 : ℝ) = t ^ (20 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 20
    rw [hp20]
    have ht20 : 0 ≤ t ^ 20 := pow_nonneg ht0.le _
    calc
      2 * Real.log (hN : ℝ) * t ^ 20 ≤ 2 * (t / 4) * t ^ 20 := by gcongr
      _ = (1 / 2 : ℝ) * (t * t ^ 20) := by ring
      _ ≤ 1 * (t * t ^ 20) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg ht0.le ht20)
      _ = t * t ^ 20 := by ring
      _ = t ^ 21 := by ring
  have hnonnegLogRatio : 0 ≤ Real.log (6 * x) / t ^ ((1 : ℝ) / 2) := by
    have h6x : (1 : ℝ) ≤ 6 * x := by linarith
    exact div_nonneg (Real.log_nonneg h6x) (zero_le_one.trans htHalf)
  have hnonnegStep : 0 ≤ 2 * Real.log (hN : ℝ) * t ^ (20 : ℝ) := by
    have hh1 : (1 : ℝ) ≤ (hN : ℝ) := hQ1.trans hQh.le
    have hlognn : 0 ≤ Real.log (hN : ℝ) := Real.log_nonneg hh1
    exact mul_nonneg (mul_nonneg (by norm_num) hlognn) (Real.rpow_nonneg ht0.le _)
  have hbase := hdefectx hN W hQh hhx hW hWh
  have hrearrange :
      (4 / x ^ 2) * ((5 * Real.pi + 15 * Real.exp 1) * x) *
          (Real.log (6 * x) / t ^ ((1 : ℝ) / 2)) *
          ((2 * Real.log (hN : ℝ) * t ^ (20 : ℝ)) *
            (5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
              8 * x * eta / Q + 5 + 3 * x / Q ^ 2)) =
        (4 * (5 * Real.pi + 15 * Real.exp 1)) *
          (Real.log (6 * x) / t ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (hN : ℝ) * t ^ (20 : ℝ)) *
          ((5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
              8 * x * eta / Q + 5 + 3 * x / Q ^ 2) / x) := by
    field_simp
  have hmajor :
      (4 * (5 * Real.pi + 15 * Real.exp 1)) *
          (Real.log (6 * x) / t ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (hN : ℝ) * t ^ (20 : ℝ)) *
          ((5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
              8 * x * eta / Q + 5 + 3 * x / Q ^ 2) / x) ≤
        400 * (6 * t) * t ^ 21 * (31 * (1 / t ^ 40)) := by
    gcongr
  have hfinish : 400 * (6 * t) * t ^ 21 * (31 * (1 / t ^ 40)) ≤
      t ^ (-(16 : ℝ)) := by
    have hlargeNat : (74400 : ℝ) ≤ t ^ 2 := by
      have hp2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 2
      rw [← hp2]
      simpa only [t] using hlarge
    rw [Real.rpow_neg ht0.le]
    have hcalc : (74400 : ℝ) / t ^ 18 ≤ 1 / t ^ 16 := by
      rw [div_le_div_iff₀ (pow_pos ht0 18) (pow_pos ht0 16)]
      have hmul := mul_le_mul_of_nonneg_right hlargeNat (pow_nonneg ht0.le 16)
      calc
        (74400 : ℝ) * t ^ 16 ≤ t ^ 2 * t ^ 16 := hmul
        _ = 1 * t ^ 18 := by ring
    have hExpr : 400 * (6 * t) * t ^ 21 * (31 * (1 / t ^ 40)) =
        (74400 : ℝ) / t ^ 18 := by field_simp; norm_num
    have hp16 : t ^ (16 : ℝ) = t ^ (16 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 16
    rw [hExpr]
    rw [hp16]
    simpa only [one_div] using hcalc
  refine hbase.trans ?_
  simpa only [t, Q, eta] using (show
    (4 / x ^ 2) * ((5 * Real.pi + 15 * Real.exp 1) * x) *
          (Real.log (6 * x) / t ^ ((1 : ℝ) / 2)) *
          ((2 * Real.log (hN : ℝ) * t ^ (20 : ℝ)) *
            (5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
              8 * x * eta / Q + 5 + 3 * x / Q ^ 2)) ≤
        t ^ (-(16 : ℝ)) from hrearrange.le.trans (hmajor.trans hfinish))

set_option maxHeartbeats 800000 in
/-- The complete all-small initial Ramaré branch has twelve inverse logarithms to spare,
uniformly through every subquartic upper endpoint. -/
theorem eventually_setIntegral_normSq_menonInitialRange_ordinary_le_log_rpow_neg_twelve :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W : ℝ),
      (((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ) < (hN : ℝ)) →
      (hN : ℝ) ≤ x ^ ((1 : ℝ) / 4) → 1 ≤ W →
      1 ≤ menonInitialRangeSteps ((1 : ℝ) / 2) 20 x hN →
      W * ((hN : ℝ) + 1) ≤ 2 * x →
      let P := menonInitialRangePrimes ((1 : ℝ) / 2) 20 x hN
      let Q := ((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ)
      let eta := lowEta 20 x
      let theta := lowTheta 20 x
      let L := menonInitialRangeSteps ((1 : ℝ) / 2) 20 x hN
      let E := allBlocksSmall P Q eta L
        (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
      (∫ w in E,
        ‖harmonicRamareBilinear P (menonFinalRangeShell x) w‖ ^ 2) ≤
        (Real.log x) ^ (-(12 : ℝ)) := by
  have hsmall :=
    eventually_setIntegral_normSq_menonInitialRange_ordinary_le_fullInterval
      (a := (1 : ℝ) / 2) (c := 20) (A := 20) (by norm_num) (by norm_num)
  have hdefect :=
    eventually_integral_Icc_normSq_menonInitialRange_ladderDefect_le_log_rpow_neg_sixteen
  have hQpow := rpow_log_le_highBase (a := (1 : ℝ) / 2) (by norm_num) 100
  have hlarge : ∀ᶠ x : ℝ in atTop, (57600 : ℝ) ≤ (Real.log x) ^ (22 : ℝ) := by
    exact ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).eventually_ge_atTop 57600
  filter_upwards [hsmall, hdefect, hQpow, hlarge,
    Filter.eventually_ge_atTop (Real.exp 3)] with
      x hsmallx hdefectx hQpowx hlarge hxlarge
  intro hN W hQh hhQuarter hW hLone hWh
  dsimp only
  let P := menonInitialRangePrimes ((1 : ℝ) / 2) 20 x hN
  let Q : ℝ := ((highBase ((1 : ℝ) / 2) x : ℕ) : ℝ)
  let eta := lowEta 20 x
  let theta := lowTheta 20 x
  let L := menonInitialRangeSteps ((1 : ℝ) / 2) 20 x hN
  let E := allBlocksSmall P Q eta L
    (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  let t := Real.log x
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 3) hxlarge
  have hx1 : 1 < x := lt_of_lt_of_le (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 3)) hxlarge
  have hxexp : Real.exp 1 ≤ x := by
    exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hxlarge
  have ht3 : 3 ≤ t := by
    dsimp only [t]
    simpa using Real.log_le_log (Real.exp_pos 3) hxlarge
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hhx : (hN : ℝ) ≤ x := by
    have hquarter_le : x ^ ((1 : ℝ) / 4) ≤ x := by
      calc
        x ^ ((1 : ℝ) / 4) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
        _ = x := Real.rpow_one x
    exact hhQuarter.trans hquarter_le
  have hQ100 : t ^ 100 ≤ Q := by
    have hp100 : t ^ (100 : ℝ) = t ^ (100 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 100
    rw [← hp100]
    simpa only [t, Q] using hQpowx
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity : 0 < t ^ 100) hQ100
  have hQ1 : 1 ≤ Q := le_trans (one_le_pow₀ ht1) hQ100
  have hh0 : 0 < (hN : ℝ) := lt_trans hQ0 hQh
  have hlogh : Real.log (hN : ℝ) ≤ t / 4 := by
    have hlog := Real.log_le_log hh0 hhQuarter
    rw [Real.log_rpow hx0] at hlog
    dsimp only [t]
    nlinarith
  have hQnat : highBase ((1 : ℝ) / 2) x ≤ hN := by exact_mod_cast hQh.le
  have hLraw := menonInitialRangeSteps_le
    (a := (1 : ℝ) / 2) (c := 20) hxexp (by norm_num) hQnat
  have hp20 : t ^ (20 : ℝ) = t ^ (20 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 20
  have hstep : 2 * Real.log (hN : ℝ) * t ^ (20 : ℝ) ≤ t ^ 21 := by
    rw [hp20]
    have ht20 : 0 ≤ t ^ 20 := pow_nonneg ht0.le _
    calc
      2 * Real.log (hN : ℝ) * t ^ 20 ≤ 2 * (t / 4) * t ^ 20 := by gcongr
      _ = (1 / 2 : ℝ) * (t * t ^ 20) := by ring
      _ ≤ 1 * (t * t ^ 20) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg ht0.le ht20)
      _ = t * t ^ 20 := by ring
      _ = t ^ 21 := by ring
  have hL : (L : ℝ) ≤ t ^ 21 := by
    have hLraw' : (L : ℝ) ≤ 2 * Real.log (hN : ℝ) * t ^ (20 : ℝ) := by
      simpa only [L, t] using hLraw
    exact hLraw'.trans hstep
  have ht20le100 : t ^ 20 ≤ t ^ 100 := pow_le_pow_right₀ ht1 (by norm_num)
  have hQinv : 1 / Q ≤ 1 / t ^ 20 :=
    (one_div_le_one_div_of_le (by positivity) hQ100).trans
      (one_div_le_one_div_of_le (by positivity) ht20le100)
  have heta : eta = 1 / t ^ 20 := by
    dsimp only [eta, lowEta]
    rw [Real.rpow_neg ht0.le]
    norm_num
  have htheta : theta = 1 / t ^ 20 := by
    dsimp only [theta, lowTheta]
    rw [Real.rpow_neg ht0.le]
    norm_num
  have hetaQ : eta + 1 / Q ≤ 2 / t ^ 20 := by
    rw [heta]
    calc
      1 / t ^ 20 + 1 / Q ≤ 1 / t ^ 20 + 1 / t ^ 20 := add_le_add le_rfl hQinv
      _ = 2 / t ^ 20 := by ring
  have hthetaEta : theta + eta = 2 / t ^ 20 := by
    rw [htheta, heta]
    ring
  have hmain :
      3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 ≤
        (Real.log x) ^ (-(16 : ℝ)) := by
    have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
    have hsum0 : 0 ≤ eta + 1 / Q := by rw [heta]; positivity
    have htarget0 : 0 ≤ 2 / t ^ 20 := by positivity
    have hsquare := pow_le_pow_left₀ hL0 hL 2
    have hsumSq := pow_le_pow_left₀ hsum0 hetaQ 2
    have hraw :
        3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 ≤
          3600 * (t ^ 21) ^ 2 * (2 / t ^ 20) ^ 2 * (2 / t ^ 20) ^ 2 := by
      rw [hthetaEta]
      gcongr
    have hlargeNat : (57600 : ℝ) ≤ t ^ 22 := by
      have hp22 : t ^ (22 : ℝ) = t ^ (22 : ℕ) := by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 22
      rw [← hp22]
      simpa only [t] using hlarge
    have hcalc : (57600 : ℝ) / t ^ 38 ≤ 1 / t ^ 16 := by
      rw [div_le_div_iff₀ (pow_pos ht0 38) (pow_pos ht0 16)]
      have hmul := mul_le_mul_of_nonneg_right hlargeNat (pow_nonneg ht0.le 16)
      calc
        (57600 : ℝ) * t ^ 16 ≤ t ^ 22 * t ^ 16 := hmul
        _ = 1 * t ^ 38 := by ring
    have hrawEq :
        3600 * (t ^ 21) ^ 2 * (2 / t ^ 20) ^ 2 * (2 / t ^ 20) ^ 2 =
          (57600 : ℝ) / t ^ 38 := by field_simp; norm_num
    have hp16 : t ^ (16 : ℝ) = t ^ (16 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 16
    rw [Real.rpow_neg (by simpa only [t] using ht0.le), hp16]
    exact hraw.trans (hrawEq.le.trans (by simpa only [one_div] using hcalc))
  have hbase := hsmallx hN W hQh hhx hW hLone hWh
  have hdef := hdefectx hN W hQh hhQuarter hW hWh
  have hdefE :
      (∫ w in E,
        ‖harmonicLadderProductDefect P ⌈x⌉₊ (menonFinalRangeTopNat x)
          Q eta L w‖ ^ 2) ≤ (Real.log x) ^ (-(16 : ℝ)) := by
    calc
      _ ≤ ∫ w in Set.Icc (-W) W,
          ‖harmonicLadderProductDefect P ⌈x⌉₊ (menonFinalRangeTopNat x)
            Q eta L w‖ ^ 2 := by
        have hf := (continuous_harmonicLadderProductDefect P ⌈x⌉₊
          (menonFinalRangeTopNat x) Q eta L).norm.pow 2
        exact MeasureTheory.setIntegral_mono_set hf.integrableOn_Icc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall
            (allBlocksSmall_subset P Q eta L
              (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W))
      _ ≤ _ := by simpa only [P, Q, eta, L] using hdef
  have hsum :
      3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 +
          2 * (Real.log x) ^ (-(16 : ℝ)) ≤
        (Real.log x) ^ (-(12 : ℝ)) := by
    have hp12 : t ^ (12 : ℝ) = t ^ (12 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 12
    have hp16 : t ^ (16 : ℝ) = t ^ (16 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 16
    have ht4 : (3 : ℝ) ≤ t ^ 4 := by
      refine ht3.trans ?_
      calc
        t = t * 1 := by ring
        _ ≤ t * t ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ ht1) ht0.le
        _ = t ^ 4 := by ring
    have hratio : 3 / t ^ 16 ≤ 1 / t ^ 12 := by
      rw [div_le_div_iff₀ (pow_pos ht0 16) (pow_pos ht0 12)]
      have hmul := mul_le_mul_of_nonneg_right ht4 (pow_nonneg ht0.le 12)
      calc
        (3 : ℝ) * t ^ 12 ≤ t ^ 4 * t ^ 12 := hmul
        _ = 1 * t ^ 16 := by ring
    calc
      3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 +
          2 * (Real.log x) ^ (-(16 : ℝ)) ≤
        3 * (Real.log x) ^ (-(16 : ℝ)) := by linarith
      _ = 3 / t ^ 16 := by
        rw [Real.rpow_neg (by simpa only [t] using ht0.le), hp16]
        simp only [t]
        ring
      _ ≤ 1 / t ^ 12 := hratio
      _ = (Real.log x) ^ (-(12 : ℝ)) := by
        rw [Real.rpow_neg (Real.log_nonneg hx1.le), hp12]
        simp only [t, one_div]
  refine hbase.trans ?_
  simpa only [P, Q, eta, theta, L, E] using
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdefE (by norm_num))).trans hsum

end

end RHTower.Sieve
