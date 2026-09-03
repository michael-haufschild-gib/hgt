import GaloisForLFunctions.RHTower.Sieve.MoebiusSquarefreeSmoothRankin
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Menon's final-range lower prime cutoff, with the fixed parameter `R = 80`. -/
def menonFinalRangePrimeCutoff (x : ℝ) : ℝ :=
  Real.exp ((Real.log x / 80) *
    (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)))

/-- Rankin exponent used for the squarefree Möbius-supported exceptional set. -/
def menonFinalRangeRankinExponent (x : ℝ) : ℝ :=
  20 * Real.log (Real.log x) / Real.log x

/-- Integer form of Menon's final-range lower prime cutoff. -/
def menonFinalRangePrimeCutoffNat (x : ℝ) : ℕ :=
  ⌊menonFinalRangePrimeCutoff x⌋₊

/-- Integer top endpoint `floor(3X)` of Menon's final range. -/
def menonFinalRangeTopNat (x : ℝ) : ℕ := ⌊3 * x⌋₊

theorem menonFinalRangePrimeCutoff_pos (x : ℝ) : 0 < menonFinalRangePrimeCutoff x :=
  Real.exp_pos _

theorem log_menonFinalRangePrimeCutoff (x : ℝ) :
    Real.log (menonFinalRangePrimeCutoff x) =
      (Real.log x / 80) *
        (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
  simp [menonFinalRangePrimeCutoff]

theorem tendsto_menonFinalRangeRankinExponent_zero :
    Tendsto menonFinalRangeRankinExponent atTop (𝓝 0) := by
  have h := tendsto_logLog_div_logRpow (δ := (1 : ℝ)) (by norm_num)
  have h20 := h.const_mul (20 : ℝ)
  simpa only [mul_zero] using h20.congr' (Eventually.of_forall fun x => by
    rw [menonFinalRangeRankinExponent]
    rw [Real.rpow_one]
    ring)

theorem eventually_menonFinalRangeRankinExponent_pos_le_one :
    ∀ᶠ x : ℝ in atTop, 0 < menonFinalRangeRankinExponent x ∧
      menonFinalRangeRankinExponent x ≤ 1 := by
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
    tendsto_menonFinalRangeRankinExponent_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
      with x hx hxle
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have honeexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hlog1 : 1 < Real.log x := lt_trans honeexp hlogLower
  have hllog : 0 < Real.log (Real.log x) := Real.log_pos hlog1
  have hlog : 0 < Real.log x := lt_trans zero_lt_one hlog1
  constructor
  · rw [menonFinalRangeRankinExponent]
    positivity
  · exact hxle

private theorem eventually_logLog_le_sqrtLog :
    ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ≤ (Real.log x) ^ ((1 : ℝ) / 2) := by
  have h := tendsto_logLog_div_logRpow (δ := (1 : ℝ) / 2) (by norm_num)
  filter_upwards [h.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (Real.exp 1)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos (lt_trans (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx1)
  have hpow : 0 < (Real.log x) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hlog _
  rw [div_le_iff₀ hpow] at hx
  simpa using hx

private theorem tendsto_sqrtLog_atTop :
    Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 2)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).comp Real.tendsto_log_atTop

theorem tendsto_menonFinalRangePrimeCutoff_atTop :
    Tendsto menonFinalRangePrimeCutoff atTop atTop := by
  have hminor : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ ((1 : ℝ) / 2) / 80 ≤
        (Real.log x / 80) *
          (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
    filter_upwards [eventually_logLog_le_sqrtLog,
      eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hsmall hx
    have hx0 : 0 < x := lt_trans (by positivity) hx
    have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
      (Real.lt_log_iff_exp_lt hx0).2 hx
    have hlog0 : 0 < Real.log x := lt_trans (by positivity) hlogLower
    have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
      (Real.lt_log_iff_exp_lt hlog0).2 hlogLower
    have hllog0 : 0 < Real.log (Real.log x) := lt_trans (by positivity) hllogLower
    have hlllLower : 1 < Real.log (Real.log (Real.log x)) :=
      (Real.lt_log_iff_exp_lt hllog0).2 hllogLower
    have honeexp : 1 < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hexpexp : 1 < Real.exp (Real.exp 1) := lt_trans honeexp
      (Real.exp_lt_exp.mpr honeexp)
    have hlog1 : 1 < Real.log x := lt_trans hexpexp hlogLower
    have hllog1 : 1 < Real.log (Real.log x) := lt_trans honeexp hllogLower
    have hlll : 1 ≤ Real.log (Real.log (Real.log x)) := hlllLower.le
    have hlog : 0 < Real.log x := lt_trans zero_lt_one hlog1
    have hllog : 0 < Real.log (Real.log x) := lt_trans zero_lt_one hllog1
    have hsqrt : 0 < (Real.log x) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hlog _
    have hquot : (Real.log x) ^ ((1 : ℝ) / 2) ≤
        Real.log x / Real.log (Real.log x) := by
      rw [le_div_iff₀ hllog]
      have hsquare : (Real.log x) ^ ((1 : ℝ) / 2) *
          (Real.log x) ^ ((1 : ℝ) / 2) = Real.log x := by
        rw [← Real.rpow_add hlog]
        norm_num
      nlinarith [mul_le_mul_of_nonneg_left hsmall hsqrt.le]
    have hquot' : Real.log x / Real.log (Real.log x) ≤
        Real.log x * (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv : 0 ≤ (Real.log (Real.log x))⁻¹ := inv_nonneg.2 hllog.le
      have hone : (Real.log (Real.log x))⁻¹ ≤
          Real.log (Real.log (Real.log x)) * (Real.log (Real.log x))⁻¹ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hlll hinv
      exact mul_le_mul_of_nonneg_left hone hlog.le
    nlinarith [hquot, hquot']
  have hbase : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 2) / 80) atTop atTop := by
    have hmul := Filter.Tendsto.const_mul_atTop
      (by norm_num : 0 < (1 : ℝ) / 80) tendsto_sqrtLog_atTop
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hmul
  have hexp := Real.tendsto_exp_atTop.comp hbase
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [hexp.eventually_ge_atTop b, hminor] with x hxb hx
  rw [menonFinalRangePrimeCutoff]
  exact hxb.trans (Real.exp_le_exp.2 hx)

theorem tendsto_menonFinalRangePrimeCutoffNat_atTop :
    Tendsto menonFinalRangePrimeCutoffNat atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_menonFinalRangePrimeCutoff_atTop

theorem eventually_two_le_menonFinalRangePrimeCutoffNat :
    ∀ᶠ x : ℝ in atTop, 2 ≤ menonFinalRangePrimeCutoffNat x :=
  tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop 2

theorem eventually_menonFinalRangePrimeCutoff_le_x :
    ∀ᶠ x : ℝ in atTop, menonFinalRangePrimeCutoff x ≤ x := by
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog : 0 < Real.log x := lt_trans (by positivity) hlogLower
  have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog).2 hlogLower
  have honeexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hllog1 : 1 < Real.log (Real.log x) := lt_trans honeexp hllogLower
  have hllog : 0 < Real.log (Real.log x) := lt_trans zero_lt_one hllog1
  have hlll_le : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
    have := Real.log_le_sub_one_of_pos hllog
    linarith
  have hratio : Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ≤ 1 :=
    (div_le_one hllog).2 hlll_le
  rw [menonFinalRangePrimeCutoff]
  have : Real.log x / 80 ≤ Real.log x := by nlinarith
  have hexp : (Real.log x / 80) *
      (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) ≤ Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ Real.log x / 80)]
  calc
    Real.exp ((Real.log x / 80) *
        (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)))
        ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 hexp
    _ = x := Real.exp_log hx0

theorem eventually_menonFinalRange_cutoff_rpow_eq :
    ∀ᶠ x : ℝ in atTop,
      (menonFinalRangePrimeCutoff x) ^ (menonFinalRangeRankinExponent x) =
        (Real.log (Real.log x)) ^ ((1 : ℝ) / 4) := by
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog : 0 < Real.log x := lt_trans (by positivity) hlogLower
  have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog).2 hlogLower
  have hllog : 0 < Real.log (Real.log x) := lt_trans (by positivity) hllogLower
  have hlogne := ne_of_gt hlog
  have hllogne := ne_of_gt hllog
  rw [menonFinalRangePrimeCutoff, menonFinalRangeRankinExponent,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hllog]
  congr 1
  field_simp [hlogne, hllogne]
  ring

theorem eventually_x_rpow_neg_menonFinalRangeRankinExponent_eq :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-menonFinalRangeRankinExponent x) =
        Real.exp (-20 * Real.log (Real.log x)) := by
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1))] with x hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog0 : 0 < Real.log x := lt_trans (by positivity) hlogLower
  rw [Real.rpow_def_of_pos hx0, menonFinalRangeRankinExponent]
  congr 1
  field_simp [ne_of_gt hlog0]

theorem eventually_log_pow_ten_eq_exp_ten_logLog :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ (10 : ℕ) = Real.exp (10 * Real.log (Real.log x)) := by
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  have honeexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hlog0 : 0 < Real.log x := Real.log_pos (honeexp.trans hx)
  calc
    (Real.log x) ^ (10 : ℕ) = (Real.exp (Real.log (Real.log x))) ^ (10 : ℕ) := by
      rw [Real.exp_log hlog0]
    _ = Real.exp (10 * Real.log (Real.log x)) := by
      simpa using (Real.exp_nat_mul (Real.log (Real.log x)) 10).symm

/-- Normalized elementary Rankin majorant for Menon's final range. -/
def menonFinalRangeSmoothNormalizedMajorant (x : ℝ) : ℝ :=
  3 * Real.exp (((-10 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
    Real.exp 1 * mertensUpperConst +
    RHTower.uniformPrimeLogRpowConst *
      (Real.log (Real.log x)) ^ ((1 : ℝ) / 4))

theorem eventually_card_squarefreeSmoothUpTo_menonFinalRange_normalized_le :
    ∀ᶠ x : ℝ in atTop,
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (10 : ℕ) / x ≤
        menonFinalRangeSmoothNormalizedMajorant x := by
  filter_upwards [eventually_menonFinalRangeRankinExponent_pos_le_one,
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangePrimeCutoff_le_x,
    eventually_menonFinalRange_cutoff_rpow_eq,
    eventually_x_rpow_neg_menonFinalRangeRankinExponent_eq,
    eventually_log_pow_ten_eq_exp_ten_logLog,
    eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))]
      with x ha hz2 hPx hPa hxa hlogpow hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hx1 : 1 ≤ x := by
    have honeexp : 1 < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hexpstep : Real.exp 1 < Real.exp (Real.exp 1) :=
      Real.exp_lt_exp.mpr honeexp
    have hexpexp : 1 < Real.exp (Real.exp 1) := honeexp.trans hexpstep
    have hexpexpexp : 1 < Real.exp (Real.exp (Real.exp 1)) :=
      hexpexp.trans (Real.exp_lt_exp.mpr hexpstep)
    exact (hexpexpexp.trans hx).le
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog0 : 0 < Real.log x := lt_trans (by positivity) hlogLower
  have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog0).2 hlogLower
  have hllog0 : 0 < Real.log (Real.log x) := lt_trans (by positivity) hllogLower
  have hYupper : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hYlower : x ≤ ((menonFinalRangeTopNat x : ℕ) : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (3 * x)
    rw [← menonFinalRangeTopNat] at hfloor
    linarith
  have hY1 : 1 ≤ menonFinalRangeTopNat x := by
    exact_mod_cast hx1.trans hYlower
  have hY0 : 0 < ((menonFinalRangeTopNat x : ℕ) : ℝ) := by exact_mod_cast hY1
  have hzfloor : ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) ≤
      menonFinalRangePrimeCutoff x := by
    rw [menonFinalRangePrimeCutoffNat]
    exact Nat.floor_le (menonFinalRangePrimeCutoff_pos x).le
  have hzx : ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) ≤ x := hzfloor.trans hPx
  have hza : ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) ^
      (menonFinalRangeRankinExponent x) ≤
        (Real.log (Real.log x)) ^ ((1 : ℝ) / 4) := by
    exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hzfloor ha.1.le).trans_eq hPa
  have hzRpos : 0 < ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hz2)
  have hlogzpos : 0 < Real.log (menonFinalRangePrimeCutoffNat x) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hz2))
  have hlogzx : Real.log (menonFinalRangePrimeCutoffNat x) ≤ Real.log x :=
    Real.log_le_log hzRpos hzx
  have hloglogzx : logLog (menonFinalRangePrimeCutoffNat x) ≤
      Real.log (Real.log x) := by
    rw [logLog]
    exact Real.log_le_log hlogzpos hlogzx
  have hmertens : mertensS (menonFinalRangePrimeCutoffNat x) ≤
      Real.log (Real.log x) + mertensUpperConst :=
    (mertensS_le_logLog_add hz2).trans (by linarith [hloglogzx])
  have hYneg : ((menonFinalRangeTopNat x : ℕ) : ℝ) ^
      (-menonFinalRangeRankinExponent x) ≤
        x ^ (-menonFinalRangeRankinExponent x) :=
    Real.rpow_le_rpow_of_nonpos hx0 hYlower (by linarith)
  have hYpow : ((menonFinalRangeTopNat x : ℕ) : ℝ) ^
      (1 - menonFinalRangeRankinExponent x) ≤
        3 * x * Real.exp (-20 * Real.log (Real.log x)) := by
    rw [show (1 : ℝ) - menonFinalRangeRankinExponent x =
      1 + (-menonFinalRangeRankinExponent x) by ring,
      Real.rpow_add hY0, Real.rpow_one]
    calc
      ((menonFinalRangeTopNat x : ℕ) : ℝ) *
          ((menonFinalRangeTopNat x : ℕ) : ℝ) ^
            (-menonFinalRangeRankinExponent x)
          ≤ (3 * x) * x ^ (-menonFinalRangeRankinExponent x) :=
        mul_le_mul hYupper hYneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
      _ = 3 * x * Real.exp (-20 * Real.log (Real.log x)) := by rw [hxa]
  have hexponent : Real.exp 1 * mertensS (menonFinalRangePrimeCutoffNat x) +
      RHTower.uniformPrimeLogRpowConst *
        ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) ^
          (menonFinalRangeRankinExponent x) ≤
      Real.exp 1 * (Real.log (Real.log x) + mertensUpperConst) +
        RHTower.uniformPrimeLogRpowConst *
          (Real.log (Real.log x)) ^ ((1 : ℝ) / 4) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmertens (Real.exp_pos 1).le)
      (mul_le_mul_of_nonneg_left hza RHTower.uniformPrimeLogRpowConst_pos.le)
  have hcount := card_squarefreeSmoothUpTo_le_uniform ha.1 ha.2
    (menonFinalRangePrimeCutoffNat x) hY1
  have hcount' : ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) ≤
      3 * x * Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
        Real.exp 1 * mertensUpperConst +
        RHTower.uniformPrimeLogRpowConst *
          (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) := by
    calc
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ)
          ≤ ((menonFinalRangeTopNat x : ℕ) : ℝ) ^
              (1 - menonFinalRangeRankinExponent x) *
            Real.exp (Real.exp 1 * mertensS (menonFinalRangePrimeCutoffNat x) +
              RHTower.uniformPrimeLogRpowConst *
                ((menonFinalRangePrimeCutoffNat x : ℕ) : ℝ) ^
                  (menonFinalRangeRankinExponent x)) := hcount
      _ ≤ (3 * x * Real.exp (-20 * Real.log (Real.log x))) *
            Real.exp (Real.exp 1 * (Real.log (Real.log x) + mertensUpperConst) +
              RHTower.uniformPrimeLogRpowConst *
                (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul hYpow (Real.exp_le_exp.2 hexponent) (Real.exp_pos _).le (by positivity)
      _ = 3 * x * Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
            Real.exp 1 * mertensUpperConst +
            RHTower.uniformPrimeLogRpowConst *
              (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) := by
        calc
          (3 * x * Real.exp (-20 * Real.log (Real.log x))) *
              Real.exp (Real.exp 1 * (Real.log (Real.log x) + mertensUpperConst) +
                RHTower.uniformPrimeLogRpowConst *
                  (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) =
              3 * x * (Real.exp (-20 * Real.log (Real.log x)) *
                Real.exp (Real.exp 1 * (Real.log (Real.log x) + mertensUpperConst) +
                  RHTower.uniformPrimeLogRpowConst *
                    (Real.log (Real.log x)) ^ ((1 : ℝ) / 4))) := by ring
          _ = 3 * x * Real.exp (-20 * Real.log (Real.log x) +
                (Real.exp 1 * (Real.log (Real.log x) + mertensUpperConst) +
                  RHTower.uniformPrimeLogRpowConst *
                    (Real.log (Real.log x)) ^ ((1 : ℝ) / 4))) := by
              rw [← Real.exp_add]
          _ = 3 * x * Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
                Real.exp 1 * mertensUpperConst +
                RHTower.uniformPrimeLogRpowConst *
                  (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) := by
              congr 1
              ring
  have hfactor0 : 0 ≤ (Real.log x) ^ (10 : ℕ) / x := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcount' hfactor0
  calc
    ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (10 : ℕ) / x
        = ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
            (menonFinalRangeTopNat x)).card : ℝ) *
              ((Real.log x) ^ (10 : ℕ) / x) := by ring
    _ ≤ (3 * x * Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
          Real.exp 1 * mertensUpperConst +
          RHTower.uniformPrimeLogRpowConst *
            (Real.log (Real.log x)) ^ ((1 : ℝ) / 4))) *
          ((Real.log x) ^ (10 : ℕ) / x) := hmul
    _ = menonFinalRangeSmoothNormalizedMajorant x := by
      rw [hlogpow, menonFinalRangeSmoothNormalizedMajorant]
      calc
        (3 * x * Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
              Real.exp 1 * mertensUpperConst +
              RHTower.uniformPrimeLogRpowConst *
                (Real.log (Real.log x)) ^ ((1 : ℝ) / 4))) *
            (Real.exp (10 * Real.log (Real.log x)) / x) =
            3 * (Real.exp (((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
                Real.exp 1 * mertensUpperConst +
                RHTower.uniformPrimeLogRpowConst *
                  (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) *
              Real.exp (10 * Real.log (Real.log x))) := by
          field_simp [ne_of_gt hx0]
        _ = 3 * Real.exp ((((-20 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
                Real.exp 1 * mertensUpperConst +
                RHTower.uniformPrimeLogRpowConst *
                  (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) +
              10 * Real.log (Real.log x)) := by rw [← Real.exp_add]
        _ = 3 * Real.exp (((-10 : ℝ) + Real.exp 1) * Real.log (Real.log x) +
              Real.exp 1 * mertensUpperConst +
              RHTower.uniformPrimeLogRpowConst *
                (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)) := by
          congr 1
          ring

private theorem eventually_uniformPrimeLogRpowConst_mul_rpow_oneFourth_le_self :
    ∀ᶠ t : ℝ in atTop,
      RHTower.uniformPrimeLogRpowConst * t ^ ((1 : ℝ) / 4) ≤ t := by
  have hsmall : Tendsto (fun t : ℝ =>
      RHTower.uniformPrimeLogRpowConst * t ^ (-((3 : ℝ) / 4))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (3 : ℝ) / 4)).const_mul
        RHTower.uniformPrimeLogRpowConst
  filter_upwards [hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  calc
    RHTower.uniformPrimeLogRpowConst * t ^ ((1 : ℝ) / 4) =
        (RHTower.uniformPrimeLogRpowConst * t ^ (-((3 : ℝ) / 4))) * t := by
      have hrpow : t ^ (-((3 : ℝ) / 4)) * t = t ^ ((1 : ℝ) / 4) := by
        calc
          t ^ (-((3 : ℝ) / 4)) * t =
              t ^ (-((3 : ℝ) / 4)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = t ^ (-((3 : ℝ) / 4) + 1) := (Real.rpow_add ht0 _ _).symm
          _ = t ^ ((1 : ℝ) / 4) := by congr 1; norm_num
      rw [← hrpow]
      ring
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right ht ht0.le
    _ = t := one_mul t

theorem tendsto_menonFinalRangeSmoothNormalizedMajorant_zero :
    Tendsto menonFinalRangeSmoothNormalizedMajorant atTop (𝓝 0) := by
  have hLL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hpower := hLL.eventually
    eventually_uniformPrimeLogRpowConst_mul_rpow_oneFourth_le_self
  have hconst := hLL.eventually_ge_atTop (Real.exp 1 * mertensUpperConst)
  have hLLpos := hLL.eventually_gt_atTop 0
  have hupper : ∀ᶠ x : ℝ in atTop,
      menonFinalRangeSmoothNormalizedMajorant x ≤
        3 * Real.exp (-5 * Real.log (Real.log x)) := by
    filter_upwards [hpower, hconst, hLLpos] with x hpower hconst hLL0
    rw [menonFinalRangeSmoothNormalizedMajorant]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    nlinarith [Real.exp_one_lt_three]
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ (-(5 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (5 : ℝ))).comp Real.tendsto_log_atTop
  have hdecay : Tendsto (fun x : ℝ => 3 * (Real.log x) ^ (-(5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (3 : ℝ)
  have hexpDecay : Tendsto (fun x : ℝ =>
      3 * Real.exp (-5 * Real.log (Real.log x))) atTop (𝓝 0) := by
    apply hdecay.congr'
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have honeexp : 1 < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hlog0 : 0 < Real.log x := Real.log_pos (honeexp.trans hx)
    rw [Real.rpow_def_of_pos hlog0]
    congr 2
    ring
  exact squeeze_zero'
    (Eventually.of_forall fun x => by
      rw [menonFinalRangeSmoothNormalizedMajorant]
      positivity)
    hupper hexpDecay

/-- Menon's literal final-range cutoff has squarefree smooth density
`o(X / (log X)^10)`, by an unconditional Rankin--Euler argument specialized to Möbius support. -/
theorem tendsto_card_squarefreeSmoothUpTo_menonFinalRange_mul_logPow_div_zero :
    Tendsto (fun x : ℝ =>
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (10 : ℕ) / x)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · exact eventually_card_squarefreeSmoothUpTo_menonFinalRange_normalized_le
  · exact tendsto_menonFinalRangeSmoothNormalizedMajorant_zero

end

end RHTower.Sieve
