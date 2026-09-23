import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFinalRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale

/-!
# Truncated final-prime schedule for Menon's harmonic decomposition

The hard cofactor endpoints cannot be replaced at the full ambient prime scale with the logarithmic
rate required by the growing-marker argument.  We therefore stop the designated-prime ladder at
`X / (log X)^(20 : ℕ)`.  This leaves only a polylogarithmic cofactor beside any omitted larger prime and
puts the global ladder defect below a fixed negative power of `log X`.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Real upper endpoint of the truncated final designated-prime range. -/
def menonTruncatedPrimeTop (x : ℝ) : ℝ := x / (Real.log x) ^ (20 : ℕ)

/-- Natural upper endpoint of the truncated final designated-prime range. -/
def menonTruncatedPrimeTopNat (x : ℝ) : ℕ := ⌊menonTruncatedPrimeTop x⌋₊

/-- Truncated final designated primes. -/
def menonTruncatedRangePrimes (x : ℝ) : Finset ℕ :=
  primesRange (menonFinalRangePrimeCutoffNat x) (menonTruncatedPrimeTopNat x)

/-- First geometric depth reaching the truncated natural prime top. -/
def menonTruncatedRangeLadderSteps (x : ℝ) : ℕ :=
  ⌈menonFinalRangeLadderH x *
      Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x)⌉₊

/-- Menon's lower cutoff is eventually at most `X^(1/80)`. -/
theorem eventually_menonFinalRangePrimeCutoff_le_rpow_one_eighty :
    ∀ᶠ x : ℝ in atTop, menonFinalRangePrimeCutoff x ≤ x ^ ((1 : ℝ) / 80) := by
  filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog0 : 0 < Real.log x := lt_trans (by positivity) hlogLower
  have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog0).2 hlogLower
  have hllog0 : 0 < Real.log (Real.log x) := lt_trans (by positivity) hllogLower
  have hlll_le : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
    have := Real.log_le_sub_one_of_pos hllog0
    linarith
  have hratio : Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ≤ 1 :=
    (div_le_one hllog0).2 hlll_le
  rw [menonFinalRangePrimeCutoff, Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.2 (by
    have hscale : 0 ≤ Real.log x / 80 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hratio hscale])

/-- A square-root-log exponential lies below Menon's lower prime cutoff. -/
theorem eventually_exp_sqrtLog_div_eighty_le_menonFinalRangePrimeCutoff :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (Real.sqrt (Real.log x) / 80) ≤ menonFinalRangePrimeCutoff x := by
  have hsmall0 := tendsto_logLog_div_logRpow (δ := (1 : ℝ) / 2) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ≤ (Real.log x) ^ ((1 : ℝ) / 2) := by
    filter_upwards [hsmall0.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (Real.exp 1)] with x hs hx
    have hlog : 0 < Real.log x := Real.log_pos (lt_trans (by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx)
    have hpow : 0 < (Real.log x) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hlog _
    rw [div_le_iff₀ hpow] at hs
    simpa using hs
  filter_upwards [hsmall,
    eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hllSmall hx
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog0 : 0 < Real.log x := lt_trans (by positivity) hlogLower
  have hllogLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog0).2 hlogLower
  have hllog0 : 0 < Real.log (Real.log x) := lt_trans (by positivity) hllogLower
  have hlll : 1 ≤ Real.log (Real.log (Real.log x)) := by
    have := (Real.lt_log_iff_exp_lt hllog0).2 hllogLower
    linarith
  have hsqrt : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog0
  have hsqrtEq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hlog0.le
  have hquot : Real.sqrt (Real.log x) ≤
      Real.log x / Real.log (Real.log x) := by
    rw [le_div_iff₀ hllog0]
    rw [← Real.sqrt_eq_rpow] at hllSmall
    nlinarith [mul_le_mul_of_nonneg_left hllSmall hsqrt.le, hsqrtEq]
  have hmain : Real.sqrt (Real.log x) / 80 ≤
      (Real.log x / 80) *
        (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
    have hq0 : 0 ≤ Real.log x / Real.log (Real.log x) := by positivity
    have hlllMul : Real.log x / Real.log (Real.log x) ≤
        Real.log x *
          (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
      field_simp
      nlinarith
    nlinarith [hquot, hlllMul]
  rw [menonFinalRangePrimeCutoff]
  exact Real.exp_le_exp.2 hmain

/-- Natural lower cutoff retains half of the square-root-log exponential. -/
theorem eventually_half_exp_sqrtLog_div_eighty_le_menonFinalRangeLadderBase :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (Real.sqrt (Real.log x) / 80) / 2 ≤ menonFinalRangeLadderBase x := by
  filter_upwards [eventually_exp_sqrtLog_div_eighty_le_menonFinalRangePrimeCutoff,
    tendsto_menonFinalRangePrimeCutoff_atTop.eventually_ge_atTop (2 : ℝ)] with x hlow htwo
  have hfloor := Nat.lt_floor_add_one (menonFinalRangePrimeCutoff x)
  have hbaseFloor : menonFinalRangePrimeCutoff x - 1 <
      menonFinalRangeLadderBase x := by
    rw [menonFinalRangeLadderBase, menonFinalRangePrimeCutoffNat]
    exact (by linarith : menonFinalRangePrimeCutoff x - 1 <
      (⌊menonFinalRangePrimeCutoff x⌋₊ : ℝ))
  have hhalf : menonFinalRangePrimeCutoff x / 2 ≤
      menonFinalRangeLadderBase x := by linarith
  linarith

/-- The truncated top lies well above the lower designated-prime cutoff. -/
theorem eventually_menonFinalRangePrimeCutoffNat_lt_truncatedTopNat :
    ∀ᶠ x : ℝ in atTop,
      menonFinalRangePrimeCutoffNat x < menonTruncatedPrimeTopNat x := by
  filter_upwards [eventually_menonFinalRangePrimeCutoff_le_rpow_one_eighty,
    eventually_const_mul_one_add_log_pow_le_rpow
      (δ := (39 : ℝ) / 80) (c := 2) (by norm_num) (by norm_num) 20,
    eventually_ge_atTop (1 : ℝ), eventually_gt_atTop (Real.exp 1)] with x hcut hlog hx1 hxe
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxgt : 1 < x := by nlinarith [Real.exp_one_gt_d9]
  have hlog0 : 0 < Real.log x := Real.log_pos hxgt
  have hlogPow0 : 0 < (Real.log x) ^ (20 : ℕ) := pow_pos hlog0 _
  have hpow1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 80) :=
    Real.one_le_rpow hx1 (by norm_num)
  have hlogMono : (Real.log x) ^ (20 : ℕ) ≤ (1 + Real.log x) ^ (20 : ℕ) := by
    exact pow_le_pow_left₀ hlog0.le (by linarith) 20
  have hsmall : 2 * (Real.log x) ^ (20 : ℕ) ≤ x ^ ((39 : ℝ) / 80) :=
    (mul_le_mul_of_nonneg_left hlogMono (by norm_num)).trans hlog
  have hpowMul : x ^ ((1 : ℝ) / 80) * x ^ ((39 : ℝ) / 80) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
    norm_num
  have hsqrtSq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have htarget : x ^ ((1 : ℝ) / 80) + 1 < menonTruncatedPrimeTop x := by
    rw [menonTruncatedPrimeTop, lt_div_iff₀ hlogPow0]
    have hleft : (x ^ ((1 : ℝ) / 80) + 1) * (Real.log x) ^ (20 : ℕ)
        ≤ 2 * x ^ ((1 : ℝ) / 80) * (Real.log x) ^ (20 : ℕ) := by
      nlinarith [hpow1, hlogPow0.le]
    have hmid : 2 * x ^ ((1 : ℝ) / 80) * (Real.log x) ^ (20 : ℕ)
        ≤ x ^ ((1 : ℝ) / 80) * x ^ ((39 : ℝ) / 80) := by
      nlinarith [mul_le_mul_of_nonneg_left hsmall
        (Real.rpow_nonneg hx0.le ((1 : ℝ) / 80))]
    rw [hpowMul] at hmid
    have hsqrtLt : Real.sqrt x < x := by
      nlinarith [Real.sqrt_pos.2 hx0, hsqrtSq, show (1 : ℝ) < x by linarith]
    linarith
  have hfloorCut : (menonFinalRangePrimeCutoffNat x : ℝ) ≤
      menonFinalRangePrimeCutoff x := by
    rw [menonFinalRangePrimeCutoffNat]
    exact Nat.floor_le (menonFinalRangePrimeCutoff_pos x).le
  have hnatReal : (menonFinalRangePrimeCutoffNat x + 1 : ℕ) ≤
      menonTruncatedPrimeTopNat x := by
    rw [menonTruncatedPrimeTopNat]
    apply Nat.le_floor
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  omega

private theorem truncated_geometric_ceil_depth_pos
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B) :
    1 ≤ ⌈H * Real.log (B / Q)⌉₊ := by
  rw [Nat.one_le_ceil_iff]
  exact mul_pos hH (Real.log_pos (by rwa [one_lt_div hQ]))

private theorem truncated_geometric_ceil_depth_cover
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B) :
    B ≤ Q * Real.exp ((⌈H * Real.log (B / Q)⌉₊ : ℝ) / H) := by
  have hratio : 0 < B / Q := div_pos (lt_trans hQ hQB) hQ
  have hceil : H * Real.log (B / Q) ≤ (⌈H * Real.log (B / Q)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hlog : Real.log (B / Q) ≤ (⌈H * Real.log (B / Q)⌉₊ : ℝ) / H := by
    rw [le_div_iff₀ hH]
    simpa [mul_comm] using hceil
  have hexp := Real.exp_le_exp.2 hlog
  calc
    B = Q * Real.exp (Real.log (B / Q)) := by
      rw [Real.exp_log hratio]
      field_simp
    _ ≤ Q * Real.exp ((⌈H * Real.log (B / Q)⌉₊ : ℝ) / H) :=
      mul_le_mul_of_nonneg_left hexp hQ.le

private theorem truncated_geometric_before_ceil_depth_lt
    {H Q B : ℝ} (hH : 0 < H) (hQ : 0 < Q) (hQB : Q < B)
    {j : ℕ} (hj : j < ⌈H * Real.log (B / Q)⌉₊) :
    Q * Real.exp ((j : ℝ) / H) < B := by
  have hratio : 0 < B / Q := div_pos (lt_trans hQ hQB) hQ
  have hjreal : (j : ℝ) < H * Real.log (B / Q) := Nat.lt_ceil.mp hj
  have hlog : (j : ℝ) / H < Real.log (B / Q) := by
    rw [div_lt_iff₀ hH]
    simpa [mul_comm] using hjreal
  have hexp := Real.exp_lt_exp.2 hlog
  calc
    Q * Real.exp ((j : ℝ) / H) < Q * Real.exp (Real.log (B / Q)) :=
      mul_lt_mul_of_pos_left hexp hQ
    _ = B := by rw [Real.exp_log hratio]; field_simp

/-- Eventual positivity and nondegeneracy of the truncated ladder. -/
theorem eventually_menonTruncatedRangeLadder_basic :
    ∀ᶠ x : ℝ in atTop,
      1 < x ∧ 1 ≤ Real.log x ∧ 0 < menonFinalRangeLadderH x ∧
      1 < menonFinalRangeLadderBase x ∧
      menonFinalRangeLadderBase x < (menonTruncatedPrimeTopNat x : ℝ) ∧
      0 ≤ menonFinalRangeLadderEta x ∧ 1 ≤ menonTruncatedRangeLadderSteps x := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangePrimeCutoffNat_lt_truncatedTopNat] with x hxe hQtwo htop
  have hx : 1 < x := lt_of_lt_of_le (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hxe
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogOne : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hH : 0 < menonFinalRangeLadderH x := by
    rw [menonFinalRangeLadderH]
    positivity
  have hQ : 1 < menonFinalRangeLadderBase x := by
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hQtwo
  have htopR : menonFinalRangeLadderBase x < (menonTruncatedPrimeTopNat x : ℝ) := by
    rw [menonFinalRangeLadderBase]
    exact_mod_cast htop
  have heta := menonFinalRangeLadderEta_nonneg hH
  have hL : 1 ≤ menonTruncatedRangeLadderSteps x := by
    rw [menonTruncatedRangeLadderSteps]
    exact truncated_geometric_ceil_depth_pos hH (menonFinalRangeLadderBase_pos hQ) htopR
  exact ⟨hx, hlogOne, hH, hQ, htopR, heta, hL⟩

/-- Truncated designated primes are covered by the exact `H`-adic ladder. -/
theorem eventually_menonTruncatedRangePrimes_ladder_range :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ menonTruncatedRangePrimes x,
      menonFinalRangeLadderBase x < (p : ℝ) ∧
      (p : ℝ) ≤ menonFinalRangeLadderBase x *
        (1 + menonFinalRangeLadderEta x) ^ menonTruncatedRangeLadderSteps x := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic] with x hx p hp
  rcases hx with ⟨_, _, hH, hQ, htop, _, _⟩
  have hpRange := mem_primesRange.1 hp
  have hpLower : menonFinalRangeLadderBase x < (p : ℝ) := by
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hpRange.2.1
  have hcover := truncated_geometric_ceil_depth_cover hH
    (menonFinalRangeLadderBase_pos hQ) htop
  rw [← menonFinalRangeLadder_pow_eq_exp] at hcover
  have hpTop : (p : ℝ) ≤ (menonTruncatedPrimeTopNat x : ℝ) := by
    exact_mod_cast hpRange.2.2
  exact ⟨hpLower, hpTop.trans hcover⟩

/-- The truncated natural prime top itself is covered by the exact `H`-adic ladder. -/
theorem eventually_menonTruncatedRangeLadder_cover :
    ∀ᶠ x : ℝ in atTop,
      (menonTruncatedPrimeTopNat x : ℝ) ≤
        menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ menonTruncatedRangeLadderSteps x := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic] with x hx
  rcases hx with ⟨_, _, hH, hQ, htop, _, _⟩
  have hcover := truncated_geometric_ceil_depth_cover hH
    (menonFinalRangeLadderBase_pos hQ) htop
  rwa [← menonFinalRangeLadder_pow_eq_exp] at hcover

/-- The ceiling depth overshoots the truncated prime top by less than one ladder ratio. -/
theorem eventually_menonTruncatedRangeLadder_overshoot :
    ∀ᶠ x : ℝ in atTop,
      menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ menonTruncatedRangeLadderSteps x ≤
        (menonTruncatedPrimeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic] with x hx
  rcases hx with ⟨_, _, hH, hQ, htop, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have htop0 : 0 < (menonTruncatedPrimeTopNat x : ℝ) := lt_trans hbase0 htop
  have hlogPos : 0 < Real.log ((menonTruncatedPrimeTopNat x : ℝ) /
      menonFinalRangeLadderBase x) := Real.log_pos (by rwa [one_lt_div hbase0])
  have harg0 : 0 ≤ menonFinalRangeLadderH x *
      Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) :=
    (mul_pos hH hlogPos).le
  have hceil := Nat.ceil_lt_add_one harg0
  have hceil' : (menonTruncatedRangeLadderSteps x : ℝ) <
      menonFinalRangeLadderH x *
          Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) + 1 := by
    simpa only [menonTruncatedRangeLadderSteps] using hceil
  have hdiv : (menonTruncatedRangeLadderSteps x : ℝ) / menonFinalRangeLadderH x <
      Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) +
        1 / menonFinalRangeLadderH x := by
    rw [div_lt_iff₀ hH]
    calc
      (menonTruncatedRangeLadderSteps x : ℝ) <
          menonFinalRangeLadderH x *
              Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) + 1 :=
        hceil'
      _ = (Real.log ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x) +
          1 / menonFinalRangeLadderH x) * menonFinalRangeLadderH x := by
        field_simp
  have hexp := Real.exp_le_exp.2 hdiv.le
  rw [← menonFinalRangeLadder_pow_eq_exp,
    Real.exp_add, Real.exp_log (div_pos htop0 hbase0),
    ← one_add_menonFinalRangeLadderEta] at hexp
  calc
    menonFinalRangeLadderBase x *
        (1 + menonFinalRangeLadderEta x) ^ menonTruncatedRangeLadderSteps x ≤
      menonFinalRangeLadderBase x *
        ((menonTruncatedPrimeTopNat x : ℝ) / menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x)) :=
      mul_le_mul_of_nonneg_left hexp hbase0.le
    _ = (menonTruncatedPrimeTopNat x : ℝ) * (1 + menonFinalRangeLadderEta x) := by
      field_simp

/-- Every truncated ladder step has nonempty natural cofactor endpoints on the ambient shell. -/
theorem eventually_menonTruncatedRangeLadder_cofactor_endpoints :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (menonTruncatedRangeLadderSteps x),
      1 ≤ ⌈(⌈x⌉₊ : ℝ) /
        ((menonFinalRangeLadderBase x *
            (1 + menonFinalRangeLadderEta x) ^ j) *
          (1 + menonFinalRangeLadderEta x))⌉₊ ∧
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) /
        (menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ j)⌋₊ := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic] with x hx j hj
  rcases hx with ⟨hxone, hlogOne, hH, hQ, htop, _, _⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have hstep0 : 0 < 1 + menonFinalRangeLadderEta x := by
    rw [one_add_menonFinalRangeLadderEta]
    positivity
  have hden0 : 0 < menonFinalRangeLadderBase x *
      (1 + menonFinalRangeLadderEta x) ^ j := mul_pos hbase0 (pow_pos hstep0 _)
  constructor
  · rw [Nat.one_le_ceil_iff]
    exact div_pos (by
      exact_mod_cast (Nat.one_le_ceil_iff.2 (by linarith : 0 < x)))
      (mul_pos hden0 hstep0)
  · apply Nat.le_floor
    have hjlt : j < menonTruncatedRangeLadderSteps x := Finset.mem_range.1 hj
    have hprev := truncated_geometric_before_ceil_depth_lt hH hbase0 htop hjlt
    rw [← menonFinalRangeLadder_pow_eq_exp] at hprev
    have htopAmbient : (menonTruncatedPrimeTopNat x : ℝ) ≤
        (menonFinalRangeTopNat x : ℝ) := by
      rw [menonTruncatedPrimeTopNat, menonFinalRangeTopNat]
      exact_mod_cast Nat.floor_mono (by
        rw [menonTruncatedPrimeTop]
        have hlogPow : 1 ≤ (Real.log x) ^ (20 : ℕ) := one_le_pow₀ hlogOne
        have hdiv : x / (Real.log x) ^ (20 : ℕ) ≤ x :=
          div_le_self (by linarith) hlogPow
        linarith)
    rw [le_div_iff₀ hden0]
    norm_num
    exact hprev.le.trans htopAmbient

end

end RHTower.Sieve
