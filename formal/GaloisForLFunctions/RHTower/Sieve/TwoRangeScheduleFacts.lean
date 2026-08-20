import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits
import GaloisForLFunctions.RHTower.Sieve.TwoRangeLimits
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeLogLogMass

/-!
# The structural facts of the two-range schedule

The hypotheses of `Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`
that do not involve the analytic layers — that each designated range is covered by its ladder, that
the low range stays below the window length, that the Gallagher cutoff exceeds one — are collected
here.  Everything is elementary; only the two prime ranges and the two ladders enter.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The top of the low ladder. -/
def lowTop (K c β x : ℝ) : ℕ :=
  ⌊((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x)⌋₊

/-- The top of the high ladder. -/
def highTop (a b c' x : ℝ) : ℕ :=
  ⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x)⌋₊

/-- **The designated primes of a ladder lie in the ladder's range.** -/
theorem primesRange_ladder_bounds_self {z₀ z L : ℕ} {Q η : ℝ} (hQ : Q = (z₀ : ℝ)) (hη : 0 ≤ η)
    (hQ0 : 0 ≤ Q) (hz : z = ⌊Q * (1 + η) ^ L⌋₊) :
    ∀ p ∈ primesRange z₀ z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L := by
  intro p hp
  rw [mem_primesRange] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  refine ⟨by rw [hQ]; exact_mod_cast hlo, ?_⟩
  have hle : (p : ℝ) ≤ ((⌊Q * (1 + η) ^ L⌋₊ : ℕ) : ℝ) := by
    rw [← hz]
    exact_mod_cast hhi
  refine hle.trans (Nat.floor_le ?_)
  positivity

/-- The low range is covered by the low ladder. -/
theorem lowRange_bounds {K c β x : ℝ} (hx : 1 < x) :
    ∀ p ∈ primesRange (lowBase K x) (lowTop K c β x),
      ((lowBase K x : ℕ) : ℝ) < (p : ℝ)
        ∧ (p : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x) :=
  primesRange_ladder_bounds_self rfl (lowEta_pos hx).le (Nat.cast_nonneg _) rfl

/-- The high range is covered by the high ladder. -/
theorem highRange_bounds {a b c' x : ℝ} (hx : 1 < x) :
    ∀ p ∈ primesRange (highBase a x) (highTop a b c' x),
      ((highBase a x : ℕ) : ℝ) < (p : ℝ)
        ∧ (p : ℝ) ≤ ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x) :=
  primesRange_ladder_bounds_self rfl (highEta_pos hx).le (Nat.cast_nonneg _) rfl

/-- **The polylogarithmic bottom is far below the window length.** -/
theorem lowBase_lt_cardLength {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, ((lowBase K x : ℕ) : ℝ) < cardLength β x := by
  have hlim := tendsto_rpow_log_div_cardLength (β := β) hβ (c := K)
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2) hlim] with x hxe hx1 hsmall
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hbd := (lowBase_bounds hK hxe).2
  have hkey : (Real.log x) ^ K < cardLength β x / 2 := by
    rw [div_lt_iff₀ hh0] at hsmall
    linarith [hsmall]
  have hone : (1 : ℝ) ≤ cardLength β x / 2 := by
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (1 : ℝ) ≤ (Real.log x) ^ K := by
      refine Real.one_le_rpow ?_ hK
      have := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at this
    linarith
  linarith

/-- **The low ladder does not overshoot the window length.** -/
theorem lowTop_le_cardLength {K c β : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x) ≤ cardLength β x := by
  have hzero := tendsto_lowEta (c := c) hc
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    lowBase_lt_cardLength (K := K) (β := β) hK hβ] with x hxe hx1 hη1 hlt
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hQ1 : (1 : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) := by
    have := one_le_lowBase hK hxe
    exact_mod_cast this
  have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hr1 : (1 : ℝ) < 1 + lowEta c x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos hr1
  have hcase : ((lowBase K x : ℕ) : ℝ) < cardLength β x := hlt
  have hratio1 : (1 : ℝ) ≤ cardLength β x / ((lowBase K x : ℕ) : ℝ) := by
    rw [le_div_iff₀ hQ0, one_mul]
    exact hcase.le
  have hlognn : (0 : ℝ) ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) :=
    Real.log_nonneg hratio1
  have hfl : ((lowSteps K c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x)
      ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) := by
    have hle : ((lowSteps K c β x : ℕ) : ℝ)
        ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) / Real.log (1 + lowEta c x) := by
      rw [lowSteps]
      exact Nat.floor_le (div_nonneg hlognn hlogr.le)
    have := mul_le_mul_of_nonneg_right hle hlogr.le
    rw [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
    exact this
  have hpow : (1 + lowEta c x) ^ (lowSteps K c β x)
      ≤ cardLength β x / ((lowBase K x : ℕ) : ℝ) := by
    have hlogpow : Real.log ((1 + lowEta c x) ^ (lowSteps K c β x))
        = ((lowSteps K c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x) := by
      rw [Real.log_pow]
    have hpos : (0 : ℝ) < (1 + lowEta c x) ^ (lowSteps K c β x) := by positivity
    have hposr : (0 : ℝ) < cardLength β x / ((lowBase K x : ℕ) : ℝ) := by positivity
    have := Real.log_le_log_iff hpos hposr
    rw [← this, hlogpow]
    exact hfl
  calc ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x)
      ≤ ((lowBase K x : ℕ) : ℝ) * (cardLength β x / ((lowBase K x : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hQ0.le
    _ = cardLength β x := by field_simp

/-- **The Gallagher cutoff exceeds one.** -/
theorem one_le_twoRangeCut {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ twoRangeCut β x := by
  filter_upwards [cardLength_le_sqrt hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hhs hx1 hh1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
    rw [twoRangeLength]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  rw [twoRangeCut, le_div_iff₀ hh0, one_mul]
  linarith [hfl, hhs]

/-- **The height at which the head bound is taken grows.** -/
theorem one_le_twoRangeTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ twoRangeTop β x := by
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [one_le_twoRangeCut hβ0 hβ1, hll.eventually_ge_atTop (1 : ℝ)] with x hcut hlog
  rw [twoRangeTop]
  nlinarith [hcut, hlog]

/-- **The low ladder has at least one step.** -/
theorem one_le_lowSteps {K c β : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ lowSteps K c β x := by
  have hzero := tendsto_lowEta (c := c) hc
  have hll := tendsto_logRpow_mul_logLogPow (e := -β) (by linarith) 1
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    hpow.eventually_ge_atTop (4 : ℝ),
    Tendsto.eventually_lt_const (show (0 : ℝ) < 1 / (2 * (K + 1)) by positivity) hll]
    with x hxe hx1 hη1 hlogbig hpowbig hsmall
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hpowβ : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlogx1
  have hinv : (Real.log x) ^ (-β) * (Real.log x) ^ β = 1 := by
    rw [← Real.rpow_add hlogx]
    simp
  have hsm : Real.log (Real.log x) < (Real.log x) ^ β / (2 * (K + 1)) := by
    have hmul := mul_lt_mul_of_pos_right hsmall hpowβ
    rw [pow_one] at hmul
    have hid : (Real.log x) ^ (-β) * Real.log (Real.log x) * (Real.log x) ^ β
        = ((Real.log x) ^ (-β) * (Real.log x) ^ β) * Real.log (Real.log x) := by ring
    rw [hid, hinv, one_mul] at hmul
    rw [div_eq_inv_mul, ← div_eq_inv_mul]
    calc Real.log (Real.log x) < 1 / (2 * (K + 1)) * (Real.log x) ^ β := hmul
      _ = (Real.log x) ^ β / (2 * (K + 1)) := by ring
  have hKsm : K * Real.log (Real.log x) ≤ (Real.log x) ^ β / 2 := by
    have hK1 : (0 : ℝ) < 2 * (K + 1) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hsm.le hK
    refine hstep.trans ?_
    have hfrac : K / (2 * (K + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ hK1]
      linarith
    have hid : K * ((Real.log x) ^ β / (2 * (K + 1)))
        = (K / (2 * (K + 1))) * (Real.log x) ^ β := by ring
    rw [hid]
    have := mul_le_mul_of_nonneg_right hfrac hpowβ.le
    linarith
  have hQ1 : (1 : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) := by
    have := one_le_lowBase hK hxe
    exact_mod_cast this
  have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
  have hpowK : (1 : ℝ) ≤ (Real.log x) ^ K := Real.one_le_rpow hlogx1 hK
  have hQ2 : ((lowBase K x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ K := by
    have := (lowBase_bounds hK hxe).2
    linarith
  have hlogQ : Real.log ((lowBase K x : ℕ) : ℝ) ≤ Real.log 2 + K * Real.log (Real.log x) := by
    have hstep : Real.log ((lowBase K x : ℕ) : ℝ) ≤ Real.log (2 * (Real.log x) ^ K) :=
      Real.log_le_log hQ0 hQ2
    refine hstep.trans (le_of_eq ?_)
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlogx K)),
      Real.log_rpow hlogx]
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hratio : Real.log (1 + lowEta c x)
      ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) := by
    have hLHS : Real.log (1 + lowEta c x) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + lowEta c x)
      linarith
    have hRHS : Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ))
        = (Real.log x) ^ β - Real.log ((lowBase K x : ℕ) : ℝ) := by
      rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    rw [hRHS]
    linarith [hlogQ, hKsm, hpowbig, hlog2]
  have hr1 : (1 : ℝ) < 1 + lowEta c x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos hr1
  rw [lowSteps]
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ hlogr, one_mul]
  exact hratio

/-- The bottom of the high range is the window length at exponent `a`, up to rounding. -/
theorem highBase_bounds {a x : ℝ} (hx : 1 < x) :
    cardLength a x ≤ ((highBase a x : ℕ) : ℝ)
      ∧ ((highBase a x : ℕ) : ℝ) ≤ 2 * cardLength a x := by
  have hc0 : (0 : ℝ) < cardLength a x := cardLength_pos a x
  have hc1 : (1 : ℝ) ≤ cardLength a x := by
    rw [cardLength]
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx).le a)
  rw [highBase, cardLength]
  refine ⟨Nat.le_ceil _, ?_⟩
  have := Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos ((Real.log x) ^ a)))
  rw [cardLength] at hc1
  linarith

/-- **The high ladder has at least one step.** -/
theorem one_le_highSteps {a b c' : ℝ} (ha : 0 < a) (hab : a < b) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, 1 ≤ highSteps a b c' x := by
  have hzero := tendsto_highEta (c' := c') hc'
  have hb : Tendsto (fun x : ℝ => (Real.log x) ^ b) atTop atTop :=
    (tendsto_rpow_atTop (lt_trans ha hab)).comp Real.tendsto_log_atTop
  have hquot : Tendsto (fun x : ℝ => (Real.log x) ^ (a - b)) atTop (𝓝 0) := by
    refine (tendsto_log_rpow_neg (δ := b - a) (by linarith)).congr fun x => ?_
    congr 1
    ring
  have hgap : Tendsto (fun x : ℝ => (Real.log x) ^ b - (Real.log x) ^ a) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (Filter.Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2) hb)
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hquot] with x hx1 hsm
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hbp : (0 : ℝ) < (Real.log x) ^ b := Real.rpow_pos_of_pos hlogx b
    have hid : (Real.log x) ^ a = (Real.log x) ^ (a - b) * (Real.log x) ^ b := by
      rw [← Real.rpow_add hlogx]
      congr 1
      ring
    rw [hid]
    nlinarith [hsm, hbp]
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    hgap.eventually_ge_atTop (1 : ℝ)] with x hx1 hη1 hbig
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hr1 : (1 : ℝ) < 1 + highEta c' x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + highEta c' x) := Real.log_pos hr1
  have hLHS : Real.log (1 + highEta c' x) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + highEta c' x)
    linarith
  rw [highSteps]
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ hlogr, one_mul]
  linarith

/-- **The high ladder does not overshoot `exp((log x)^b)`.** -/
theorem highLadder_le {a b c' : ℝ} (hab : a ≤ b) (_hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop,
      ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x)
        ≤ 2 * cardLength b x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hlog1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hr1 : (1 : ℝ) < 1 + highEta c' x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + highEta c' x) := Real.log_pos hr1
  have hmono : (Real.log x) ^ a ≤ (Real.log x) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hab
  have hgap0 : (0 : ℝ) ≤ (Real.log x) ^ b - (Real.log x) ^ a := by linarith
  have hfl : ((highSteps a b c' x : ℕ) : ℝ) * Real.log (1 + highEta c' x)
      ≤ (Real.log x) ^ b - (Real.log x) ^ a := by
    have hle : ((highSteps a b c' x : ℕ) : ℝ)
        ≤ ((Real.log x) ^ b - (Real.log x) ^ a) / Real.log (1 + highEta c' x) := by
      rw [highSteps]
      exact Nat.floor_le (div_nonneg hgap0 hlogr.le)
    have := mul_le_mul_of_nonneg_right hle hlogr.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
  have hpow : (1 + highEta c' x) ^ (highSteps a b c' x)
      ≤ Real.exp ((Real.log x) ^ b - (Real.log x) ^ a) := by
    have hid : (1 + highEta c' x) ^ (highSteps a b c' x)
        = Real.exp (((highSteps a b c' x : ℕ) : ℝ) * Real.log (1 + highEta c' x)) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [hid]
    exact Real.exp_le_exp.2 hfl
  have hbase := (highBase_bounds (a := a) hx1).2
  have hpow0 : (0 : ℝ) ≤ (1 + highEta c' x) ^ (highSteps a b c' x) :=
    pow_nonneg (by linarith) _
  have hc0 : (0 : ℝ) ≤ 2 * cardLength a x := by
    have := cardLength_pos a x
    linarith
  calc ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x)
      ≤ (2 * cardLength a x) * Real.exp ((Real.log x) ^ b - (Real.log x) ^ a) :=
        mul_le_mul hbase hpow hpow0 hc0
    _ = 2 * cardLength b x := by
        rw [cardLength, cardLength, mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The high cofactor blocks are non-empty.**  This is the hypothesis `hNj` of the two-range
bound: every cofactor length `⌊M/R'_j⌋` is at least one, because the whole high ladder sits below
the length of the Dirichlet polynomial. -/
theorem one_le_floor_div_highLadder {a b c' β : ℝ} (hab : a ≤ b) (hc' : 0 < c') (hb1 : b < 1)
    (hb0 : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (highSteps a b c' x),
      1 ≤ ⌊((twoRangeLength β x : ℕ) : ℝ)
        / (((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ j)⌋₊ := by
  have hsmall : Tendsto (fun x : ℝ => cardLength b x / Real.sqrt x) atTop (𝓝 0) := by
    refine (tendsto_rpow_log_mul_cardLength_div_sqrt (β := b) hb0 hb1 0).congr fun x => ?_
    rw [Real.rpow_zero, one_mul]
  filter_upwards [highLadder_le (a := a) (b := b) (c' := c') hab hc',
    Filter.eventually_gt_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (16 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8) hsmall] with x htop hx1 hx16 hsm
  intro j hj
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqrt : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hb0' : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have := (highBase_bounds (a := a) hx1).1
    have := cardLength_pos a x
    linarith
  have hmono : (1 + highEta c' x) ^ j ≤ (1 + highEta c' x) ^ (highSteps a b c' x) :=
    pow_le_pow_right₀ (by linarith) (le_of_lt (Finset.mem_range.1 hj))
  have hprod : ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ j ≤ 2 * cardLength b x := by
    refine le_trans (mul_le_mul_of_nonneg_left hmono hb0'.le) htop
  have hcard : cardLength b x ≤ Real.sqrt x / 8 := by
    rw [div_le_iff₀ (by positivity)] at hsm
    have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
    nlinarith [hsm, hs0]
  have hM : (2 : ℝ) * cardLength b x ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
    have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
      rw [twoRangeLength]
      have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
      linarith
    have hβ0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    linarith [hcard, hsqrt, hfl, hβ0]
  have hpos : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ j := by positivity
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ hpos, one_mul]
  linarith [hprod, hM]

/-- **The harmonic mass of the low range is at most `β·log log x`.**  This is the aggregate `H` of
`Sieve/LadderAggregates.smallLadderGroup_le`, and the reason the ladder groups cost only a power of
`log log` rather than a power of `log`. -/
theorem lowRange_harmonic_le {K c β : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ primesRange (lowBase K x) (lowTop K c β x), 1 / (p : ℝ)
        ≤ β * Real.log (Real.log x) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hpowK : Tendsto (fun x : ℝ => (Real.log x) ^ K) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have herr : Tendsto (fun x : ℝ =>
      2 * ((2 * mertensFirstConst + 1 / 2) / (K * Real.log (Real.log x)))) atTop (𝓝 0) := by
    have hll : Tendsto (fun x : ℝ => K * Real.log (Real.log x)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by linarith) ?_
      exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have := (Tendsto.div_atTop (tendsto_const_nhds
      (x := 2 * mertensFirstConst + 1 / 2)) hll).const_mul (2 : ℝ)
    simpa using this
  have hllto : Tendsto (fun x : ℝ => Real.log (K * Real.log (Real.log x))) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    refine Filter.Tendsto.const_mul_atTop (by linarith) ?_
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    lowTop_le_cardLength (K := K) (c := c) (β := β) hK0 hc hβ,
    hpowK.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr,
    hllto.eventually_ge_atTop (1 : ℝ)] with x hxe hx1 htop hpow2 hlogbig hsmall hllbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hQ2 : (2 : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) := by
    have := (lowBase_bounds hK0 hxe).1
    linarith
  have h₀ : 2 ≤ lowBase K x := by exact_mod_cast hQ2
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hpowge : (1 : ℝ) ≤ (1 + lowEta c x) ^ (lowSteps K c β x) :=
    one_le_pow₀ (by linarith)
  have hz : lowBase K x ≤ lowTop K c β x := by
    rw [lowTop]
    refine Nat.le_floor ?_
    have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
    nlinarith [hpowge, hQ0]
  have hmass := sum_inv_primesRange_le_logLog_diff (z₀ := lowBase K x)
    (z := lowTop K c β x) h₀ hz
  -- the top
  have hTop0 : (0 : ℝ) < ((lowTop K c β x : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((lowTop K c β x : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ lowTop K c β x := le_trans h₀ hz
      exact_mod_cast this
    linarith
  have hTople : ((lowTop K c β x : ℕ) : ℝ) ≤ cardLength β x := by
    rw [lowTop]
    refine le_trans (Nat.floor_le ?_) htop
    have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
    positivity
  have hlogTop : Real.log ((lowTop K c β x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
    have := Real.log_le_log hTop0 hTople
    rwa [log_cardLength] at this
  have hlogTop0 : (0 : ℝ) < Real.log ((lowTop K c β x : ℕ) : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℕ) ≤ lowTop K c β x := le_trans h₀ hz
    have : (2 : ℝ) ≤ ((lowTop K c β x : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hllTop : Real.log (Real.log ((lowTop K c β x : ℕ) : ℝ)) ≤ β * Real.log (Real.log x) := by
    have hstep := Real.log_le_log hlogTop0 hlogTop
    rwa [Real.log_rpow hlogx] at hstep
  -- the bottom
  have hlogBase : K * Real.log (Real.log x) ≤ Real.log ((lowBase K x : ℕ) : ℝ) := by
    have hb := (lowBase_bounds hK0 hxe).1
    have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
    have hp0 : (0 : ℝ) < (Real.log x) ^ K := Real.rpow_pos_of_pos hlogx K
    have := Real.log_le_log hp0 hb
    rwa [Real.log_rpow hlogx] at this
  have hlogBase0 : (0 : ℝ) < K * Real.log (Real.log x) := by
    have hll1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have := Real.log_le_log (Real.exp_pos 1) hlogbig
      rw [Real.log_exp] at this
      linarith
    nlinarith [hK]
  have hllBase : Real.log (K * Real.log (Real.log x))
      ≤ Real.log (Real.log ((lowBase K x : ℕ) : ℝ)) :=
    Real.log_le_log hlogBase0 hlogBase
  have herrle : 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log ((lowBase K x : ℕ) : ℝ))
      ≤ 2 * ((2 * mertensFirstConst + 1 / 2) / (K * Real.log (Real.log x))) := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have := div_le_div_of_nonneg_left hc0 hlogBase0 hlogBase
    linarith
  linarith [hmass, hllTop, hllBase, herrle, hsmall, hllbig]

end

end RHTower.Sieve
