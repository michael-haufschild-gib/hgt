import GaloisForLFunctions.RHTower.Sieve.TwoRangeMajorant
import GaloisForLFunctions.RHTower.Sieve.TwoRangeScheduleFacts

/-!
# The Route-T parameters of the high range

`Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` takes fourteen side conditions.  At the
two-range schedule all of them are elementary consequences of two facts about the high ladder: its
blocks sit between `exp((log x)^a)` and `2·exp((log x)^b)`, and its base is a natural number, so the
floor of any block top is at least the base itself.

This file fixes the remaining Route-T parameters — the contour's frequency `q`, its lower cutoff
`xmin`, the width `μ` and the height cost `Hmaj` — and discharges the block-top comparisons.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The frequency at which the Route-T contour is evaluated. -/
def twoRangeQ (a x : ℝ) : ℝ := (Real.log x) ^ a

/-- The lower cutoff of the Route-T contour. -/
def twoRangeXmin (a x : ℝ) : ℝ := cardLength a x

/-- The width of the Route-T contour at the schedule. -/
def twoRangeMu (A delta β x : ℝ) : ℝ :=
  min delta (routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)) / 2

/-- The height cost of the Route-T contour at the schedule. -/
def twoRangeHmaj (A b A₃ β x : ℝ) : ℝ :=
  1 / (2 * Real.pi * twoRangeDisc b A₃ x)
    + Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)

theorem twoRangeXmin_pos (a x : ℝ) : 0 < twoRangeXmin a x := cardLength_pos a x

theorem twoRangeQ_nonneg {a x : ℝ} (hx : 1 < x) : 0 ≤ twoRangeQ a x :=
  Real.rpow_nonneg (Real.log_pos hx).le a

theorem twoRangeMu_nonneg {A delta β : ℝ} (hdelta : 0 ≤ delta) (x : ℝ) :
    0 ≤ twoRangeMu A delta β x := by
  rw [twoRangeMu]
  have := (routeTWidthPolylogLower_pos A (2 * Real.pi * twoRangeTop β x)).le
  have hmin : (0 : ℝ) ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)) :=
    le_min hdelta this
  linarith

theorem twoRangeMu_le {A delta β : ℝ} (x : ℝ) :
    twoRangeMu A delta β x
      ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)) / 2 :=
  le_refl _

/-- **The high ladder's block tops are between the base and twice the top.** -/
theorem highBlockTop_bounds {a b c' : ℝ} (hab : a ≤ b) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (highSteps a b c' x),
      ((highBase a x : ℕ) : ℝ)
          ≤ max ((⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1
        ∧ max ((⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1
          ≤ 2 * cardLength b x := by
  filter_upwards [highLadder_le (a := a) (b := b) (c' := c') hab hc',
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x htop hx1 hlog1
  intro j hj
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hb1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have hc := (highBase_bounds (a := a) hx1).1
    have hcl : (1 : ℝ) ≤ cardLength a x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx1).le a)
    linarith
  have hb0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hmono : (1 + highEta c' x) ^ (j + 1) ≤ (1 + highEta c' x) ^ (highSteps a b c' x) :=
    pow_le_pow_right₀ (by linarith) (Finset.mem_range.1 hj)
  have hprod : ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1) ≤ 2 * cardLength b x :=
    le_trans (mul_le_mul_of_nonneg_left hmono hb0.le) htop
  have hge : ((highBase a x : ℕ) : ℝ) ≤ ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1) := by
    have h1 : (1 : ℝ) ≤ (1 + highEta c' x) ^ (j + 1) := one_le_pow₀ (by linarith)
    nlinarith [hb0, h1]
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    have : (highBase a x : ℕ) ≤ ⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1)⌋₊ :=
      Nat.le_floor (by exact_mod_cast hge)
    exact_mod_cast this
  · have hcl : (1 : ℝ) ≤ cardLength b x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx1).le b)
    refine max_le ?_ (by linarith)
    refine le_trans (Nat.floor_le (by positivity)) hprod

/-- **The block tops in logarithmic form.**  These are the hypotheses `hLxj`, `hqj` and `hxminj`. -/
theorem highBlockTop_log_bounds {a b c' : ℝ} (hab : a ≤ b) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (highSteps a b c' x),
      Real.log (max ((⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)
          ≤ twoRangeLx b x
        ∧ twoRangeQ a x
          ≤ Real.log (max ((⌊((highBase a x : ℕ) : ℝ)
              * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)
        ∧ twoRangeXmin a x
          ≤ max ((⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := by
  filter_upwards [highBlockTop_bounds (a := a) (b := b) (c' := c') hab hc',
    Filter.eventually_gt_atTop (1 : ℝ)] with x hbd hx1
  intro j hj
  obtain ⟨hlo, hhi⟩ := hbd j hj
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hbase : cardLength a x ≤ ((highBase a x : ℕ) : ℝ) := (highBase_bounds (a := a) hx1).1
  have hca : (0 : ℝ) < cardLength a x := cardLength_pos a x
  have hmax0 : (0 : ℝ) < max ((⌊((highBase a x : ℕ) : ℝ)
      * (1 + highEta c' x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨?_, ?_, le_trans hbase hlo⟩
  · have hstep := Real.log_le_log hmax0 hhi
    have hid : Real.log (2 * cardLength b x) = Real.log 2 + (Real.log x) ^ b := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos b x)), log_cardLength]
    rw [hid] at hstep
    exact hstep
  · have hstep := Real.log_le_log hca (le_trans hbase hlo)
    rw [log_cardLength] at hstep
    exact hstep

/-- The contour width is at least one. -/
theorem one_le_twoRangeWidth {b A₃ : ℝ} (_hb : 0 < b) (_hA₃ : 0 < A₃) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ twoRangeWidth b A₃ x := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hlog1
  rw [twoRangeWidth]
  exact Real.one_le_rpow hlog1 (by linarith)

/-- The disc radius clears the Route-T threshold. -/
theorem twoRangeDisc_ge {b A₃ : ℝ} (hb : 0 < b) (hA₃ : 0 < A₃) (τ₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      max τ₀ (16 * Real.pi / 3) ≤ 2 * Real.pi * twoRangeDisc b A₃ x := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ (4 * b + 3 * A₃ + 3)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually_ge_atTop (max τ₀ (16 * Real.pi / 3)),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hbig hx1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [twoRangeDisc]
  have hid : 2 * Real.pi * ((Real.log x) ^ (4 * b + 3 * A₃ + 3) / (2 * Real.pi))
      = (Real.log x) ^ (4 * b + 3 * A₃ + 3) := by
    field_simp
  rw [hid]
  exact hbig

/-- The disc sits inside the window. -/
theorem twoRangeDisc_le_top {b A₃ β : ℝ} (_hb : 0 < b) (_hA₃ : 0 < A₃) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, twoRangeDisc b A₃ x ≤ twoRangeTop β x := by
  have hlim := tendsto_rpow_log_mul_cardLength_div_sqrt (β := β) hβ0 hβ1
    (4 * b + 3 * A₃ + 3)
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim,
    Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ),
    hll.eventually_ge_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hsm hx1 hx16 hlog1 hh1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hsqrt : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
    rw [twoRangeLength]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  have hcut : Real.sqrt x / cardLength β x ≤ twoRangeCut β x := by
    rw [twoRangeCut, div_le_div_iff_of_pos_right hh0]
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hkey : (Real.log x) ^ (4 * b + 3 * A₃ + 3) * 4 ≤ Real.sqrt x / cardLength β x := by
    have hratio : (0 : ℝ) < Real.sqrt x / cardLength β x := by positivity
    have hid : (Real.log x) ^ (4 * b + 3 * A₃ + 3) * (cardLength β x / Real.sqrt x)
        * (Real.sqrt x / cardLength β x) = (Real.log x) ^ (4 * b + 3 * A₃ + 3) := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hsm hratio.le
    rw [hid] at hmul
    linarith [hmul]
  have hdisc : twoRangeDisc b A₃ x ≤ (Real.log x) ^ (4 * b + 3 * A₃ + 3) := by
    rw [twoRangeDisc, div_le_iff₀ (by positivity)]
    have hp0 : (0 : ℝ) ≤ (Real.log x) ^ (4 * b + 3 * A₃ + 3) :=
      Real.rpow_nonneg (Real.log_pos hx1).le _
    nlinarith [hp0, Real.pi_gt_three]
  rw [twoRangeTop]
  have hcut0 : (0 : ℝ) ≤ twoRangeCut β x := le_trans (by positivity) hcut
  nlinarith [hdisc, hkey, hcut, hlog1, hcut0]

end

end RHTower.Sieve
