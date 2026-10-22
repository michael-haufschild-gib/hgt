import GaloisForLFunctions.RHTower.BVPrimeWindowReciprocalReflection
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowQuadrature
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# Literal rational-interval bounded-variation prime windows

The closed interval indicator `1_[1,b]` is a concrete compact BV prime window.  Its Mellin
transform is exactly the sharp-window factor of logarithmic width `log b`.  The fixed dyadic
window detects every right shifted Xi zero, while dyadic and triadic windows jointly detect every
complex Mellin coordinate.  Adding their reciprocal-conjugates gives a finite, hence countable,
reflection-stable family with rational endpoints.
-/

open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- Two compact BV windows are equal once their endpoint data and functions agree. -/
@[ext]
theorem ext {W V : CompactBVPrimeWindow}
    (hlower : W.lower = V.lower) (hupper : W.upper = V.upper)
    (hfun : W.toFun = V.toFun) : W = V := by
  cases W
  cases V
  simp_all

/-- Literal closed interval window `1_[a,b]`, for `0 < a < b`. -/
def sharpInterval (a b : ℝ) (ha : 0 < a) (hab : a < b) : CompactBVPrimeWindow where
  lower := a
  upper := b
  lower_pos := ha
  lower_lt_upper := hab
  toFun := Set.Icc a b |>.indicator fun _ => 1
  eq_zero_off_support := by
    intro x hx
    exact Set.indicator_of_notMem hx _
  integrable := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (ne_of_lt measure_Icc_lt_top)
  boundedVariation := by
    apply boundedVariationOn_univ_of_eq_zero_off_Icc hab.le
    · have hzero : eVariationOn
          (Set.Icc a b |>.indicator fun _ : ℝ => (1 : ℂ)) (Set.Icc a b) = 0 := by
        rw [eVariationOn.eq_zero_iff]
        intro x hx y hy
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      rw [BoundedVariationOn, hzero]
      exact ENNReal.zero_ne_top
    · intro x hx
      exact Set.indicator_of_notMem hx _

@[simp]
theorem sharpInterval_apply (a b : ℝ) (ha : 0 < a) (hab : a < b) (x : ℝ) :
    sharpInterval a b ha hab x =
      (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ)) x :=
  rfl

/-- Literal closed interval window `1_[1,b]`, for `b > 1`. -/
def unitSharpInterval (b : ℝ) (hb : 1 < b) : CompactBVPrimeWindow :=
  sharpInterval 1 b zero_lt_one hb

@[simp]
theorem unitSharpInterval_apply (b : ℝ) (hb : 1 < b) (x : ℝ) :
    unitSharpInterval b hb x = (Set.Icc 1 b).indicator (fun _ : ℝ => (1 : ℂ)) x :=
  rfl

/-- Integral realization of a literal interval window's Mellin transform. -/
theorem mellinTransform_sharpInterval_eq_integral
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (s : ℂ) :
    (sharpInterval a b ha hab).mellinTransform s =
      ∫ x in a..b, (x : ℂ) ^ (-s) := by
  rw [mellinTransform]
  calc
    (∫ x : ℝ, (sharpInterval a b ha hab).mellinIntegrand s x) =
        ∫ x : ℝ, (Set.Icc a b).indicator (fun x : ℝ => (x : ℂ) ^ (-s)) x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [(sharpInterval a b ha hab).mellinIntegrand_eq_raw, sharpInterval_apply]
      by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
    _ = ∫ x : ℝ in Set.Icc a b, (x : ℂ) ^ (-s) :=
      integral_indicator measurableSet_Icc
    _ = ∫ x : ℝ in Set.Ioc a b, (x : ℂ) ^ (-s) :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, (x : ℂ) ^ (-s) :=
      (intervalIntegral.integral_of_le hab.le).symm

/-- Integral realization of the literal unit-anchored interval window's Mellin transform. -/
theorem mellinTransform_unitSharpInterval_eq_integral
    (b : ℝ) (hb : 1 < b) (s : ℂ) :
    (unitSharpInterval b hb).mellinTransform s =
      ∫ x in (1 : ℝ)..b, (x : ℂ) ^ (-s) := by
  simpa only [unitSharpInterval] using
    mellinTransform_sharpInterval_eq_integral 1 b zero_lt_one hb s

/-- The literal interval's Mellin integral equals the entire sharp-window amplitude, including the
removable coordinate `s = 1`. -/
theorem mellinTransform_unitSharpInterval
    (b : ℝ) (hb : 1 < b) (s : ℂ) :
    (unitSharpInterval b hb).mellinTransform s =
      sharpPrimeWindowMellin (Real.log b) s := by
  have hbpos : 0 < b := zero_lt_one.trans hb
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le hb.le]
    intro h
    linarith [h.1]
  by_cases hs : s = 1
  · subst s
    rw [mellinTransform_unitSharpInterval_eq_integral]
    have hfun : (fun x : ℝ => (x : ℂ) ^ (-(1 : ℂ))) =
        fun x : ℝ => ((1 / x : ℝ) : ℂ) := by
      funext x
      rw [Complex.cpow_neg_one]
      norm_num [div_eq_mul_inv]
    rw [hfun, intervalIntegral.integral_ofReal, integral_one_div hzero, div_one]
    simp [sharpPrimeWindowMellin]
  · have hneg : -s ≠ (-1 : ℂ) := by
      intro h
      exact hs (neg_inj.mp h)
    rw [mellinTransform_unitSharpInterval_eq_integral,
      integral_cpow (Or.inr ⟨hneg, hzero⟩)]
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbpos.ne'
    have hlogB : Complex.log (b : ℂ) = (Real.log b : ℂ) :=
      (Complex.ofReal_log hbpos.le).symm
    have hexpB : Complex.exp (-(Real.log b : ℂ) * (s - 1)) =
        (b : ℂ) ^ (1 - s) := by
      rw [Complex.cpow_def_of_ne_zero hbC, hlogB]
      congr 1
      ring
    rw [show -s + 1 = 1 - s by ring, Complex.ofReal_one, Complex.one_cpow,
      sharpPrimeWindowMellin, rectangularWindowAmplitude_eq_div
        (sub_ne_zero.mpr hs), hexpB]
    rw [div_eq_mul_inv, show 1 - s = -(s - 1) by ring, inv_neg]
    ring

/-- Fixed dyadic rational-interval BV window. -/
def dyadicSharpInterval : CompactBVPrimeWindow :=
  unitSharpInterval 2 (by norm_num)

/-- Fixed triadic rational-interval BV window. -/
def triadicSharpInterval : CompactBVPrimeWindow :=
  unitSharpInterval 3 (by norm_num)

@[simp]
theorem mellinTransform_dyadicSharpInterval (s : ℂ) :
    dyadicSharpInterval.mellinTransform s =
      sharpPrimeWindowMellin (Real.log 2) s := by
  simpa only [dyadicSharpInterval] using
    mellinTransform_unitSharpInterval 2 (by norm_num) s

@[simp]
theorem mellinTransform_triadicSharpInterval (s : ℂ) :
    triadicSharpInterval.mellinTransform s =
      sharpPrimeWindowMellin (Real.log 3) s := by
  simpa only [triadicSharpInterval] using
    mellinTransform_unitSharpInterval 3 (by norm_num) s

/-- One fixed literal dyadic BV window sees every Mellin coordinate in `Re s > 1`. -/
theorem mellinTransform_dyadicSharpInterval_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    dyadicSharpInterval.mellinTransform s ≠ 0 := by
  rw [mellinTransform_dyadicSharpInterval]
  exact sharpPrimeWindowMellin_ne_zero_of_one_lt_re
    (Real.log_pos (by norm_num)) hs

/-- One fixed literal dyadic BV window detects every right shifted Xi zero. -/
theorem mellinTransform_dyadicSharpInterval_ne_zero_at_xiRightShiftedPole
    (q : XiRightZeroCopy) :
    dyadicSharpInterval.mellinTransform (xiRightShiftedPole q) ≠ 0 := by
  apply mellinTransform_dyadicSharpInterval_ne_zero_of_one_lt_re
  rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
  linarith [xiRightCenteredZero_re_pos q]

/-- Fixed dyadic and triadic literal BV windows jointly see every complex coordinate. -/
theorem mellinTransform_dyadicSharpInterval_or_triadicSharpInterval_ne_zero
    (s : ℂ) :
    dyadicSharpInterval.mellinTransform s ≠ 0 ∨
      triadicSharpInterval.mellinTransform s ≠ 0 := by
  rw [mellinTransform_dyadicSharpInterval, mellinTransform_triadicSharpInterval]
  exact sharpPrimeWindowMellin_pair_nonzero_of_irrational_ratio
    (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
    (GaloisForLFunctions.RHTower.irrational_log_ratio
      Nat.prime_three Nat.prime_two (by norm_num)) s

/-- Index type of all positive rational intervals `(a,b)` with `a<b`. -/
abbrev RationalIntervalWindowIndex :=
  {p : ℚ × ℚ // 0 < p.1 ∧ p.1 < p.2}

/-- Full countable family of all positive rational interval indicators. -/
def rationalIntervalSeparatingFamily
    (i : RationalIntervalWindowIndex) : CompactBVPrimeWindow :=
  sharpInterval (i.1.1 : ℝ) (i.1.2 : ℝ)
    (by exact_mod_cast i.2.1) (by exact_mod_cast i.2.2)

/-- The full family's endpoint data are exactly the rational pair used as its index. -/
theorem rationalIntervalSeparatingFamily_endpoints
    (i : RationalIntervalWindowIndex) :
    (rationalIntervalSeparatingFamily i).lower = (i.1.1 : ℝ) ∧
      (rationalIntervalSeparatingFamily i).upper = (i.1.2 : ℝ) :=
  ⟨rfl, rfl⟩

/-- Reciprocal endpoint index `(a,b) ↦ (1/b,1/a)`. -/
def reciprocalRationalIntervalIndex
    (i : RationalIntervalWindowIndex) : RationalIntervalWindowIndex :=
  ⟨(i.1.2⁻¹, i.1.1⁻¹), inv_pos.mpr (i.2.1.trans i.2.2),
    by simpa only [one_div] using one_div_lt_one_div_of_lt i.2.1 i.2.2⟩

/-- Rational argument-dilation endpoint index `(a,b) ↦ (a/r,b/r)`. -/
def dilationRationalIntervalIndex
    (i : RationalIntervalWindowIndex) (r : ℚ) (hr : 0 < r) :
    RationalIntervalWindowIndex :=
  ⟨(i.1.1 / r, i.1.2 / r), div_pos i.2.1 hr, div_lt_div_of_pos_right i.2.2 hr⟩

/-- Rational argument-expansion endpoint index `(a,b) ↦ (ra,rb)`. -/
def expansionRationalIntervalIndex
    (i : RationalIntervalWindowIndex) (r : ℚ) (hr : 0 < r) :
    RationalIntervalWindowIndex :=
  ⟨(r * i.1.1, r * i.1.2), mul_pos hr i.2.1, mul_lt_mul_of_pos_left i.2.2 hr⟩

/-- The full rational interval family is exactly closed under reciprocal conjugation. -/
theorem rationalIntervalSeparatingFamily_reciprocal_closed
    (i : RationalIntervalWindowIndex) :
    (rationalIntervalSeparatingFamily i).reciprocalConjugate =
      rationalIntervalSeparatingFamily (reciprocalRationalIntervalIndex i) := by
  apply ext
  · simp [rationalIntervalSeparatingFamily, reciprocalRationalIntervalIndex, sharpInterval]
  · simp [rationalIntervalSeparatingFamily, reciprocalRationalIntervalIndex, sharpInterval]
  · funext x
    rw [show (rationalIntervalSeparatingFamily i).reciprocalConjugate.toFun x =
        (starRingEnd ℂ) (rationalIntervalSeparatingFamily i x⁻¹) by rfl]
    rw [rationalIntervalSeparatingFamily, sharpInterval_apply,
      rationalIntervalSeparatingFamily, sharpInterval_apply]
    have ha : (0 : ℝ) < (i.1.1 : ℚ) := by exact_mod_cast i.2.1
    have hb : (0 : ℝ) < (i.1.2 : ℚ) := by exact_mod_cast i.2.1.trans i.2.2
    have hmem : x⁻¹ ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ) ↔
        x ∈ Set.Icc ((i.1.2 : ℝ)⁻¹) ((i.1.1 : ℝ)⁻¹) := by
      constructor
      · intro hx
        have hxinvpos : 0 < x⁻¹ := ha.trans_le hx.1
        have hxpos : 0 < x := inv_pos.mp hxinvpos
        exact ⟨(inv_le_comm₀ hb hxpos).2 hx.2, (le_inv_comm₀ hxpos ha).2 hx.1⟩
      · intro hx
        have hxpos : 0 < x := (inv_pos.mpr hb).trans_le hx.1
        exact ⟨(le_inv_comm₀ hxpos ha).1 hx.2, (inv_le_comm₀ hb hxpos).1 hx.1⟩
    simp only [reciprocalRationalIntervalIndex, Rat.cast_inv]
    by_cases hx : x⁻¹ ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mpr hx)]
      simp

/-- The full rational interval family is exactly closed under every positive rational argument
dilation. -/
theorem rationalIntervalSeparatingFamily_dilation_closed
    (i : RationalIntervalWindowIndex) (r : ℚ) (hr : 0 < r) :
    (rationalIntervalSeparatingFamily i).argumentDilation (r : ℝ)
        (by exact_mod_cast hr) =
      rationalIntervalSeparatingFamily (dilationRationalIntervalIndex i r hr) := by
  apply ext
  · simp [rationalIntervalSeparatingFamily, dilationRationalIntervalIndex, sharpInterval]
  · simp [rationalIntervalSeparatingFamily, dilationRationalIntervalIndex, sharpInterval]
  · funext x
    rw [show ((rationalIntervalSeparatingFamily i).argumentDilation (r : ℝ)
        (by exact_mod_cast hr)).toFun x =
        rationalIntervalSeparatingFamily i ((r : ℝ) * x) by rfl]
    rw [rationalIntervalSeparatingFamily, sharpInterval_apply,
      rationalIntervalSeparatingFamily, sharpInterval_apply]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hmem : (r : ℝ) * x ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ) ↔
        x ∈ Set.Icc ((i.1.1 : ℝ) / r) ((i.1.2 : ℝ) / r) := by
      constructor
      · intro hx
        exact ⟨(div_le_iff₀ hrR).2 (by simpa [mul_comm] using hx.1),
          (le_div_iff₀ hrR).2 (by simpa [mul_comm] using hx.2)⟩
      · intro hx
        exact ⟨by simpa [mul_comm] using (div_le_iff₀ hrR).1 hx.1,
          by simpa [mul_comm] using (le_div_iff₀ hrR).1 hx.2⟩
    simp only [dilationRationalIntervalIndex, Rat.cast_div]
    by_cases hx : (r : ℝ) * x ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mpr hx)]

/-- The full rational interval family is exactly closed under every positive rational argument
expansion. -/
theorem rationalIntervalSeparatingFamily_expansion_closed
    (i : RationalIntervalWindowIndex) (r : ℚ) (hr : 0 < r) :
    (rationalIntervalSeparatingFamily i).argumentExpansion (r : ℝ)
        (by exact_mod_cast hr) =
      rationalIntervalSeparatingFamily (expansionRationalIntervalIndex i r hr) := by
  apply ext
  · simp [argumentExpansion, rationalIntervalSeparatingFamily,
      expansionRationalIntervalIndex, sharpInterval, mul_comm]
  · simp [argumentExpansion, rationalIntervalSeparatingFamily,
      expansionRationalIntervalIndex, sharpInterval, mul_comm]
  · funext x
    rw [show ((rationalIntervalSeparatingFamily i).argumentExpansion (r : ℝ)
        (by exact_mod_cast hr)).toFun x = rationalIntervalSeparatingFamily i (x / (r : ℝ)) by
      exact argumentExpansion_apply _ _ _ _]
    rw [rationalIntervalSeparatingFamily, sharpInterval_apply,
      rationalIntervalSeparatingFamily, sharpInterval_apply]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hmem : x / (r : ℝ) ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ) ↔
        x ∈ Set.Icc ((r : ℝ) * i.1.1) ((r : ℝ) * i.1.2) := by
      constructor
      · intro hx
        exact ⟨by simpa [mul_comm] using (le_div_iff₀ hrR).1 hx.1,
          by simpa [mul_comm] using (div_le_iff₀ hrR).1 hx.2⟩
      · intro hx
        exact ⟨(le_div_iff₀ hrR).2 (by simpa [mul_comm] using hx.1),
          (div_le_iff₀ hrR).2 (by simpa [mul_comm] using hx.2)⟩
    simp only [expansionRationalIntervalIndex, Rat.cast_mul]
    by_cases hx : x / (r : ℝ) ∈ Set.Icc (i.1.1 : ℝ) (i.1.2 : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mpr hx)]

/-- Dyadic witness inside the full rational interval family. -/
def dyadicRationalIntervalIndex : RationalIntervalWindowIndex :=
  ⟨(1, 2), by norm_num⟩

/-- Triadic witness inside the full rational interval family. -/
def triadicRationalIntervalIndex : RationalIntervalWindowIndex :=
  ⟨(1, 3), by norm_num⟩

/-- The full positive rational interval family is countable. -/
theorem range_rationalIntervalSeparatingFamily_countable :
    (Set.range rationalIntervalSeparatingFamily).Countable :=
  Set.countable_range _

/-- Fixed countable operation-stable rational interval family separates every Mellin fibre. -/
theorem exists_rationalIntervalSeparatingFamily_mellinTransform_ne_zero
    (s : ℂ) :
    ∃ i : RationalIntervalWindowIndex,
      (rationalIntervalSeparatingFamily i).mellinTransform s ≠ 0 := by
  rcases mellinTransform_dyadicSharpInterval_or_triadicSharpInterval_ne_zero s with h | h
  · refine ⟨dyadicRationalIntervalIndex, ?_⟩
    simpa [rationalIntervalSeparatingFamily, dyadicRationalIntervalIndex,
      dyadicSharpInterval, unitSharpInterval] using h
  · refine ⟨triadicRationalIntervalIndex, ?_⟩
    simpa [rationalIntervalSeparatingFamily, triadicRationalIntervalIndex,
      triadicSharpInterval, unitSharpInterval] using h

end CompactBVPrimeWindow
end RHTower
