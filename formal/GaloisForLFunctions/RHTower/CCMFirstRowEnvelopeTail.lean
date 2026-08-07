import GaloisForLFunctions.RHTower.CCMFirstRowVanDerCorputBlocks

/-!
# The Bessel envelope tail integral

The remainder layer of the first-row Gram entry is controlled by the single elementary integral

```text
int_1^infinity x^(-3/2) (1 + c sqrt(x²-1))^(-1/2) dx <= C c^(-1/2),
```

proved here with the explicit constant `3`.  The two blocks are:

* on `x >= 2` the envelope factor is at most `c^(-1/2)` and the power `x^(-3/2)` integrates to
  `sqrt 2` — the exact value coming from the antiderivative `-2 x^(-1/2)`;
* on `1 < x <= 2` the power is at most `1` and the envelope factor is at most
  `c^(-1/2)(x-1)^(-1/4)`, because `sqrt(x²-1) >= sqrt(x-1)`; the remaining integral is exactly `4/3`.

The endpoint of the near block is singular, which is why the integrand is compared with a fractional
power rather than bounded pointwise.

Main statement: **`integral_Ioi_envelopeTail_le`**.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-! ## The pure power `x^{-3/2}` -/

/-- The power `x^{-3/2}`, written without `rpow`. -/
def invPow32 (x : ℝ) : ℝ := 1 / (x * Real.sqrt x)

theorem invPow32_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ invPow32 x := by
  rw [invPow32]
  positivity

theorem hasDerivAt_negTwoDivSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -2 / Real.sqrt t) (invPow32 x) x := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have h := (hasDerivAt_const x (-2 : ℝ)).fun_div (Real.hasDerivAt_sqrt hx.ne') hs
  have hval : ((0 : ℝ) * Real.sqrt x - (-2) * (1 / (2 * Real.sqrt x))) / Real.sqrt x ^ 2
      = invPow32 x := by
    rw [invPow32, Real.sq_sqrt hx.le]
    field_simp
    ring
  rw [hval] at h
  exact h

theorem tendsto_negTwoDivSqrt : Tendsto (fun t : ℝ => -2 / Real.sqrt t) atTop (𝓝 0) :=
  Filter.Tendsto.div_atTop (tendsto_const_nhds) Real.tendsto_sqrt_atTop

theorem continuousWithinAt_negTwoDivSqrt {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (fun t : ℝ => -2 / Real.sqrt t) (Ici a) a := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  exact (ContinuousAt.div continuousAt_const (Real.continuous_sqrt.continuousAt) hs).continuousWithinAt

theorem integrableOn_invPow32 {a : ℝ} (ha : 0 < a) : IntegrableOn invPow32 (Ioi a) volume :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_negTwoDivSqrt ha)
    (fun _ hx => hasDerivAt_negTwoDivSqrt (lt_trans ha hx))
    (fun _ hx => invPow32_nonneg (le_of_lt (lt_trans ha hx))) tendsto_negTwoDivSqrt

/-- The exact tail mass of the power `x^{-3/2}`. -/
theorem integral_Ioi_invPow32 {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, invPow32 x) = 2 / Real.sqrt a := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
    (continuousWithinAt_negTwoDivSqrt ha)
    (fun _ hx => hasDerivAt_negTwoDivSqrt (lt_trans ha hx))
    (fun _ hx => invPow32_nonneg (le_of_lt (lt_trans ha hx))) tendsto_negTwoDivSqrt
  rw [h]
  ring

/-! ## The fractional power at the endpoint -/

theorem intervalIntegrable_rpow_sub_one_gen {r : ℝ} (hr : -1 < r) {x : ℝ} :
    IntervalIntegrable (fun t : ℝ => (t - 1) ^ r) volume 1 x := by
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 (x - 1) :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h := hbase.comp_sub_right 1
  simpa using h

theorem rpow_neg_quarter {t : ℝ} (ht : 0 < t) :
    t ^ (-(1 : ℝ) / 4) = 1 / Real.sqrt (Real.sqrt t) := by
  have h4 : Real.sqrt (Real.sqrt t) = t ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    norm_num
  rw [h4, show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) from by ring, Real.rpow_neg ht.le,
    inv_eq_one_div]

/-- The exact endpoint mass of the fractional power. -/
theorem integral_Ioc_rpow_sub_one :
    (∫ x in Ioc (1 : ℝ) 2, (x - 1) ^ (-(1 : ℝ) / 4)) = 4 / 3 := by
  have h := intervalIntegral.integral_comp_sub_right
    (fun t : ℝ => t ^ (-(1 : ℝ) / 4)) 1 (a := 1) (b := 2)
  have hval : (∫ x in (0 : ℝ)..(1 : ℝ), x ^ (-(1 : ℝ) / 4)) = 4 / 3 := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  rw [h]
  norm_num at hval ⊢
  exact hval

/-! ## The envelope integrand -/

/-- The envelope integrand `x^{-3/2}(1 + c sqrt(x²-1))^{-1/2}`. -/
def envelopeTail (c x : ℝ) : ℝ :=
  1 / (x * Real.sqrt x * Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)))

theorem measurable_envelopeTail (c : ℝ) : Measurable (envelopeTail c) := by
  unfold envelopeTail
  fun_prop

theorem envelopeTail_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) : 0 ≤ envelopeTail c x := by
  rw [envelopeTail]
  positivity

theorem envelopeTail_eq_mul {c x : ℝ} :
    envelopeTail c x = invPow32 x * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1))) := by
  rw [envelopeTail, invPow32, div_mul_div_comm, one_mul]

theorem envelopeTail_le_invPow32 {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) :
    envelopeTail c x ≤ invPow32 x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsq : (0 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
  have hone : (1 : ℝ) ≤ 1 + c * Real.sqrt (x ^ 2 - 1) := by
    have : (0 : ℝ) ≤ c * Real.sqrt (x ^ 2 - 1) := by positivity
    linarith
  have hroot : (1 : ℝ) ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) :=
    Real.one_le_sqrt.mpr hone
  rw [envelopeTail_eq_mul]
  have hpos : (0 : ℝ) < invPow32 x := by
    rw [invPow32]; positivity
  calc invPow32 x * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)))
      ≤ invPow32 x * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        rw [div_le_one (by linarith)]
        exact hroot
    _ = invPow32 x := mul_one _

theorem integrableOn_envelopeTail {c a : ℝ} (hc : 0 ≤ c) (ha1 : 1 ≤ a) :
    IntegrableOn (envelopeTail c) (Ioi a) volume := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  refine MeasureTheory.Integrable.mono' (integrableOn_invPow32 ha)
    (measurable_envelopeTail c).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans ha1 (le_of_lt hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (envelopeTail_nonneg hc (by linarith))]
  exact envelopeTail_le_invPow32 hc hx1

/-! ## The far block -/

theorem integral_Ioi_two_envelopeTail_le {c : ℝ} (hc : 1 ≤ c) :
    (∫ x in Ioi (2 : ℝ), envelopeTail c x) ≤ Real.sqrt 2 / Real.sqrt c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hcomp : IntegrableOn (fun x : ℝ => invPow32 x / Real.sqrt c) (Ioi 2) volume :=
    (integrableOn_invPow32 (by norm_num)).div_const _
  have hmono : (∫ x in Ioi (2 : ℝ), envelopeTail c x)
      ≤ ∫ x in Ioi (2 : ℝ), invPow32 x / Real.sqrt c := by
    refine MeasureTheory.setIntegral_mono_on
      (integrableOn_envelopeTail hc0.le (by norm_num)) hcomp measurableSet_Ioi ?_
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have hsq : (1 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
    have hroot : (1 : ℝ) ≤ Real.sqrt (x ^ 2 - 1) := Real.one_le_sqrt.mpr hsq
    have hlow : c ≤ 1 + c * Real.sqrt (x ^ 2 - 1) := by nlinarith
    have hrootc : Real.sqrt c ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) :=
      Real.sqrt_le_sqrt hlow
    have hpos : (0 : ℝ) < invPow32 x := by
      rw [invPow32]
      have : (0 : ℝ) < x := by linarith
      positivity
    calc envelopeTail c x = invPow32 x * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1))) :=
          envelopeTail_eq_mul
      _ ≤ invPow32 x * (1 / Real.sqrt c) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hcs hrootc) hpos.le
      _ = invPow32 x / Real.sqrt c := by rw [mul_one_div]
  refine hmono.trans ?_
  rw [MeasureTheory.integral_div, integral_Ioi_invPow32 (by norm_num : (0:ℝ) < 2),
    Real.div_sqrt]

/-! ## The near block -/

theorem integral_Ioc_envelopeTail_le {c : ℝ} (hc : 1 ≤ c) :
    (∫ x in Ioc (1 : ℝ) 2, envelopeTail c x) ≤ (4 / 3) / Real.sqrt c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hnear : IntegrableOn (fun x : ℝ => (x - 1) ^ (-(1 : ℝ) / 4) / Real.sqrt c)
      (Ioc 1 2) volume := by
    have h := (intervalIntegrable_rpow_sub_one_gen (r := -(1 : ℝ) / 4) (by norm_num)
      (x := (2 : ℝ)))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 2)] at h
    exact h.div_const _
  have henv : IntegrableOn (envelopeTail c) (Ioc 1 2) volume := by
    refine MeasureTheory.Integrable.mono' hnear
      (measurable_envelopeTail c).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hsub : (0 : ℝ) < x - 1 := by linarith
    have hnn : 0 ≤ envelopeTail c x := envelopeTail_nonneg hc0.le hx0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    -- the pointwise comparison
    have hpow : invPow32 x ≤ 1 := by
      rw [invPow32, div_le_one (by positivity)]
      have hs : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1.le
      nlinarith
    have hfact : Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))
        ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := by
      have hsub2 : Real.sqrt (x - 1) ≤ Real.sqrt (x ^ 2 - 1) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith
      have hlow : c * Real.sqrt (x - 1) ≤ 1 + c * Real.sqrt (x ^ 2 - 1) := by
        nlinarith [Real.sqrt_nonneg (x - 1)]
      have hstep : Real.sqrt (c * Real.sqrt (x - 1))
          ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := Real.sqrt_le_sqrt hlow
      rwa [Real.sqrt_mul hc0.le] at hstep
    have hquarter : (x - 1) ^ (-(1 : ℝ) / 4) = 1 / Real.sqrt (Real.sqrt (x - 1)) :=
      rpow_neg_quarter hsub
    have hqpos : (0 : ℝ) < Real.sqrt (Real.sqrt (x - 1)) :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hsub)
    have hdpos : (0 : ℝ) < Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := by
      have : (0 : ℝ) < 1 + c * Real.sqrt (x ^ 2 - 1) := by
        have : (0 : ℝ) ≤ c * Real.sqrt (x ^ 2 - 1) := by positivity
        linarith
      exact Real.sqrt_pos.mpr this
    rw [hquarter, envelopeTail_eq_mul]
    calc invPow32 x * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)))
        ≤ 1 * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1))) := by
          refine mul_le_mul_of_nonneg_right hpow ?_
          positivity
      _ = 1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := one_mul _
      _ ≤ 1 / (Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))) :=
          one_div_le_one_div_of_le (by positivity) hfact
      _ = 1 / Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt c := by
          rw [div_div, mul_comm]
  have hmono : (∫ x in Ioc (1 : ℝ) 2, envelopeTail c x)
      ≤ ∫ x in Ioc (1 : ℝ) 2, (x - 1) ^ (-(1 : ℝ) / 4) / Real.sqrt c := by
    refine MeasureTheory.setIntegral_mono_on henv hnear measurableSet_Ioc ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hsub : (0 : ℝ) < x - 1 := by linarith
    have hpow : invPow32 x ≤ 1 := by
      rw [invPow32, div_le_one (by positivity)]
      have hs : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1.le
      nlinarith
    have hfact : Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))
        ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := by
      have hsub2 : Real.sqrt (x - 1) ≤ Real.sqrt (x ^ 2 - 1) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith
      have hlow : c * Real.sqrt (x - 1) ≤ 1 + c * Real.sqrt (x ^ 2 - 1) := by
        nlinarith [Real.sqrt_nonneg (x - 1)]
      have hstep : Real.sqrt (c * Real.sqrt (x - 1))
          ≤ Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := Real.sqrt_le_sqrt hlow
      rwa [Real.sqrt_mul hc0.le] at hstep
    have hquarter : (x - 1) ^ (-(1 : ℝ) / 4) = 1 / Real.sqrt (Real.sqrt (x - 1)) :=
      rpow_neg_quarter hsub
    rw [hquarter, envelopeTail_eq_mul]
    calc invPow32 x * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)))
        ≤ 1 * (1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1))) := by
          refine mul_le_mul_of_nonneg_right hpow ?_
          positivity
      _ = 1 / Real.sqrt (1 + c * Real.sqrt (x ^ 2 - 1)) := one_mul _
      _ ≤ 1 / (Real.sqrt c * Real.sqrt (Real.sqrt (x - 1))) :=
          one_div_le_one_div_of_le (by positivity) hfact
      _ = 1 / Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt c := by
          rw [div_div, mul_comm]
  refine hmono.trans ?_
  rw [MeasureTheory.integral_div, integral_Ioc_rpow_sub_one]

/-! ## Equation (16) -/

/-- **Equation (16).**  The envelope tail integral is `O(c^{-1/2})` with the explicit constant `3`.
The near block contributes `4/3` and the far block `sqrt 2`. -/
theorem integral_Ioi_envelopeTail_le {c : ℝ} (hc : 1 ≤ c) :
    (∫ x in Ioi (1 : ℝ), envelopeTail c x) ≤ 3 / Real.sqrt c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hunion : Ioc (1 : ℝ) 2 ∪ Ioi 2 = Ioi 1 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hdisj : Disjoint (Ioc (1 : ℝ) 2) (Ioi 2) := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact absurd hx'.out (not_lt.mpr hx.2)
  have hI1 : IntegrableOn (envelopeTail c) (Ioc 1 2) volume := by
    have h := integrableOn_envelopeTail (c := c) hc0.le (le_refl 1)
    exact h.mono_set (fun x hx => hx.1)
  have hI2 : IntegrableOn (envelopeTail c) (Ioi 2) volume := by
    have h := integrableOn_envelopeTail (c := c) hc0.le (le_refl 1)
    exact h.mono_set (fun x hx => lt_trans (by norm_num : (1:ℝ) < 2) hx)
  have hsplit : (∫ x in Ioi (1 : ℝ), envelopeTail c x)
      = (∫ x in Ioc (1 : ℝ) 2, envelopeTail c x) + ∫ x in Ioi (2 : ℝ), envelopeTail c x := by
    rw [← hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hI1 hI2
  rw [hsplit]
  have h1 := integral_Ioc_envelopeTail_le hc
  have h2 := integral_Ioi_two_envelopeTail_le hc
  have hsum : (4 / 3) / Real.sqrt c + Real.sqrt 2 / Real.sqrt c ≤ 3 / Real.sqrt c := by
    rw [← add_div, div_le_div_iff₀ hcs hcs]
    have hs2 : Real.sqrt 2 ≤ 5 / 3 := by
      have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    nlinarith [hcs, hs2]
  linarith

/-! ## The two-amplitude envelope product -/

/-- The majorant of the Bessel remainder layer of `(15)`: the two Liouville–Green amplitudes against
the two Bessel envelopes `(1 + c xi)^{-1/2}`. -/
def envelopeProduct (s c k x : ℝ) : ℝ :=
  xiAmplitude s x * xiAmplitude s (k * x)
    * (1 / Real.sqrt (1 + c * xiEndpointPhase s x))
    * (1 / Real.sqrt (1 + c * xiEndpointPhase s (k * x)))

theorem xiAmplitude_nonneg (s x : ℝ) : 0 ≤ xiAmplitude s x := by
  rw [xiAmplitude]
  positivity

theorem envelopeProduct_nonneg (s c k x : ℝ) : 0 ≤ envelopeProduct s c k x := by
  rw [envelopeProduct]
  have h1 := xiAmplitude_nonneg s x
  have h2 := xiAmplitude_nonneg s (k * x)
  have h3 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + c * xiEndpointPhase s x) := by positivity
  have h4 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + c * xiEndpointPhase s (k * x)) := by positivity
  positivity

theorem xiEndpointPhase_nonneg {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : 1 ≤ x) :
    0 ≤ xiEndpointPhase s x := by
  refine le_trans ?_ (xiEndpointPhase_bounds hs0 hs1 hx).1
  positivity

/-! ### Continuity in the interior -/

theorem continuousOn_xiEndpointPhase {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (xiEndpointPhase s) (Ioi 1) :=
  fun _ hx => ((hasDerivAt_xiEndpointPhase hs hx).continuousAt).continuousWithinAt

theorem continuousOn_xiAmplitude {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (xiAmplitude s) (Ioi 1) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hden : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) ≠ 0 := by
    have hprod : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := by positivity
    exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hprod)).ne'
  have hnum : ContinuousWithinAt (fun t : ℝ => Real.sqrt (xiEndpointPhase s t)) (Ioi 1) x :=
    (continuousOn_xiEndpointPhase hs0 x hx).sqrt
  have hd : ContinuousWithinAt
      (fun t : ℝ => Real.sqrt (Real.sqrt ((t ^ 2 - 1) * (t ^ 2 - s)))) (Ioi 1) x :=
    (by fun_prop : Continuous
      fun t : ℝ => Real.sqrt (Real.sqrt ((t ^ 2 - 1) * (t ^ 2 - s)))).continuousWithinAt
  exact hnum.div hd hden

theorem mapsTo_mul_left_Ioi {k : ℝ} (hk : 2 ≤ k) :
    Set.MapsTo (fun x : ℝ => k * x) (Ioi 1) (Ioi 1) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have : (1 : ℝ) < k * x := by nlinarith
  exact this

theorem continuousOn_envelopeProduct {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 ≤ c)
    (hk : 2 ≤ k) : ContinuousOn (envelopeProduct s c k) (Ioi 1) := by
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hA : ContinuousOn (xiAmplitude s) (Ioi 1) := continuousOn_xiAmplitude hs0 hs1
  have hB : ContinuousOn (fun x : ℝ => xiAmplitude s (k * x)) (Ioi 1) :=
    hA.comp hlin (mapsTo_mul_left_Ioi hk)
  have hP : ContinuousOn (xiEndpointPhase s) (Ioi 1) := continuousOn_xiEndpointPhase hs0
  have hQ : ContinuousOn (fun x : ℝ => xiEndpointPhase s (k * x)) (Ioi 1) :=
    hP.comp hlin (mapsTo_mul_left_Ioi hk)
  have hC : ContinuousOn (fun x : ℝ => 1 / Real.sqrt (1 + c * xiEndpointPhase s x)) (Ioi 1) := by
    intro x hx
    have hpos : (0 : ℝ) < 1 + c * xiEndpointPhase s x := by
      have hnn := xiEndpointPhase_nonneg hs0 (by linarith) (le_of_lt hx)
      have : (0 : ℝ) ≤ c * xiEndpointPhase s x := by positivity
      linarith
    exact continuousWithinAt_const.div
      ((continuousWithinAt_const.add (continuousWithinAt_const.mul (hP x hx))).sqrt)
      (Real.sqrt_pos.mpr hpos).ne'
  have hD : ContinuousOn
      (fun x : ℝ => 1 / Real.sqrt (1 + c * xiEndpointPhase s (k * x))) (Ioi 1) := by
    intro x hx
    have hkx : (1 : ℝ) < k * x := mapsTo_mul_left_Ioi hk hx
    have hpos : (0 : ℝ) < 1 + c * xiEndpointPhase s (k * x) := by
      have hnn := xiEndpointPhase_nonneg hs0 (by linarith) (le_of_lt hkx)
      have : (0 : ℝ) ≤ c * xiEndpointPhase s (k * x) := by positivity
      linarith
    exact continuousWithinAt_const.div
      ((continuousWithinAt_const.add (continuousWithinAt_const.mul (hQ x hx))).sqrt)
      (Real.sqrt_pos.mpr hpos).ne'
  exact ((hA.mul hB).mul hC).mul hD

/-! ### The pointwise majorant -/

private theorem envelope_root_identity {A K X C R : ℝ} (hK : 0 < K) (hX : 0 < X) (hC : 0 < C)
    (hR : 0 < R) (hA : 0 < A) :
    A / X * (A / (K * X)) * (1 / R) * (A * A / (C * (K * X)))
      = A * A * (A * A) / (K * K * C) * (1 / (X * X * X * R)) := by
  field_simp

/-- The lower bound on the phase used by both envelope factors: `xi_s(x) >= sqrt(x²-1)/sqrt 2`. -/
theorem sqrt_div_sqrt_two_le_xiEndpointPhase {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 ≤ x) : Real.sqrt (x ^ 2 - 1) / Real.sqrt 2 ≤ xiEndpointPhase s x := by
  have hsq : (0 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
  have hb := (xiEndpointPhase_bounds hs0 (by linarith) hx).1
  have hmul : Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) = Real.sqrt ((1 - s) * (x ^ 2 - 1)) :=
    (Real.sqrt_mul (by linarith) _).symm
  have hq : (x ^ 2 - 1) / 2 ≤ (1 - s) * (x ^ 2 - 1) := by nlinarith
  have h2 := Real.sqrt_le_sqrt hq
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)] at h2
  rw [hmul] at hb
  linarith

/-- At the far argument the phase is bounded below linearly: `xi_s(k x) >= k x / 2`. -/
theorem half_mul_le_xiEndpointPhase_far {s u : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hu : 2 < u) :
    u / 2 ≤ xiEndpointPhase s u := by
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hb := (xiEndpointPhase_bounds hs0 (by linarith) hu1).1
  have hmul : Real.sqrt (1 - s) * Real.sqrt (u ^ 2 - 1) = Real.sqrt ((1 - s) * (u ^ 2 - 1)) :=
    (Real.sqrt_mul (by linarith) _).symm
  have hq : (u / 2) ^ 2 ≤ (1 - s) * (u ^ 2 - 1) := by nlinarith
  have h2 := Real.sqrt_le_sqrt hq
  rw [Real.sqrt_sq (by linarith)] at h2
  rw [hmul] at hb
  linarith

/-- **The pointwise majorant of `(15)`.**  The two amplitudes and the far envelope contribute
`2 c^{-1/2} k^{-1} x^{-3/2}`, and the near envelope is exactly the integrand of `(16)` at the
rescaled aperture `c / sqrt 2`. -/
theorem envelopeProduct_le {s c k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 2 ≤ c) (hk : 2 ≤ k)
    (hx : 1 < x) :
    envelopeProduct s c k x
      ≤ 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hkx : (1 : ℝ) < k * x := by nlinarith
  have hkx2 : (2 : ℝ) < k * x := by nlinarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hA : (0 : ℝ) < Real.sqrt (Real.sqrt 2) := Real.sqrt_pos.mpr hs2
  have hX : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hK : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hC : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsqx : (0 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
  set R : ℝ := Real.sqrt (1 + c / Real.sqrt 2 * Real.sqrt (x ^ 2 - 1)) with hRdef
  have hRpos : (0 : ℝ) < R := by
    rw [hRdef]
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) ≤ c / Real.sqrt 2 * Real.sqrt (x ^ 2 - 1) := by positivity
    linarith
  -- the near envelope
  have hnear : 1 / Real.sqrt (1 + c * xiEndpointPhase s x) ≤ 1 / R := by
    refine one_div_le_one_div_of_le hRpos ?_
    rw [hRdef]
    refine Real.sqrt_le_sqrt ?_
    have hlow := sqrt_div_sqrt_two_le_xiEndpointPhase hs0 hs1 hx.le
    have : c / Real.sqrt 2 * Real.sqrt (x ^ 2 - 1) = c * (Real.sqrt (x ^ 2 - 1) / Real.sqrt 2) := by
      ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hlow hc0.le
    linarith
  -- the far envelope
  have hfar : 1 / Real.sqrt (1 + c * xiEndpointPhase s (k * x))
      ≤ Real.sqrt 2 / Real.sqrt (c * (k * x)) := by
    have hlow := half_mul_le_xiEndpointPhase_far hs0 hs1 hkx2
    have hstep : c * (k * x) / 2 ≤ 1 + c * xiEndpointPhase s (k * x) := by
      have := mul_le_mul_of_nonneg_left hlow hc0.le
      have hdiv : c * ((k * x) / 2) = c * (k * x) / 2 := by ring
      linarith [hdiv ▸ this]
    have hsqrt : Real.sqrt (c * (k * x) / 2) ≤ Real.sqrt (1 + c * xiEndpointPhase s (k * x)) :=
      Real.sqrt_le_sqrt hstep
    have hval : Real.sqrt (c * (k * x) / 2) = Real.sqrt (c * (k * x)) / Real.sqrt 2 :=
      Real.sqrt_div' _ (by norm_num)
    rw [hval] at hsqrt
    have hpos : (0 : ℝ) < Real.sqrt (c * (k * x)) / Real.sqrt 2 := by
      have : (0 : ℝ) < Real.sqrt (c * (k * x)) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have h := one_div_le_one_div_of_le hpos hsqrt
    rw [one_div_div] at h
    exact h
  -- the two amplitudes
  have hAx : xiAmplitude s x ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x := xiAmplitude_le hs0 hs1 hx
  have hAkx : xiAmplitude s (k * x) ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt (k * x) :=
    xiAmplitude_le hs0 hs1 hkx
  have hnn1 : (0 : ℝ) ≤ xiAmplitude s x := xiAmplitude_nonneg s x
  have hnn2 : (0 : ℝ) ≤ xiAmplitude s (k * x) := xiAmplitude_nonneg s (k * x)
  have hnn3 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + c * xiEndpointPhase s x) := by positivity
  have hnn4 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + c * xiEndpointPhase s (k * x)) := by positivity
  have hbound : envelopeProduct s c k x
      ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x * (Real.sqrt (Real.sqrt 2) / Real.sqrt (k * x))
        * (1 / R) * (Real.sqrt 2 / Real.sqrt (c * (k * x))) := by
    rw [envelopeProduct]
    gcongr
  refine hbound.trans ?_
  -- the algebraic collapse
  have e1 : Real.sqrt (k * x) = Real.sqrt k * Real.sqrt x := Real.sqrt_mul hk0.le x
  have e2 : Real.sqrt (c * (k * x)) = Real.sqrt c * (Real.sqrt k * Real.sqrt x) := by
    rw [Real.sqrt_mul hc0.le, e1]
  have e3 : Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt 2) = Real.sqrt 2 :=
    Real.mul_self_sqrt (Real.sqrt_nonneg 2)
  have e4 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e5 : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have e6 : Real.sqrt x * Real.sqrt x * Real.sqrt x = x * Real.sqrt x := by
    rw [Real.mul_self_sqrt hx0.le]
  calc Real.sqrt (Real.sqrt 2) / Real.sqrt x * (Real.sqrt (Real.sqrt 2) / Real.sqrt (k * x))
        * (1 / R) * (Real.sqrt 2 / Real.sqrt (c * (k * x)))
      = Real.sqrt (Real.sqrt 2) / Real.sqrt x
          * (Real.sqrt (Real.sqrt 2) / (Real.sqrt k * Real.sqrt x)) * (1 / R)
          * (Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt 2)
              / (Real.sqrt c * (Real.sqrt k * Real.sqrt x))) := by
        rw [e1, e2, e3]
    _ = Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt 2)
          * (Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt 2))
          / (Real.sqrt k * Real.sqrt k * Real.sqrt c)
          * (1 / (Real.sqrt x * Real.sqrt x * Real.sqrt x * R)) :=
        envelope_root_identity hK hX hC hRpos hA
    _ = 2 / (k * Real.sqrt c) * (1 / (x * Real.sqrt x * R)) := by
        rw [e3, e4, e5, e6]
    _ = 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x := by
        rw [envelopeTail, hRdef]
    _ ≤ 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x := le_refl _

/-! ### Equation (15) -/

theorem integrableOn_envelopeProduct {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 2 ≤ c)
    (hk : 2 ≤ k) : IntegrableOn (envelopeProduct s c k) (Ioi 1) volume := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hC : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcs : (1 : ℝ) ≤ c / Real.sqrt 2 := by
    rw [le_div_iff₀ hs2]
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  have hdom : IntegrableOn
      (fun x : ℝ => 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x) (Ioi 1) volume :=
    (integrableOn_envelopeTail (by positivity) (le_refl 1)).const_mul _
  refine MeasureTheory.Integrable.mono' hdom
    ((continuousOn_envelopeProduct hs0 hs1 hc0.le hk).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (envelopeProduct_nonneg s c k x)]
  exact envelopeProduct_le hs0 hs1 hc hk hx

/-- **Equation (15).**  The whole envelope remainder layer of the first-row entry is `O(1/(c k))`,
with the explicit constant `8`.  The prefactor `c` of `(5)` then cancels one power, which is what
makes the remainder summable on the exact aperture. -/
theorem integral_Ioi_envelopeProduct_le {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 2 ≤ c)
    (hk : 2 ≤ k) :
    (∫ x in Ioi (1 : ℝ), envelopeProduct s c k x) ≤ 8 / (c * k) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hC : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hA : (0 : ℝ) < Real.sqrt (Real.sqrt 2) := Real.sqrt_pos.mpr hs2
  have hcs : (1 : ℝ) ≤ c / Real.sqrt 2 := by
    rw [le_div_iff₀ hs2]
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  have hdom : IntegrableOn
      (fun x : ℝ => 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x) (Ioi 1) volume :=
    (integrableOn_envelopeTail (by positivity) (le_refl 1)).const_mul _
  have hmono : (∫ x in Ioi (1 : ℝ), envelopeProduct s c k x)
      ≤ ∫ x in Ioi (1 : ℝ), 2 / (k * Real.sqrt c) * envelopeTail (c / Real.sqrt 2) x := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_envelopeProduct hs0 hs1 hc hk) hdom
      measurableSet_Ioi ?_
    intro x hx
    exact envelopeProduct_le hs0 hs1 hc hk hx
  rw [MeasureTheory.integral_const_mul] at hmono
  have htail := integral_Ioi_envelopeTail_le hcs
  have hprod : 2 / (k * Real.sqrt c) * (∫ x in Ioi (1 : ℝ), envelopeTail (c / Real.sqrt 2) x)
      ≤ 2 / (k * Real.sqrt c) * (3 / Real.sqrt (c / Real.sqrt 2)) := by
    refine mul_le_mul_of_nonneg_left htail ?_
    positivity
  refine le_trans hmono (le_trans hprod ?_)
  -- the final numeric collapse
  have hval : Real.sqrt (c / Real.sqrt 2) = Real.sqrt c / Real.sqrt (Real.sqrt 2) :=
    Real.sqrt_div' _ (Real.sqrt_nonneg 2)
  rw [hval, div_div_eq_mul_div, div_mul_div_comm]
  have hA43 : Real.sqrt (Real.sqrt 2) ≤ 4 / 3 := by
    have h2 : Real.sqrt 2 ≤ 16 / 9 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    have h := Real.sqrt_le_sqrt h2
    have h169 : Real.sqrt (16 / 9 : ℝ) = 4 / 3 := by
      rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h169] at h
  have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 2 * (3 * Real.sqrt (Real.sqrt 2)) * (c * k)
      ≤ 2 * (3 * (4 / 3)) * (c * k) := by
        have : (0 : ℝ) < c * k := by positivity
        nlinarith [hA43, this]
    _ = 8 * (k * Real.sqrt c * Real.sqrt c) := by
        linear_combination (-(8 * k)) * hcc

/-! ## The endpoint layer -/

theorem continuousOn_ampFourthRoot {s k : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) :
    ContinuousOn (ampFourthRoot s k) (Ioi 1) :=
  fun _ hx => ((hasDerivAt_ampFourthRoot hs1 hk hx).continuousAt).continuousWithinAt

/-- **The endpoint bound on the amplitude.**  Near the endpoint the amplitude has the exact
`(x-1)^{-1/4}` singularity, with the far factors contributing `k^{-1}`. -/
theorem ampFourthRoot_le_endpoint {s k x : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hx : 1 < x) :
    ampFourthRoot s k x ≤ Real.sqrt (Real.sqrt 2) / k * (x - 1) ^ (-(1 : ℝ) / 4) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hsub : (0 : ℝ) < x - 1 := by linarith
  have hx1 : (1 : ℝ) < x ^ 2 := by nlinarith
  -- the polynomial is at least (x-1) k⁴ / 2
  have hW : (x - 1) * k ^ 4 / 2 ≤ ampPoly s k x := by
    rw [ampPoly]
    have h1 : 2 * (x - 1) ≤ x ^ 2 - 1 := by nlinarith
    have h2 : (1 : ℝ) / 2 ≤ x ^ 2 - s := by linarith
    have h3 : (3 : ℝ) / 4 * k ^ 2 ≤ k ^ 2 * x ^ 2 - 1 := by nlinarith
    have h4 : (7 : ℝ) / 8 * k ^ 2 ≤ k ^ 2 * x ^ 2 - s := by nlinarith
    have hstep1 : 2 * (x - 1) * (1 / 2) ≤ (x ^ 2 - 1) * (x ^ 2 - s) :=
      mul_le_mul h1 h2 (by norm_num) (by linarith)
    have hstep2 : (3 : ℝ) / 4 * k ^ 2 * (7 / 8 * k ^ 2)
        ≤ (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) :=
      mul_le_mul h3 h4 (by positivity) (by linarith)
    have hprod : (2 * (x - 1) * (1 / 2)) * (3 / 4 * k ^ 2 * (7 / 8 * k ^ 2))
        ≤ ((x ^ 2 - 1) * (x ^ 2 - s)) * ((k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s)) :=
      mul_le_mul hstep1 hstep2 (by positivity) (by linarith [hstep1, hsub])
    calc (x - 1) * k ^ 4 / 2 ≤ (2 * (x - 1) * (1 / 2)) * (3 / 4 * k ^ 2 * (7 / 8 * k ^ 2)) := by
          nlinarith [mul_nonneg hsub.le (by positivity : (0:ℝ) ≤ k ^ 4)]
      _ ≤ ((x ^ 2 - 1) * (x ^ 2 - s)) * ((k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s)) := hprod
      _ = (x ^ 2 - 1) * (x ^ 2 - s) * (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) := by ring
  -- pass to the fourth root
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs22 : (0 : ℝ) < Real.sqrt (Real.sqrt 2) := Real.sqrt_pos.mpr hs2
  have hq : (0 : ℝ) < Real.sqrt (Real.sqrt (x - 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hsub)
  have hWpos : (0 : ℝ) < ampPoly s k x := ampPoly_pos hs1 hk hx
  have hlow : k * Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt (Real.sqrt 2)
      ≤ Real.sqrt (Real.sqrt (ampPoly s k x)) := by
    have hstep : Real.sqrt (Real.sqrt ((x - 1) * k ^ 4 / 2))
        ≤ Real.sqrt (Real.sqrt (ampPoly s k x)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hW)
    have hval : Real.sqrt (Real.sqrt ((x - 1) * k ^ 4 / 2))
        = k * Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt (Real.sqrt 2) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div' _ (Real.sqrt_nonneg 2),
        Real.sqrt_mul hsub.le, Real.sqrt_mul (Real.sqrt_nonneg _)]
      rw [show Real.sqrt (k ^ 4) = k ^ 2 from by
        rw [show k ^ 4 = (k ^ 2) ^ 2 from by ring, Real.sqrt_sq (by positivity)]]
      rw [show Real.sqrt (k ^ 2) = k from Real.sqrt_sq hk0.le]
      ring
    rw [hval] at hstep
    exact hstep
  have hquarter : (x - 1) ^ (-(1 : ℝ) / 4) = 1 / Real.sqrt (Real.sqrt (x - 1)) :=
    rpow_neg_quarter hsub
  rw [ampFourthRoot, hquarter]
  have hpos : (0 : ℝ) < k * Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt (Real.sqrt 2) := by
    positivity
  calc 1 / Real.sqrt (Real.sqrt (ampPoly s k x))
      ≤ 1 / (k * Real.sqrt (Real.sqrt (x - 1)) / Real.sqrt (Real.sqrt 2)) :=
        one_div_le_one_div_of_le hpos hlow
    _ = Real.sqrt (Real.sqrt 2) / k * (1 / Real.sqrt (Real.sqrt (x - 1))) := by
        rw [one_div_div]
        ring

/-- The exact endpoint mass of the fractional power at an arbitrary upper limit. -/
theorem integral_Ioc_rpow_sub_one_gen {X : ℝ} (hX : 1 ≤ X) :
    (∫ x in Ioc (1 : ℝ) X, (x - 1) ^ (-(1 : ℝ) / 4)) = 4 / 3 * (X - 1) ^ ((3 : ℝ) / 4) := by
  have h := intervalIntegral.integral_comp_sub_right
    (fun t : ℝ => t ^ (-(1 : ℝ) / 4)) 1 (a := 1) (b := X)
  have hval : (∫ x in (0 : ℝ)..(X - 1), x ^ (-(1 : ℝ) / 4))
      = 4 / 3 * (X - 1) ^ ((3 : ℝ) / 4) := by
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [show -(1 : ℝ) / 4 + 1 = (3 : ℝ) / 4 from by ring,
      Real.zero_rpow (by norm_num : (3 : ℝ) / 4 ≠ 0)]
    ring
  rw [← intervalIntegral.integral_of_le hX, h]
  norm_num at hval ⊢
  exact hval

theorem integrableOn_ampFourthRoot {s k X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hX : 1 ≤ X) : IntegrableOn (ampFourthRoot s k) (Ioc 1 X) volume := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hrpow : IntegrableOn (fun x : ℝ => (x - 1) ^ (-(1 : ℝ) / 4)) (Ioc 1 X) volume := by
    have h := intervalIntegrable_rpow_sub_one_gen (r := -(1 : ℝ) / 4) (by norm_num) (x := X)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX] at h
    exact h
  have hcomp : IntegrableOn
      (fun x : ℝ => Real.sqrt (Real.sqrt 2) / k * (x - 1) ^ (-(1 : ℝ) / 4)) (Ioc 1 X) volume :=
    hrpow.const_mul _
  have hmeas : AEStronglyMeasurable (ampFourthRoot s k) (volume.restrict (Ioc 1 X)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_ampFourthRoot hs1 hk).mono (fun x hx => hx.1)
  refine MeasureTheory.Integrable.mono' hcomp hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ampFourthRoot_pos hs1 hk hx.1).le]
  exact ampFourthRoot_le_endpoint hs0 hs1 hk hx.1

/-- **Equation (12), the endpoint layer.**  The amplitude is integrable up to the endpoint and its mass
on `[1, X]` is `O(k^{-1}(X-1)^{3/4})`.  At the Bessel endpoint scale `X - 1 = c^{-2}` this is
`O(c^{-3/2} k^{-1})`, which is below the window contribution whenever `k <= c`. -/
theorem integral_Ioc_ampFourthRoot_le {s k X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hX : 1 ≤ X) :
    (∫ x in Ioc (1 : ℝ) X, ampFourthRoot s k x)
      ≤ 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (X - 1) ^ ((3 : ℝ) / 4) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hs22 : (0 : ℝ) < Real.sqrt (Real.sqrt 2) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hrpow : IntegrableOn (fun x : ℝ => (x - 1) ^ (-(1 : ℝ) / 4)) (Ioc 1 X) volume := by
    have h := intervalIntegrable_rpow_sub_one_gen (r := -(1 : ℝ) / 4) (by norm_num) (x := X)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX] at h
    exact h
  have hcomp : IntegrableOn
      (fun x : ℝ => Real.sqrt (Real.sqrt 2) / k * (x - 1) ^ (-(1 : ℝ) / 4)) (Ioc 1 X) volume :=
    hrpow.const_mul _
  have hmeas : AEStronglyMeasurable (ampFourthRoot s k) (volume.restrict (Ioc 1 X)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_ampFourthRoot hs1 hk).mono (fun x hx => hx.1)
  have hamp : IntegrableOn (ampFourthRoot s k) (Ioc 1 X) volume :=
    integrableOn_ampFourthRoot hs0 hs1 hk hX
  have hmono : (∫ x in Ioc (1 : ℝ) X, ampFourthRoot s k x)
      ≤ ∫ x in Ioc (1 : ℝ) X, Real.sqrt (Real.sqrt 2) / k * (x - 1) ^ (-(1 : ℝ) / 4) := by
    refine MeasureTheory.setIntegral_mono_on hamp hcomp measurableSet_Ioc fun x hx => ?_
    exact ampFourthRoot_le_endpoint hs0 hs1 hk hx.1
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_sub_one_gen hX]
  rw [show Real.sqrt (Real.sqrt 2) / k * (4 / 3 * (X - 1) ^ ((3 : ℝ) / 4))
      = 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (X - 1) ^ ((3 : ℝ) / 4) from by ring]

/-! ## The real oscillatory integral -/

/-- The real cosine integral is dominated by the complex oscillatory integral, for either sign of the
phase.  This is what lets the three block estimates — which carry the phase sign their van der Corput
test demands — all bound the same real quantity. -/
theorem abs_integral_mul_cos_le_norm {w g : ℝ → ℝ} {a b : ℝ}
    (hint : IntervalIntegrable
      (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * Complex.I)) volume a b) :
    |∫ x in a..b, w x * Real.cos (g x)|
      ≤ ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * Complex.I)‖ := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (Complex.reCLM) hint
  rw [Complex.reCLM_apply] at h
  have hcongr : (∫ x in a..b, w x * Real.cos (g x))
      = ∫ x in a..b, Complex.reCLM ((w x : ℂ) * Complex.exp ((g x : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [Complex.reCLM_apply, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcongr, h]
  exact Complex.abs_re_le_norm _

theorem continuousOn_xiDiffPhase {s k : ℝ} (hs0 : 0 ≤ s) (hk : 2 ≤ k) :
    ContinuousOn (xiDiffPhase s k) (Ioi 1) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hkx : (1 : ℝ) < k * x := by nlinarith
  exact ((hasDerivAt_xiDiffPhase hs0 hx1 hkx).continuousAt).continuousWithinAt

/-- The complex integrand of a block is interval integrable: both factors are continuous on the open
ray, and every block sits inside it. -/
theorem intervalIntegrable_ampCexp {s c k a b : ℝ} (hs1 : s ≤ 1 / 2) (hs0 : 0 ≤ s) (hk : 2 ≤ k)
    (hab : a ≤ b) (ha : 1 < a) (σ : ℝ) :
    IntervalIntegrable
      (fun x => (ampFourthRoot s k x : ℂ)
        * Complex.exp (((σ * (c * xiDiffPhase s k x) : ℝ) : ℂ) * Complex.I)) volume a b := by
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  refine ContinuousOn.intervalIntegrable ?_
  have hamp : ContinuousOn (fun x : ℝ => (ampFourthRoot s k x : ℂ)) (uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_ampFourthRoot hs1 hk).mono hsub))
  have hph : ContinuousOn (fun x : ℝ => ((σ * (c * xiDiffPhase s k x) : ℝ) : ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))
  exact hamp.mul (Complex.continuous_exp.comp_continuousOn (hph.mul continuousOn_const))

/-! ## The four-way assembly -/

private theorem le_of_sq_le_sq_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  have hs := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hs

private theorem rpow_three_quarter_inv_sq {c : ℝ} (hc : 0 < c) :
    ((1 : ℝ) / c ^ 2) ^ ((3 : ℝ) / 4) = 1 / (c * Real.sqrt c) := by
  have h2 : (1 : ℝ) / c ^ 2 = c ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hc.le, ← Real.rpow_natCast c 2]
    norm_num
  rw [h2, ← Real.rpow_mul hc.le,
    show -(2 : ℝ) * ((3 : ℝ) / 4) = -((3 : ℝ) / 2) from by ring, Real.rpow_neg hc.le,
    show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring, Real.rpow_add hc, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

private theorem rpow_neg_quarter_inv_sq {c : ℝ} (hc : 0 < c) :
    ((1 : ℝ) / c ^ 2) ^ (-(1 : ℝ) / 4) = Real.sqrt c := by
  have h2 : (1 : ℝ) / c ^ 2 = c ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hc.le, ← Real.rpow_natCast c 2]
    norm_num
  rw [h2, ← Real.rpow_mul hc.le,
    show -(2 : ℝ) * (-(1 : ℝ) / 4) = (1 : ℝ) / 2 from by ring, ← Real.sqrt_eq_rpow]

theorem sqrt_sqrt_two_le : Real.sqrt (Real.sqrt 2) ≤ 6 / 5 := by
  have h2 : Real.sqrt 2 ≤ 36 / 25 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have h := Real.sqrt_le_sqrt h2
  have hval : Real.sqrt (36 / 25 : ℝ) = 6 / 5 := by
    rw [show (36 / 25 : ℝ) = (6 / 5) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [hval] at h

/-- **The four-block assembly.**  Given the endpoint cut `E` and the two window edges `A`, `B`, the
leading Bessel term of the first-row entry is bounded by the sum of the four block estimates: the
endpoint layer `(12)`, the inner block, the window block and the outer block.  No arithmetic between
the four is performed here — that is the content of the corollary below. -/
theorem abs_integral_firstRow_leading_le_of_cuts {s c k E A B R : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 2 ≤ k) (hc0 : 0 < c) (hEgt : 1 < E) (hEA : E ≤ A) (hAB : A ≤ B) (hBR : B ≤ R)
    (hA1 : 1 < A) (hAsq : A ^ 2 = 1 + 1 / (4 * k ^ 2)) (hBsq : B ^ 2 = 1 + 2 / k ^ 2) :
    |∫ x in (1 : ℝ)..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (E - 1) ^ ((3 : ℝ) / 4)
        + 20 * ampFourthRoot s k E / (c * k)
        + 80 / (Real.sqrt c * k ^ 2)
        + 64 / (c * k * Real.sqrt k) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have h1E : (1 : ℝ) ≤ E := hEgt.le
  have h1A : (1 : ℝ) ≤ A := hA1.le
  have hB1 : (1 : ℝ) < B := lt_of_lt_of_le hA1 hAB
  have h1B : (1 : ℝ) ≤ B := hB1.le
  have h1R : (1 : ℝ) ≤ R := le_trans h1B hBR
  -- every piece is integrable
  have hint : ∀ p q : ℝ, 1 ≤ p → p ≤ q →
      IntervalIntegrable (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        volume p q := by
    intro p q hp hpq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    have hbig : IntegrableOn (ampFourthRoot s k) (Ioc 1 q) volume :=
      integrableOn_ampFourthRoot hs0 hs1 hk (le_trans hp hpq)
    have hsub : Ioc p q ⊆ Ioi 1 := fun x hx => lt_of_le_of_lt hp hx.1
    have hdom : IntegrableOn (ampFourthRoot s k) (Ioc p q) volume :=
      hbig.mono_set (fun x hx => ⟨lt_of_le_of_lt hp hx.1, hx.2⟩)
    have hmeas : AEStronglyMeasurable
        (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        (volume.restrict (Ioc p q)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact ((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
        (Real.continuous_cos.comp_continuousOn
          (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))
    refine MeasureTheory.Integrable.mono' hdom hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : (1 : ℝ) < x := lt_of_le_of_lt hp hx.1
    have hamppos := (ampFourthRoot_pos hs1 hk hx1).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hamppos]
    nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x), hamppos]
  -- the split
  have hsp1 := intervalIntegral.integral_add_adjacent_intervals (hint 1 E le_rfl h1E)
    (hint E A h1E hEA)
  have hsp2 := intervalIntegral.integral_add_adjacent_intervals (hint 1 A le_rfl h1A)
    (hint A B h1A hAB)
  have hsp3 := intervalIntegral.integral_add_adjacent_intervals (hint 1 B le_rfl h1B)
    (hint B R h1B hBR)
  -- piece 1: the endpoint layer
  have hP1 : |∫ x in (1 : ℝ)..E, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (E - 1) ^ ((3 : ℝ) / 4) := by
    have hIab : IntegrableOn
        (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) (Ioc 1 E) volume := by
      have h := hint 1 E le_rfl h1E
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h1E] at h
    have hnorm : ‖∫ x in Ioc (1 : ℝ) E,
          ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)‖
        ≤ ∫ x in Ioc (1 : ℝ) E, ‖ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hmono : (∫ x in Ioc (1 : ℝ) E,
          ‖ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)‖)
        ≤ ∫ x in Ioc (1 : ℝ) E, ampFourthRoot s k x := by
      refine MeasureTheory.setIntegral_mono_on hIab.norm
        (integrableOn_ampFourthRoot hs0 hs1 hk h1E) measurableSet_Ioc fun x hx => ?_
      have hamppos := (ampFourthRoot_pos hs1 hk hx.1).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hamppos]
      nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x), hamppos]
    have hend := integral_Ioc_ampFourthRoot_le (s := s) (k := k) (X := E) hs0 hs1 hk h1E
    rw [intervalIntegral.integral_of_le h1E, ← Real.norm_eq_abs]
    linarith
  -- piece 2: the inner block
  have hP2 : |∫ x in E..A, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 20 * ampFourthRoot s k E / (c * k) := by
    have hin : ∀ x ∈ uIcc E A, x ^ 2 - 1 ≤ 1 / (4 * k ^ 2) := by
      intro x hx
      rw [uIcc_of_le hEA] at hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (lt_of_lt_of_le hEgt hx.1)
      have hle : x ^ 2 ≤ A ^ 2 := by nlinarith [hx.2]
      rw [hAsq] at hle
      linarith
    have hblock := norm_integral_inner_block_le (s := s) (c := c) (k := k) (a := E) (b := A)
      hs0 hs1 hk hc0 hEA hEgt hin
    refine le_trans (abs_integral_mul_cos_le_norm
      (w := ampFourthRoot s k) (g := fun x => c * xiDiffPhase s k x) (a := E) (b := A) ?_) hblock
    have h := intervalIntegrable_ampCexp (s := s) (c := c) (k := k) (a := E) (b := A)
      hs1 hs0 hk hEA hEgt 1
    simpa using h
  -- piece 3: the window block
  have hP3 : |∫ x in A..B, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 80 / (Real.sqrt c * k ^ 2) := by
    have hwin : ∀ x ∈ uIcc A B, 1 / (4 * k ^ 2) ≤ x ^ 2 - 1 ∧ x ^ 2 - 1 ≤ 2 / k ^ 2 := by
      intro x hx
      rw [uIcc_of_le hAB] at hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (lt_of_lt_of_le hA1 hx.1)
      have hlo : A ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
      have hhi : x ^ 2 ≤ B ^ 2 := by nlinarith [hx.2]
      rw [hAsq] at hlo
      rw [hBsq] at hhi
      exact ⟨by linarith, by linarith⟩
    have hblock := norm_integral_window_block_le (s := s) (c := c) (k := k) (a := A) (b := B)
      hs0 hs1 hk hc0 hAB hA1 hwin
    have hcongr : (∫ x in A..B, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        = ∫ x in A..B, ampFourthRoot s k x * Real.cos (-(c * xiDiffPhase s k x)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [Real.cos_neg]
    rw [hcongr]
    refine le_trans (abs_integral_mul_cos_le_norm
      (w := ampFourthRoot s k) (g := fun x => -(c * xiDiffPhase s k x)) (a := A) (b := B) ?_) hblock
    have h := intervalIntegrable_ampCexp (s := s) (c := c) (k := k) (a := A) (b := B)
      hs1 hs0 hk hAB hA1 (-1)
    simpa using h
  -- piece 4: the outer block
  have hP4 : |∫ x in B..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 64 / (c * k * Real.sqrt k) := by
    have hout : ∀ x ∈ uIcc B R, 2 / k ^ 2 ≤ x ^ 2 - 1 := by
      intro x hx
      rw [uIcc_of_le hBR] at hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (lt_of_lt_of_le hB1 hx.1)
      have hlo : B ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
      rw [hBsq] at hlo
      linarith
    have hblock := norm_integral_outer_block_le (s := s) (c := c) (k := k) (a := B) (b := R)
      hs0 hs1 hk hc0 hBR hB1 hout
    have hcongr : (∫ x in B..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        = ∫ x in B..R, ampFourthRoot s k x * Real.cos (-(c * xiDiffPhase s k x)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [Real.cos_neg]
    rw [hcongr]
    refine le_trans (abs_integral_mul_cos_le_norm
      (w := ampFourthRoot s k) (g := fun x => -(c * xiDiffPhase s k x)) (a := B) (b := R) ?_) hblock
    have h := intervalIntegrable_ampCexp (s := s) (c := c) (k := k) (a := B) (b := R)
      hs1 hs0 hk hBR hB1 (-1)
    simpa using h
  -- add up
  have hsplit : (∫ x in (1 : ℝ)..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
      = (∫ x in (1 : ℝ)..E, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        + (∫ x in E..A, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        + (∫ x in A..B, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
        + ∫ x in B..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
    rw [← hsp3, ← hsp2, ← hsp1]
  rw [hsplit]
  have h123 := abs_add_three
    ((∫ x in (1 : ℝ)..E, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
      + ∫ x in E..A, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
    (∫ x in A..B, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
    (∫ x in B..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
  have h12 := abs_add_le
    (∫ x in (1 : ℝ)..E, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
    (∫ x in E..A, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
  linarith [h123, h12, hP1, hP2, hP3, hP4]

/-! ### The numeric comparisons of the four blocks -/

private theorem endpoint_cut_le {c k : ℝ} (hk : 2 ≤ k) (hkc : 3 * k ≤ c) :
    1 + 1 / c ^ 2 ≤ Real.sqrt (1 + 1 / (4 * k ^ 2)) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hApos : (0 : ℝ) < Real.sqrt (1 + 1 / (4 * k ^ 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hAsq : Real.sqrt (1 + 1 / (4 * k ^ 2)) ^ 2 = 1 + 1 / (4 * k ^ 2) :=
    Real.sq_sqrt (by positivity)
  refine le_of_sq_le_sq_aux (by positivity) hApos.le ?_
  rw [hAsq, show (1 + 1 / c ^ 2 : ℝ) ^ 2 = 1 + 2 / c ^ 2 + (1 / c ^ 2) ^ 2 from by ring]
  have hkc2 : (9 : ℝ) * k ^ 2 ≤ c ^ 2 := by nlinarith
  have hc2 : (36 : ℝ) ≤ c ^ 2 := by nlinarith
  have h1 : (2 : ℝ) / c ^ 2 ≤ 2 / (9 * k ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkc2]
  have h2 : ((1 : ℝ) / c ^ 2) ^ 2 ≤ 1 / (324 * k ^ 2) := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkc2, hc2]
  have h3 : (2 : ℝ) / (9 * k ^ 2) + 1 / (324 * k ^ 2) ≤ 1 / (4 * k ^ 2) := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hksq, sq_nonneg k]
  linarith

private theorem endpoint_term_le {c k : ℝ} (hk : 2 ≤ k) (hkc : 3 * k ≤ c) :
    4 / 3 * Real.sqrt (Real.sqrt 2) / k * (1 / (c * Real.sqrt c))
      ≤ 3 / 5 / (Real.sqrt c * k ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hs22 : Real.sqrt (Real.sqrt 2) ≤ 6 / 5 := sqrt_sqrt_two_le
  have hLHS : 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (1 / (c * Real.sqrt c))
      = 4 / 3 * Real.sqrt (Real.sqrt 2) / (k * (c * Real.sqrt c)) := by field_simp
  rw [hLHS, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 4 / 3 * Real.sqrt (Real.sqrt 2) * (Real.sqrt c * k ^ 2)
      ≤ 8 / 5 * (Real.sqrt c * k ^ 2) := by
        nlinarith [hs22, mul_nonneg hcs.le (sq_nonneg k)]
    _ ≤ 3 / 5 * (k * ((3 * k) * Real.sqrt c)) := by
        linarith [mul_nonneg hcs.le (sq_nonneg k)]
    _ ≤ 3 / 5 * (k * (c * Real.sqrt c)) := by
        linarith [mul_le_mul_of_nonneg_left hkc
          (by positivity : (0 : ℝ) ≤ 3 / 5 * k * Real.sqrt c)]

private theorem inner_term_le {c k w : ℝ} (hk : 2 ≤ k) (hc : 6 ≤ c) (_hw0 : 0 ≤ w)
    (hw : w ≤ Real.sqrt (Real.sqrt 2) / k * Real.sqrt c) :
    20 * w / (c * k) ≤ 24 / (Real.sqrt c * k ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hkne : k ≠ 0 := hk0.ne'
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hcssq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hs22 : Real.sqrt (Real.sqrt 2) ≤ 6 / 5 := sqrt_sqrt_two_le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 20 * w * (Real.sqrt c * k ^ 2)
      ≤ 20 * (Real.sqrt (Real.sqrt 2) / k * Real.sqrt c) * (Real.sqrt c * k ^ 2) := by
        nlinarith [hw, mul_nonneg hcs.le (sq_nonneg k)]
    _ = 20 * Real.sqrt (Real.sqrt 2) * (c * k) := by
        rw [show 20 * (Real.sqrt (Real.sqrt 2) / k * Real.sqrt c) * (Real.sqrt c * k ^ 2)
            = 20 * Real.sqrt (Real.sqrt 2) * (Real.sqrt c * Real.sqrt c) * (k ^ 2 / k) from by
              ring, hcssq, show k ^ 2 / k = k from by field_simp]
        ring
    _ ≤ 24 * (c * k) := by
        nlinarith [hs22, mul_nonneg hc0.le hk0.le]

private theorem outer_term_le {c k : ℝ} (hk : 2 ≤ k) (hkc : 3 * k ≤ c) :
    64 / (c * k * Real.sqrt k) ≤ 64 / (Real.sqrt c * k ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hks : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hkssq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have hcssq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hsk : Real.sqrt k ≤ Real.sqrt c := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (64 : ℝ) * (Real.sqrt c * k ^ 2)
      = 64 * Real.sqrt c * k * (Real.sqrt k * Real.sqrt k) := by
        rw [hkssq]
        ring
    _ ≤ 64 * Real.sqrt c * k * (Real.sqrt c * Real.sqrt k) := by
        linarith [mul_le_mul_of_nonneg_left hsk
          (by positivity : (0 : ℝ) ≤ 64 * Real.sqrt c * k * Real.sqrt k)]
    _ = 64 * (c * k * Real.sqrt k) := by
        rw [show 64 * Real.sqrt c * k * (Real.sqrt c * Real.sqrt k)
            = 64 * (Real.sqrt c * Real.sqrt c) * (k * Real.sqrt k) from by ring, hcssq]
        ring

private theorem four_terms_sum_le {c k : ℝ} (hk : 2 ≤ k) (hc : 6 ≤ c) :
    3 / 5 / (Real.sqrt c * k ^ 2) + 24 / (Real.sqrt c * k ^ 2)
      + 80 / (Real.sqrt c * k ^ 2) + 64 / (Real.sqrt c * k ^ 2)
      ≤ 170 / (Real.sqrt c * k ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hD : (0 : ℝ) < Real.sqrt c * k ^ 2 := by positivity
  calc 3 / 5 / (Real.sqrt c * k ^ 2) + 24 / (Real.sqrt c * k ^ 2)
        + 80 / (Real.sqrt c * k ^ 2) + 64 / (Real.sqrt c * k ^ 2)
      = (3 / 5 + 24 + 80 + 64) / (Real.sqrt c * k ^ 2) := by ring
    _ ≤ 170 / (Real.sqrt c * k ^ 2) := by
        rw [div_le_div_iff₀ hD hD]
        linarith [hD.le]

/-- **Equation (13).**  The leading Bessel term of the exceptional first-row entry obeys the sharp
bound

```text
|int_1^R amp(x) cos(c phi_(s,k)(x)) dx| <= 170 / (sqrt c * k²)
```

for every `R` beyond the stationary window, every `k >= 2` and every aperture with `3k <= c`, which the
card's range `k <= c/(2 pi)` implies.  The four contributions are `O(c^{-3/2}k^{-1})` (endpoint layer),
`O(c^{-1/2}k^{-2})` (inner block), `O(c^{-1/2}k^{-2})` (window block) and `O(c^{-1}k^{-3/2})` (outer
block); the aperture hypothesis is exactly what puts the first and the last below the middle two. -/
theorem abs_integral_firstRow_leading_le {s c k R : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hkc : 3 * k ≤ c) (hR : Real.sqrt (1 + 2 / k ^ 2) ≤ R) :
    |∫ x in (1 : ℝ)..R, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
      ≤ 170 / (Real.sqrt c * k ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hc : (6 : ℝ) ≤ c := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hEgt : (1 : ℝ) < 1 + 1 / c ^ 2 := by
    have : (0 : ℝ) < 1 / c ^ 2 := by positivity
    linarith
  have hE1 : (1 + 1 / c ^ 2 : ℝ) - 1 = 1 / c ^ 2 := by ring
  have hAsq : Real.sqrt (1 + 1 / (4 * k ^ 2)) ^ 2 = 1 + 1 / (4 * k ^ 2) :=
    Real.sq_sqrt (by positivity)
  have hBsq : Real.sqrt (1 + 2 / k ^ 2) ^ 2 = 1 + 2 / k ^ 2 := Real.sq_sqrt (by positivity)
  have hA1 : (1 : ℝ) < Real.sqrt (1 + 1 / (4 * k ^ 2)) := by
    refine (Real.lt_sqrt (by norm_num)).mpr ?_
    have : (0 : ℝ) < 1 / (4 * k ^ 2) := by positivity
    nlinarith
  have hEA : 1 + 1 / c ^ 2 ≤ Real.sqrt (1 + 1 / (4 * k ^ 2)) := endpoint_cut_le hk hkc
  have hAB : Real.sqrt (1 + 1 / (4 * k ^ 2)) ≤ Real.sqrt (1 + 2 / k ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have : (1 : ℝ) / (4 * k ^ 2) ≤ 2 / k ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hmain := abs_integral_firstRow_leading_le_of_cuts (s := s) (c := c) (k := k)
    (E := 1 + 1 / c ^ 2) (A := Real.sqrt (1 + 1 / (4 * k ^ 2))) (B := Real.sqrt (1 + 2 / k ^ 2))
    (R := R) hs0 hs1 hk hc0 hEgt hEA hAB hR hA1 hAsq hBsq
  refine hmain.trans ?_
  have hQ1 : 4 / 3 * Real.sqrt (Real.sqrt 2) / k * ((1 + 1 / c ^ 2 : ℝ) - 1) ^ ((3 : ℝ) / 4)
      ≤ 3 / 5 / (Real.sqrt c * k ^ 2) := by
    rw [hE1, rpow_three_quarter_inv_sq hc0]
    exact endpoint_term_le hk hkc
  have hQ2 : 20 * ampFourthRoot s k (1 + 1 / c ^ 2) / (c * k)
      ≤ 24 / (Real.sqrt c * k ^ 2) := by
    have hampE : ampFourthRoot s k (1 + 1 / c ^ 2)
        ≤ Real.sqrt (Real.sqrt 2) / k * Real.sqrt c := by
      have h := ampFourthRoot_le_endpoint (s := s) (k := k) (x := 1 + 1 / c ^ 2) hs0 hs1 hk hEgt
      rwa [hE1, rpow_neg_quarter_inv_sq hc0] at h
    exact inner_term_le hk hc (ampFourthRoot_pos hs1 hk hEgt).le hampE
  have hQ4 : 64 / (c * k * Real.sqrt k) ≤ 64 / (Real.sqrt c * k ^ 2) := outer_term_le hk hkc
  have hsum := four_terms_sum_le (c := c) (k := k) hk hc
  linarith [hQ1, hQ2, hQ4, hsum]

end GaloisForLFunctions.RHTower

end
