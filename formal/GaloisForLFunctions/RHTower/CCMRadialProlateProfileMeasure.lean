import GaloisForLFunctions.RHTower.CCMRadialProlateEndpointLayer

/-!
# The limiting radial profile measure of the constrained source

The weak limit of the squared exterior radial profile of the constrained CCM source is the measure

```text
dx / (pi x sqrt(x² - 1))     on (1, ∞),
```

and the arithmetic that makes the limit a *probability-like* statement is that this density has total mass
exactly `1/2`.  That is an elementary but exact computation: the density is the derivative of

```text
theta(x) = arctan(sqrt(x² - 1)) = arccos(1/x),
```

the radial angle, which runs from `0` at the band edge to `pi/2` at radial infinity.  So the mass is
`(1/pi)(pi/2) = 1/2`, with no asymptotics involved.

The same angle is the phase marking of the fixed-degree radial expansion, where the degree enters only
through `-(2n+1) theta(x)/2`; both uses are served by the single derivative law proved here.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## The radial angle -/

/-- The radial angle `theta(x) = arctan(sqrt(x²-1))`, equal to `arccos(1/x)` on the ray. -/
def radialAngle (x : ℝ) : ℝ := Real.arctan (Real.sqrt (x ^ 2 - 1))

theorem radialAngle_one : radialAngle 1 = 0 := by
  rw [radialAngle]
  norm_num

theorem continuous_radialAngle : Continuous radialAngle := by
  have h : Continuous fun x : ℝ => Real.sqrt (x ^ 2 - 1) :=
    Real.continuous_sqrt.comp (by fun_prop)
  exact Real.continuous_arctan.comp h

/-- The derivative of the radial angle is the limiting profile density up to the factor `pi`. -/
theorem hasDerivAt_radialAngle {x : ℝ} (hx : 1 < x) :
    HasDerivAt radialAngle (1 / (x * Real.sqrt (x ^ 2 - 1))) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hd.le
  have hw : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1)) (x / Real.sqrt (x ^ 2 - 1)) x := by
    have h := hasDerivAt_nfWeight hx
    have hfun : nfWeight = fun t : ℝ => Real.sqrt (t ^ 2 - 1) := by
      funext t
      rw [nfWeight]
    rw [hfun, nfWeightDeriv] at h
    exact h
  have h := hw.arctan
  have hval : 1 / (1 + Real.sqrt (x ^ 2 - 1) ^ 2) * (x / Real.sqrt (x ^ 2 - 1))
      = 1 / (x * Real.sqrt (x ^ 2 - 1)) := by
    rw [hrsq]
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [show (1 : ℝ) + (x ^ 2 - 1) = x ^ 2 by ring]
    field_simp
  have hfun : radialAngle = fun t : ℝ => Real.arctan (Real.sqrt (t ^ 2 - 1)) := by
    funext t
    rw [radialAngle]
  rw [hfun, ← hval]
  exact h

theorem tendsto_radialAngle_atTop :
    Filter.Tendsto radialAngle Filter.atTop (nhds (Real.pi / 2)) := by
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2 - 1) Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ)
      (Filter.tendsto_pow_atTop (n := 2) (by norm_num))
    simpa [sub_eq_add_neg] using h
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (x ^ 2 - 1)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hsq
  have harctan := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  exact harctan.comp hsqrt

/-! ## The limiting profile density and its total mass -/

/-- The limiting density `1/(pi x sqrt(x²-1))` of the squared radial profile. -/
def profileDensity (x : ℝ) : ℝ := 1 / (Real.pi * x * Real.sqrt (x ^ 2 - 1))

theorem profileDensity_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ profileDensity x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [profileDensity]
  positivity

theorem hasDerivAt_radialAngle_div_pi {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => radialAngle t / Real.pi) (profileDensity x) x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := (hasDerivAt_radialAngle hx).div_const Real.pi
  have hval : 1 / (x * Real.sqrt (x ^ 2 - 1)) / Real.pi = profileDensity x := by
    rw [profileDensity]
    field_simp
  rw [← hval]
  exact h

theorem continuousWithinAt_radialAngle_div_pi :
    ContinuousWithinAt (fun t : ℝ => radialAngle t / Real.pi) (Ici 1) 1 :=
  ((continuous_radialAngle.div_const Real.pi).continuousAt).continuousWithinAt

theorem tendsto_radialAngle_div_pi :
    Filter.Tendsto (fun t : ℝ => radialAngle t / Real.pi) Filter.atTop (nhds (1 / 2)) := by
  have hpi : (0 : ℝ) ≠ Real.pi := ne_of_lt Real.pi_pos
  have h := tendsto_radialAngle_atTop.div_const Real.pi
  have hval : Real.pi / 2 / Real.pi = 1 / 2 := by
    field_simp
  rwa [hval] at h

theorem integrableOn_profileDensity : IntegrableOn profileDensity (Ioi 1) volume :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg continuousWithinAt_radialAngle_div_pi
    (fun _ hx => hasDerivAt_radialAngle_div_pi hx)
    (fun _ hx => profileDensity_nonneg (le_of_lt hx)) tendsto_radialAngle_div_pi

/-- **The total mass of the limiting radial profile density is `1/2`.**  The density is the derivative of
`theta/pi` with `theta(1) = 0` and `theta(x) -> pi/2`, so no asymptotics enter: the mass is exactly the
angle swept from the band edge to radial infinity. -/
theorem integral_Ioi_profileDensity : (∫ x in Ioi (1 : ℝ), profileDensity x) = 1 / 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
    continuousWithinAt_radialAngle_div_pi
    (fun _ hx => hasDerivAt_radialAngle_div_pi hx)
    (fun _ hx => profileDensity_nonneg (le_of_lt hx)) tendsto_radialAngle_div_pi
  rw [h, radialAngle_one]
  norm_num


/-! ## The second-order expansion of the endpoint phase

The card's expansion `xi_sigma(x) = sqrt(x²-1) - sigma² theta(x)/2 + O(sigma⁴)` is exact at the level of
integrands: the two leading terms are the exact primitives of `t/sqrt(t²-1)` and `1/(t sqrt(t²-1))`, and the
remainder is the Taylor error of `sqrt(t² - s)` against `t - s/(2t)`, which is uniformly `s²/4`. -/

/-- The scalar Taylor bound behind the expansion: `sqrt(t²-s) = t - s/(2t) + O(s²)`, uniformly for `t >= 1`
and `0 <= s <= 1/2`.  The upper half is `(t - s/(2t))² >= t² - s`; the lower half squares to a polynomial
inequality that `t >= 1`, `s <= 1/2` settle. -/
theorem abs_sqrt_sq_sub_sub_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht : 1 ≤ t) :
    |Real.sqrt (t ^ 2 - s) - t + s / (2 * t)| ≤ s ^ 2 / 4 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hn : (0 : ℝ) < t ^ 2 - s := by nlinarith
  have hP0 : 0 ≤ Real.sqrt (t ^ 2 - s) := Real.sqrt_nonneg _
  have hPsq : Real.sqrt (t ^ 2 - s) ^ 2 = t ^ 2 - s := Real.sq_sqrt hn.le
  have hv0 : 0 ≤ s / (2 * t) := by positivity
  have hvs : s / (2 * t) ≤ s / 2 := div_le_div_of_nonneg_left hs0 (by norm_num) (by linarith)
  have hv4 : s / (2 * t) ≤ 1 / 4 := by linarith
  have hsqexp : (t - s / (2 * t)) ^ 2 = t ^ 2 - s + (s / (2 * t)) ^ 2 := by
    field_simp
    ring
  have hupper : Real.sqrt (t ^ 2 - s) ≤ t - s / (2 * t) := by
    have hA : 0 ≤ t - s / (2 * t) := by linarith
    calc Real.sqrt (t ^ 2 - s) ≤ Real.sqrt ((t - s / (2 * t)) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith [sq_nonneg (s / (2 * t))]
      _ = t - s / (2 * t) := Real.sqrt_sq hA
  have hlower : t - s / (2 * t) - s ^ 2 / 4 ≤ Real.sqrt (t ^ 2 - s) := by
    have hA : 0 ≤ t - s / (2 * t) - s ^ 2 / 4 := by nlinarith
    have hexp : (t - s / (2 * t) - s ^ 2 / 4) ^ 2
        = (t - s / (2 * t)) ^ 2 - 2 * (t - s / (2 * t)) * (s ^ 2 / 4) + (s ^ 2 / 4) ^ 2 := by
      ring
    calc t - s / (2 * t) - s ^ 2 / 4
        = Real.sqrt ((t - s / (2 * t) - s ^ 2 / 4) ^ 2) := (Real.sqrt_sq hA).symm
      _ ≤ Real.sqrt (t ^ 2 - s) := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith [hexp, hsqexp, hv0, hvs, hv4, sq_nonneg s, sq_nonneg (s ^ 2)]
  rw [abs_le]
  constructor <;> linarith

/-- The integrand form: the Liouville speed minus its two leading terms is `O(s²) (t²-1)^{-1/2}`. -/
theorem abs_xiSpeed_sub_second_order_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht : 1 < t) :
    |xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))|
      ≤ s ^ 2 / 4 * (1 / Real.sqrt (t ^ 2 - 1)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (t ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hmul : xiSpeed s t * (t ^ 2 - 1)
      = Real.sqrt (t ^ 2 - s) * Real.sqrt (t ^ 2 - 1) := xiSpeed_mul_sub_one hs1 ht
  have hrsq : Real.sqrt (t ^ 2 - 1) * Real.sqrt (t ^ 2 - 1) = t ^ 2 - 1 :=
    Real.mul_self_sqrt hd.le
  have hspeed : xiSpeed s t * Real.sqrt (t ^ 2 - 1) = Real.sqrt (t ^ 2 - s) := by
    have h : xiSpeed s t * Real.sqrt (t ^ 2 - 1) * Real.sqrt (t ^ 2 - 1)
        = Real.sqrt (t ^ 2 - s) * Real.sqrt (t ^ 2 - 1) := by
      rw [mul_assoc, hrsq]
      exact hmul
    exact mul_right_cancel₀ (ne_of_gt hr) h
  have hscalar := abs_sqrt_sq_sub_sub_le hs0 hs1 ht.le
  have e1 : t / Real.sqrt (t ^ 2 - 1) * Real.sqrt (t ^ 2 - 1) = t := by
    field_simp
  have e2 : s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))) * Real.sqrt (t ^ 2 - 1) = s / (2 * t) := by
    field_simp
  have hkey : (xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))))
      * Real.sqrt (t ^ 2 - 1) = Real.sqrt (t ^ 2 - s) - t + s / (2 * t) := by
    rw [xiCompSpeed]
    calc (xiSpeed s t - t / Real.sqrt (t ^ 2 - 1)
          + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))) * Real.sqrt (t ^ 2 - 1)
        = xiSpeed s t * Real.sqrt (t ^ 2 - 1)
          - t / Real.sqrt (t ^ 2 - 1) * Real.sqrt (t ^ 2 - 1)
          + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))) * Real.sqrt (t ^ 2 - 1) := by ring
      _ = Real.sqrt (t ^ 2 - s) - t + s / (2 * t) := by rw [hspeed, e1, e2]
  have habs : |xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))|
      * Real.sqrt (t ^ 2 - 1) ≤ s ^ 2 / 4 := by
    have h1 : |xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))|
          * |Real.sqrt (t ^ 2 - 1)|
        = |(xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))))
            * Real.sqrt (t ^ 2 - 1)| := (abs_mul _ _).symm
    rw [abs_of_pos hr] at h1
    rw [h1, hkey]
    exact hscalar
  rw [mul_one_div (s ^ 2 / 4) (Real.sqrt (t ^ 2 - 1)), le_div_iff₀ hr]
  exact habs

theorem intervalIntegrable_invMulSqrtSqSubOne {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / (t * Real.sqrt (t ^ 2 - 1))) volume 1 x := by
  have hmeas : Measurable fun t : ℝ => 1 / (t * Real.sqrt (t ^ 2 - 1)) := by fun_prop
  have hdom := intervalIntegrable_invSqrtSqSubOne hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx] at hdom ⊢
  refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, htx⟩ := ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (t ^ 2 - 1) := Real.sqrt_pos.mpr hd
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (t * Real.sqrt (t ^ 2 - 1)))]
  have hle : Real.sqrt (t ^ 2 - 1) ≤ t * Real.sqrt (t ^ 2 - 1) := by
    nlinarith [hr, ht1]
  exact one_div_le_one_div_of_le hr hle

/-- The radial angle is the exact primitive of `1/(t sqrt(t²-1))` from the band edge. -/
theorem integral_invMulSqrtSqSubOne {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, 1 / (t * Real.sqrt (t ^ 2 - 1))) = radialAngle x := by
  have hcont : ContinuousOn radialAngle (Set.Icc 1 x) := continuous_radialAngle.continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (1 : ℝ) x,
      HasDerivWithinAt radialAngle (1 / (t * Real.sqrt (t ^ 2 - 1))) (Set.Ioi t) t :=
    fun t ht => (hasDerivAt_radialAngle ht.1).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv
    (intervalIntegrable_invMulSqrtSqSubOne hx)
  rw [h, radialAngle_one, sub_zero]

/-- **The second-order expansion of the endpoint phase, with an explicit error.**  For `0 <= s <= 1/2` and
`x >= 1`,

```text
|xi_s(x) - (sqrt(x²-1) - (s/2) theta(x))| <= (s²/4) log(x + sqrt(x²-1)).
```

Both leading terms are exact primitives and the error is the integrated Taylor bound; with `s = sigma²` and
`s = O(1/c)` this is the card's `xi = sqrt(x²-1) - sigma² theta/2 + O(sigma⁴)`, uniformly on compacts. -/
theorem abs_xiEndpointPhase_sub_second_order_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 ≤ x) :
    |xiEndpointPhase s x - (Real.sqrt (x ^ 2 - 1) - s / 2 * radialAngle x)|
      ≤ s ^ 2 / 4 * GaloisForLFunctions.HTGeometry.endpointLog x := by
  have hint1 := intervalIntegrable_xiSpeed hs0 hx
  have hint2 := intervalIntegrable_xiCompSpeed hx
  have hint3 := (intervalIntegrable_invMulSqrtSqSubOne hx).const_mul (s / 2)
  have hintsum : IntervalIntegrable
      (fun t : ℝ => xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))))
      volume 1 x := (hint1.sub hint2).add hint3
  have hsplit : (∫ t in (1 : ℝ)..x,
        (xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))))
      = (∫ t in (1 : ℝ)..x, xiSpeed s t) - (∫ t in (1 : ℝ)..x, xiCompSpeed t)
        + s / 2 * ∫ t in (1 : ℝ)..x, 1 / (t * Real.sqrt (t ^ 2 - 1)) := by
    rw [intervalIntegral.integral_add (hint1.sub hint2) hint3,
      intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul]
  have hdiff : xiEndpointPhase s x - (Real.sqrt (x ^ 2 - 1) - s / 2 * radialAngle x)
      = ∫ t in (1 : ℝ)..x,
        (xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))) := by
    rw [hsplit, integral_xiCompSpeed hx, integral_invMulSqrtSqSubOne hx, xiEndpointPhase]
    ring
  rw [hdiff]
  have habs : |∫ t in (1 : ℝ)..x,
        (xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1))))|
      ≤ ∫ t in (1 : ℝ)..x,
        |xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))| := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t : ℝ => xiSpeed s t - xiCompSpeed t
        + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))) hx
    simpa [Real.norm_eq_abs] using h
  have hmono : (∫ t in (1 : ℝ)..x,
        |xiSpeed s t - xiCompSpeed t + s / 2 * (1 / (t * Real.sqrt (t ^ 2 - 1)))|)
      ≤ ∫ t in (1 : ℝ)..x, s ^ 2 / 4 * (1 / Real.sqrt (t ^ 2 - 1)) := by
    refine intervalIntegral.integral_mono_on hx hintsum.abs
      ((intervalIntegrable_invSqrtSqSubOne hx).const_mul _) ?_
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · have h0 : Real.sqrt (t ^ 2 - 1) = 0 := by
        rw [← h1]
        norm_num
      have hxi : xiSpeed s t = 0 := by
        rw [xiSpeed, ← h1]
        norm_num
      rw [hxi, xiCompSpeed, h0]
      norm_num
    · exact abs_xiSpeed_sub_second_order_le hs0 hs1 h1
  have hval : (∫ t in (1 : ℝ)..x, s ^ 2 / 4 * (1 / Real.sqrt (t ^ 2 - 1)))
      = s ^ 2 / 4 * GaloisForLFunctions.HTGeometry.endpointLog x := by
    rw [intervalIntegral.integral_const_mul, integral_invSqrtSqSubOne hx]
  linarith [habs, hmono, hval.le, hval.ge]


end GaloisForLFunctions.RHTower

end
