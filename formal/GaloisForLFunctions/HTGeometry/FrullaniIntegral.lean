import Mathlib

/-!
# The complex Frullani integral

For complex rates `a`, `b` in the open right half plane,

```
∫_0^∞ (exp (-a t) - exp (-b t)) / t dt = Log b - Log a.
```

This is the classical Frullani evaluation, proved here by writing the integrand as the `u`-integral
of `(b - a) exp (-(a + u (b - a)) t)` over the segment `[0,1]` and swapping the order of
integration; the segment from `a` to `b` stays in the right half plane, so the inner `t`-integral is
`(b - a) / (a + u (b - a))`, whose `u`-primitive is `Log (a + u (b - a))`.

The auxiliary evaluation `∫_0^∞ exp (-z t) dt = 1 / z` for `Re z > 0` is proved first and is useful
on its own: mathlib only provides the real-rate and Gamma-weighted versions.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

/-! ## The exponential integral with complex rate -/

theorem norm_cexp_neg_mul_ofReal (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(z * t))‖ = Real.exp (-(z.re * t)) := by
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re]

theorem continuous_cexp_neg_mul (z : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (-(z * t))) := by
  fun_prop

theorem integrableOn_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * t))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (g := fun t : ℝ => Real.exp (-z.re * t))
    (exp_neg_integrableOn_Ioi 0 hz)
    (continuous_cexp_neg_mul z).aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_cexp_neg_mul_ofReal]
  simp [neg_mul]

theorem hasDerivAt_cexp_neg_mul (z : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (-(z * r))) (Complex.exp (-(z * t)) * (-z)) t := by
  have hb : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun r : ℝ => -(z * (r : ℂ))) (-(z * 1)) t := (hb.const_mul z).neg
  simpa using h1.cexp

theorem integral_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) = 1 / z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  set f : ℝ → ℂ := fun t => -(Complex.exp (-(z * t)) / z) with hf
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (Complex.exp (-(z * t))) t := by
    intro t _
    have h := ((hasDerivAt_cexp_neg_mul z t).div_const z).neg
    refine h.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt f (Ici (0 : ℝ)) 0 :=
    (((continuous_cexp_neg_mul z).div_const z).neg).continuousWithinAt
  have htend : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj : Tendsto (fun t : ℝ => Real.exp (-(z.re * t)) / ‖z‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(z.re * t))) atTop (𝓝 0) := by
        have h2 : Tendsto (fun t : ℝ => -(z.re * t)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hz tendsto_id)
        exact Real.tendsto_exp_atBot.comp h2
      simpa using h1.div_const ‖z‖
    refine hmaj.congr ?_
    intro t
    rw [hf]
    simp [norm_cexp_neg_mul_ofReal]
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_cexp_neg_mul hz) htend
  rw [hval, hf]
  simp

/-! ## Frullani -/

section Frullani

variable {a b : ℂ}

/-- The point of the segment from `a` to `b` at parameter `u`. -/
def seg (a b : ℂ) (u : ℝ) : ℂ := a + (u : ℂ) * (b - a)

theorem seg_re (a b : ℂ) (u : ℝ) : (seg a b u).re = a.re + u * (b.re - a.re) := by
  simp [seg, Complex.add_re, Complex.mul_re, Complex.sub_re]

theorem seg_zero (a b : ℂ) : seg a b 0 = a := by simp [seg]

theorem seg_one (a b : ℂ) : seg a b 1 = b := by simp [seg]

theorem continuous_seg (a b : ℂ) : Continuous (seg a b) := by
  unfold seg; fun_prop

theorem min_re_le_seg_re (a b : ℂ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    min a.re b.re ≤ (seg a b u).re := by
  rw [seg_re]
  obtain ⟨hu0, hu1⟩ := hu
  rcases le_total a.re b.re with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem seg_re_pos (ha : 0 < a.re) (hb : 0 < b.re) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < (seg a b u).re :=
  lt_of_lt_of_le (lt_min ha hb) (min_re_le_seg_re a b hu)

theorem seg_ne_zero (ha : 0 < a.re) (hb : 0 < b.re) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seg a b u ≠ 0 := by
  intro h
  have hpos := seg_re_pos ha hb hu
  rw [h] at hpos
  simp at hpos

theorem seg_mem_slitPlane (ha : 0 < a.re) (hb : 0 < b.re) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : seg a b u ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (seg_re_pos ha hb hu))

/-- The Frullani integrand is the segment integral of the exponential family. -/
theorem intervalIntegral_seg_cexp (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..1, (b - a) * Complex.exp (-(seg a b u * t))) =
      (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hprim : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => -(Complex.exp (-(seg a b v * t)) / t))
        ((b - a) * Complex.exp (-(seg a b u * t))) u := by
    intro u _
    have hseg : HasDerivAt (fun v : ℝ => seg a b v) (b - a) u := by
      have hb' : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa [seg] using (hb'.mul_const (b - a)).const_add a
    have hmul : HasDerivAt (fun v : ℝ => -(seg a b v * (t : ℂ))) (-((b - a) * t)) u :=
      (hseg.mul_const (t : ℂ)).neg
    have h := (hmul.cexp.div_const (t : ℂ)).neg
    refine h.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => (b - a) * Complex.exp (-(seg a b u * t)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hs := continuous_seg a b
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hint, seg_zero, seg_one]
  field_simp
  ring

/-- The two-variable segment kernel whose `u`-integral is the Frullani integrand. -/
noncomputable def segKernel (a b : ℂ) (t u : ℝ) : ℂ := (b - a) * Complex.exp (-(seg a b u * t))

theorem continuous_uncurry_segKernel (a b : ℂ) :
    Continuous (Function.uncurry (segKernel a b)) := by
  have hs : Continuous (fun p : ℝ × ℝ => seg a b p.2) := (continuous_seg a b).comp continuous_snd
  unfold Function.uncurry segKernel
  fun_prop

theorem integral_segKernel_eq (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioc (0 : ℝ) 1, segKernel a b t u) =
      (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t := by
  rw [← intervalIntegral.integral_of_le (zero_le_one)]
  exact intervalIntegral_seg_cexp a b ht

theorem integrable_uncurry_segKernel (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (Function.uncurry (segKernel a b))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  set c : ℝ := min a.re b.re with hc
  have hcpos : 0 < c := lt_min ha hb
  have hdom : Integrable (fun p : ℝ × ℝ => ‖b - a‖ * Real.exp (-c * p.1))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have h1 : Integrable (fun t : ℝ => ‖b - a‖ * Real.exp (-c * t))
        (volume.restrict (Ioi (0 : ℝ))) := (exp_neg_integrableOn_Ioi 0 hcpos).const_mul _
    exact h1.comp_fst _
  have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioc (0 : ℝ) 1))), p ∈ Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)
  refine Integrable.mono' hdom (continuous_uncurry_segKernel a b).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  obtain ⟨ht, hu⟩ := hp
  have hu' : p.2 ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1, hu.2⟩
  have hre : c ≤ (seg a b p.2).re := min_re_le_seg_re a b hu'
  have ht' : (0 : ℝ) < p.1 := ht
  simp only [Function.uncurry, segKernel, norm_mul]
  rw [norm_cexp_neg_mul_ofReal]
  have hle : -((seg a b p.2).re * p.1) ≤ -c * p.1 := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg _)

/-- The Frullani integrand is integrable on the positive ray. -/
theorem integrableOn_frullani (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t)
      (Ioi (0 : ℝ)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  have h := (integrable_uncurry_segKernel ha hb).integral_prod_left
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integral_segKernel_eq a b ht

/-- **The complex Frullani integral.** -/
theorem integral_frullani (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t) =
      Complex.log b - Complex.log a := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  have hstep1 :
      (∫ t in Ioi (0 : ℝ), (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t) =
        ∫ t in Ioi (0 : ℝ), ∫ u in Ioc (0 : ℝ) 1, segKernel a b t u := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact (integral_segKernel_eq a b ht).symm
  rw [hstep1, integral_integral_swap (integrable_uncurry_segKernel ha hb)]
  have hstep4 : (∫ u in Ioc (0 : ℝ) 1, ∫ t in Ioi (0 : ℝ), segKernel a b t u) =
      ∫ u in Ioc (0 : ℝ) 1, (b - a) * (1 / seg a b u) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1, hu.2⟩
    simp only [segKernel]
    rw [integral_const_mul, integral_cexp_neg_mul (seg_re_pos ha hb hu')]
  rw [hstep4]
  have hprim : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Complex.log (seg a b v)) ((b - a) * (1 / seg a b u)) u := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    have hseg : HasDerivAt (fun v : ℝ => seg a b v) (b - a) u := by
      have hb' : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa [seg] using (hb'.mul_const (b - a)).const_add a
    have h : HasDerivAt (fun v : ℝ => Complex.log (seg a b v))
        ((seg a b u)⁻¹ * (b - a)) u :=
      HasDerivAt.comp u (Complex.hasDerivAt_log (seg_mem_slitPlane ha hb hu)) hseg
    refine h.congr_deriv ?_
    rw [one_div]
    ring
  have hintu : IntervalIntegrable (fun u : ℝ => (b - a) * (1 / seg a b u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const (continuous_seg a b).continuousOn
    intro u hu
    exact seg_ne_zero ha hb hu
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hintu, seg_zero, seg_one]

end Frullani

end GaloisForLFunctions.HTGeometry
