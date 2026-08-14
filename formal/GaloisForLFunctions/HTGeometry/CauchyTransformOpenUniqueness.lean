import GaloisForLFunctions.HTGeometry.CompleteCauchyGermClosure
import GaloisForLFunctions.HTGeometry.StieltjesTransformPick
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# A Cauchy transform on an open set determines a finite measure

The resolvent transform of a finite measure on the line is analytic off the line, so agreement on a
nonempty open subset of the upper half-plane propagates to the whole half-plane by the identity
theorem.  The total masses are then recovered as `lim_{y→∞} y·Im S(iy)`, and after normalising both
measures the complete Cauchy germ at a single point determines them.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

noncomputable section

/-- The open upper half-plane. -/
def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_upperHalfPlaneSet : IsOpen upperHalfPlaneSet :=
  isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_upperHalfPlaneSet : IsPreconnected upperHalfPlaneSet := by
  refine (Convex.isPreconnected ?_)
  intro x hx y hy a b ha hb hab
  have hx' : 0 < x.im := hx
  have hy' : 0 < y.im := hy
  show 0 < (a • x + b • y).im
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb0 : 0 < b := by
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · exfalso
        rw [← ha0, ← hb0] at hab
        norm_num at hab
      · exact hb0
    rw [← ha0]
    simpa using mul_pos hb0 hy'
  · have := mul_pos ha0 hx'
    have hb' : 0 ≤ b * y.im := mul_nonneg hb hy'.le
    linarith

/-- The resolvent transform of a finite real measure is analytic on the upper half-plane. -/
theorem analyticOnNhd_resolventTransform_upper (mu : Measure ℝ) [IsFiniteMeasure mu] :
    AnalyticOnNhd ℂ (resolventTransform mu) upperHalfPlaneSet := by
  have hsub : upperHalfPlaneSet ⊆ (algebraMap ℝ ℂ '' mu.support)ᶜ := by
    rintro z hz ⟨x, -, hx⟩
    have : z.im = 0 := by
      rw [← hx]
      simp
    exact absurd this (ne_of_gt hz)
  have hA0 : AnalyticOn ℂ (resolventTransform mu) (algebraMap ℝ ℂ '' mu.support)ᶜ :=
    MeasureTheory.analyticOn_resolventTransform
  exact (isOpen_upperHalfPlaneSet.analyticOn_iff_analyticOnNhd).1 (hA0.mono hsub)

/-- Agreement of two resolvent transforms on a nonempty open subset propagates to the whole upper
half-plane. -/
theorem eqOn_upper_of_eqOn_open (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {V : Set ℂ} (hV : IsOpen V) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hVsub : V ⊆ upperHalfPlaneSet)
    (heq : EqOn (resolventTransform mu) (resolventTransform nu) V) :
    EqOn (resolventTransform mu) (resolventTransform nu) upperHalfPlaneSet := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_resolventTransform_upper mu) (analyticOnNhd_resolventTransform_upper nu)
    isPreconnected_upperHalfPlaneSet (hVsub hz₀) ?_
  filter_upwards [hV.mem_nhds hz₀] with z hz
  exact heq hz

/-- The resolvent transform of a real measure at a nonreal point is the Cauchy transform. -/
theorem resolventTransform_eq_cauchy (mu : Measure ℝ) (z : ℂ) :
    resolventTransform mu z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂mu := by
  rw [resolventTransform_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [resolvent, Ring.inverse_eq_inv']

/-- **Total mass from the Cauchy transform.**  `y·Im S_μ(iy) → μ(ℝ)` as `y → ∞`. -/
theorem tendsto_mul_im_resolventTransform (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Tendsto (fun y : ℝ => y * (resolventTransform mu (y * Complex.I)).im) atTop
      (𝓝 (mu univ).toReal) := by
  have hpoisson : ∀ y : ℝ, 0 < y →
      y * (resolventTransform mu (y * Complex.I)).im = ∫ x : ℝ, y ^ 2 / (x ^ 2 + y ^ 2) ∂mu := by
    intro y hy
    have hz : ((y : ℂ) * Complex.I).im = y := by simp
    have hzre : ((y : ℂ) * Complex.I).re = 0 := by simp
    have hnotmem : ((y : ℂ) * Complex.I) ∉ algebraMap ℝ ℂ '' mu.support := by
      rintro ⟨x, -, hx⟩
      have him : ((y : ℂ) * Complex.I).im = 0 := by
        rw [← hx]
        simp
      rw [hz] at him
      exact absurd him (ne_of_gt hy)
    have hInt : Integrable (fun x : ℝ => ((x : ℂ) - (y * Complex.I))⁻¹) mu := by
      refine (MeasureTheory.integrable_resolvent hnotmem).congr ?_
      filter_upwards with x
      simp [resolvent, Ring.inverse_eq_inv']
    rw [resolventTransform_eq_cauchy, HTGeometry.stieltjesTransform_im_eq_poisson _ hInt, hzre, hz,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
    field_simp
    ring
  have hlim : Tendsto (fun y : ℝ => ∫ x : ℝ, y ^ 2 / (x ^ 2 + y ^ 2) ∂mu) atTop
      (𝓝 (∫ _x : ℝ, (1 : ℝ) ∂mu)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      refine (Measurable.aestronglyMeasurable ?_)
      have : Measurable fun x : ℝ => x ^ 2 + y ^ 2 := by fun_prop
      exact measurable_const.div this
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      filter_upwards with x
      have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_one hpos]
      nlinarith [sq_nonneg x]
    · exact integrable_const 1
    · filter_upwards with x
      have hx : Tendsto (fun y : ℝ => x ^ 2 / y ^ 2 + 1) atTop (𝓝 1) := by
        have h1 : Tendsto (fun y : ℝ => x ^ 2 / y ^ 2) atTop (𝓝 0) := by
          have hsq : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
            tendsto_pow_atTop (by norm_num)
          simpa [div_eq_mul_inv] using hsq.inv_tendsto_atTop.const_mul (x ^ 2)
        simpa using h1.add_const 1
      have hkey : (fun y : ℝ => y ^ 2 / (x ^ 2 + y ^ 2))
          =ᶠ[atTop] fun y : ℝ => (x ^ 2 / y ^ 2 + 1)⁻¹ := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        have hy2 : (y : ℝ) ^ 2 ≠ 0 := by positivity
        have hsum : x ^ 2 + y ^ 2 ≠ 0 := by positivity
        field_simp
      refine Tendsto.congr' hkey.symm ?_
      simpa using hx.inv₀ (by norm_num)
  have hfinal : Tendsto (fun y : ℝ => y * (resolventTransform mu (y * Complex.I)).im) atTop
      (𝓝 (∫ _x : ℝ, (1 : ℝ) ∂mu)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (hpoisson y hy).symm
  simpa [integral_const, measureReal_def] using hfinal

/-- Two finite measures whose Cauchy transforms agree on the upper half-plane have the same mass. -/
theorem measure_univ_eq_of_eqOn_upper (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (heq : EqOn (resolventTransform mu) (resolventTransform nu) upperHalfPlaneSet) :
    mu univ = nu univ := by
  have hcongr : (fun y : ℝ => y * (resolventTransform mu (y * Complex.I)).im)
      =ᶠ[atTop] fun y : ℝ => y * (resolventTransform nu (y * Complex.I)).im := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hmem : ((y : ℂ) * Complex.I) ∈ upperHalfPlaneSet := by
      show 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    rw [heq hmem]
  have h1 := tendsto_mul_im_resolventTransform mu
  have h2 := (tendsto_mul_im_resolventTransform nu).congr' hcongr.symm
  have hreal : (mu univ).toReal = (nu univ).toReal := tendsto_nhds_unique h1 h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu univ) (measure_ne_top nu univ)).1 hreal

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology
open scoped ENNReal

noncomputable section

/-- Scaling a measure scales its resolvent transform. -/
theorem resolventTransform_smul (c : ℝ≥0∞) (mu : Measure ℝ) (z : ℂ) :
    resolventTransform (c • mu) z = (c.toReal : ℂ) * resolventTransform mu z := by
  rw [resolventTransform_apply, resolventTransform_apply, integral_smul_measure]
  simp [Complex.real_smul]

/-- **Cauchy-transform uniqueness from an open set.**  Two finite measures on the line whose
resolvent transforms agree on a nonempty open subset of the upper half-plane are equal. -/
theorem measure_eq_of_resolventTransform_eqOn_open (mu nu : Measure ℝ) [IsFiniteMeasure mu]
    [IsFiniteMeasure nu] {V : Set ℂ} (hV : IsOpen V) {z₀ : ℂ} (hz₀ : z₀ ∈ V)
    (hVsub : V ⊆ upperHalfPlaneSet)
    (heq : EqOn (resolventTransform mu) (resolventTransform nu) V) :
    mu = nu := by
  have hupper := eqOn_upper_of_eqOn_open mu nu hV hz₀ hVsub heq
  have hmass := measure_univ_eq_of_eqOn_upper mu nu hupper
  have hz₀im : z₀.im ≠ 0 := ne_of_gt (hVsub hz₀)
  by_cases hzero : mu univ = 0
  · have hmu : mu = 0 := MeasureTheory.Measure.measure_univ_eq_zero.mp hzero
    have hnuzero : nu univ = 0 := by rw [← hmass, hzero]
    have hnu : nu = 0 := MeasureTheory.Measure.measure_univ_eq_zero.mp hnuzero
    rw [hmu, hnu]
  · set c : ℝ≥0∞ := (mu univ)⁻¹ with hc
    have hfin : mu univ ≠ ⊤ := measure_ne_top mu univ
    have hcne : c ≠ 0 := ENNReal.inv_ne_zero.2 hfin
    have hctop : c ≠ ⊤ := ENNReal.inv_ne_top.2 hzero
    haveI hpmu : IsProbabilityMeasure (c • mu) := by
      constructor
      show c * mu univ = 1
      rw [hc]
      exact ENNReal.inv_mul_cancel hzero hfin
    haveI hpnu : IsProbabilityMeasure (c • nu) := by
      constructor
      show c * nu univ = 1
      rw [hc, ← hmass]
      exact ENNReal.inv_mul_cancel hzero hfin
    have hfun : resolventTransform (c • mu) =ᶠ[𝓝 z₀] resolventTransform (c • nu) := by
      filter_upwards [hV.mem_nhds hz₀] with z hz
      rw [resolventTransform_smul, resolventTransform_smul, heq hz]
    have hjet : ∀ n : ℕ, iteratedDeriv n (resolventTransform (c • mu)) z₀ =
        iteratedDeriv n (resolventTransform (c • nu)) z₀ := by
      intro n
      exact (hfun.iteratedDeriv n).eq_of_nhds
    have hscaled : c • mu = c • nu := measure_eq_of_completeCauchyJet_eq _ _ hz₀im hjet
    have hcancel : (mu univ) • (c • mu) = (mu univ) • (c • nu) := by rw [hscaled]
    rw [smul_smul, smul_smul, hc, ENNReal.mul_inv_cancel hzero hfin, one_smul, one_smul] at hcancel
    exact hcancel

end

end GaloisForLFunctions.HTGeometry
