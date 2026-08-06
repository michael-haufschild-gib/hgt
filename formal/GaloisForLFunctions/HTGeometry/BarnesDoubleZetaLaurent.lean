import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaHolomorphy
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The Laurent expansion of the Barnes double zeta at `s = 1`

Dividing the split Mellin representation by `Gamma` defines the continued Barnes double zeta on the
right half-plane.  It agrees with the convergent series where that converges, and is analytic away
from `s = 1` and `s = 2`.

At `s = 1` the reciprocal `1/Gamma` equals `1`, so the pole of the head survives with residue the
linear Taylor coefficient of the extended cone kernel.  Subtracting it leaves an analytic remainder,
built from the divided difference of `1/Gamma` at `1`; its value there is the finite part, which is
the quantity the double gamma is defined by.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The analytic part of the split Mellin representation: the subtracted head plus the tail. -/
def barnesConeContinuedPart (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
    + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t

/-- **The meromorphic continuation of the Barnes double zeta to the right half-plane.** -/
def barnesDoubleZetaCont (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
      + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
      + barnesConeContinuedPart o1 o2 x s) * (Complex.Gamma s)⁻¹

/-- **The continuation agrees with the convergent series.** -/
theorem barnesDoubleZetaCont_eq_barnesDoubleZeta {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    barnesDoubleZetaCont o1 o2 x s = barnesDoubleZeta o1 o2 s (x : ℂ) := by
  have hs0 : 0 < s.re := by linarith
  have hG : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (HTGeometry.ne_neg_natCast_of_re_pos hs0)
  have hcont := Gamma_mul_barnesDoubleZeta_eq_continuation h1 h2 hx hs
  rw [barnesDoubleZetaCont, barnesConeContinuedPart]
  rw [show (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
      + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
      + ((∫ t in Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (s - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t))
      = Complex.Gamma s * barnesDoubleZeta o1 o2 s (x : ℂ) by
    rw [hcont]; ring]
  field_simp

/-- The analytic remainder of the continued Barnes double zeta at its pole `s = 1`. -/
def barnesDoubleZetaRemainderOne (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2) + barnesConeContinuedPart o1 o2 x s)
      * (Complex.Gamma s)⁻¹
    + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ)
        * analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 1 s

/-- **The Laurent expansion at `s = 1`.**  Off the pole the continuation is a simple pole with
residue the linear Taylor coefficient of the extended cone kernel, plus an analytic remainder. -/
theorem barnesDoubleZetaCont_eq_pole_add_remainder {o1 o2 x : ℝ} {s : ℂ} (hs : s ≠ 1) :
    barnesDoubleZetaCont o1 o2 x s
      = barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + barnesDoubleZetaRemainderOne o1 o2 x s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hQ1 : (Complex.Gamma (1 : ℂ))⁻¹ = 1 := by simp [Complex.Gamma_one]
  have hslope := sub_eq_mul_analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 1 s
  simp only [hQ1] at hslope
  rw [barnesDoubleZetaCont, barnesDoubleZetaRemainderOne]
  set Qs : ℂ := (Complex.Gamma s)⁻¹ with hQsdef
  set σ : ℂ := analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 1 s with hσdef
  have hQs : Qs = 1 + (s - 1) * σ := by
    rw [hQsdef, hσdef]
    linear_combination hslope
  have key : barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1) * Qs
      = barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
        + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) * σ := by
    rw [hQs]
    field_simp
  linear_combination key

theorem analyticAt_barnesDoubleZetaRemainderOne {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) : AnalyticAt ℂ (barnesDoubleZetaRemainderOne o1 o2 x) 1 := by
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hQent : AnalyticAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) 1 :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) 1
      (Set.mem_univ 1)
  have hpole : AnalyticAt ℂ (fun w : ℂ => ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (w - 2)) 1 := by
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro hcon
    have : (1 : ℂ) = 2 := by linear_combination hcon
    exact absurd this (by norm_num)
  exact ((hpole.add (analyticAt_barnesConeContinuedPart h1 h2 hx hone)).mul hQent).add
    (analyticAt_const.mul (analyticAt_analyticSlope hQent))

/-- **The residue at `s = 1`.**  The linear Taylor coefficient of the extended cone kernel is the
residue of the continued Barnes double zeta. -/
theorem tendsto_sub_one_mul_barnesDoubleZetaCont {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * barnesDoubleZetaCont o1 o2 x s) (𝓝[≠] (1 : ℂ))
      (𝓝 (barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ))) := by
  have hR := (analyticAt_barnesDoubleZetaRemainderOne h1 h2 hx).continuousAt
  have heq : (fun s : ℂ => (s - 1) * barnesDoubleZetaCont o1 o2 x s)
      =ᶠ[𝓝[≠] (1 : ℂ)] (fun s : ℂ => barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ)
        + (s - 1) * barnesDoubleZetaRemainderOne o1 o2 x s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [barnesDoubleZetaCont_eq_pole_add_remainder hs]
    field_simp
  refine Filter.Tendsto.congr' heq.symm ?_
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * barnesDoubleZetaRemainderOne o1 o2 x s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul hR
  have h0 : Filter.Tendsto (fun s : ℂ => (s - 1) * barnesDoubleZetaRemainderOne o1 o2 x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℂ => (s - 1) * barnesDoubleZetaRemainderOne o1 o2 x s)
        (𝓝[≠] (1 : ℂ)) (𝓝 ((1 - 1) * barnesDoubleZetaRemainderOne o1 o2 x 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  simpa using tendsto_const_nhds.add h0

/-- **The continuation is analytic away from its two poles.** -/
theorem analyticAt_barnesDoubleZetaCont {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) (hne1 : s ≠ 1) (hne2 : s ≠ 2) :
    AnalyticAt ℂ (barnesDoubleZetaCont o1 o2 x) s := by
  have hQent : AnalyticAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) s
      (Set.mem_univ s)
  have hpole2 : AnalyticAt ℂ (fun w : ℂ => ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (w - 2)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne2)
  have hpole1 : AnalyticAt ℂ
      (fun w : ℂ => barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (w - 1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne1)
  exact ((hpole2.add hpole1).add (analyticAt_barnesConeContinuedPart h1 h2 hx hs)).mul hQent

/-- The finite part of the continued Barnes double zeta at `s = 1`. -/
def barnesDoubleZetaFinitePartOne (o1 o2 x : ℝ) : ℂ := barnesDoubleZetaRemainderOne o1 o2 x 1

end

end GaloisForLFunctions.HTGeometry
