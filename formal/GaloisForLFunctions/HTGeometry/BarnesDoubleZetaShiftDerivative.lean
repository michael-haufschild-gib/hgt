import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaHolomorphy
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The shift derivative of the Barnes double zeta

Differentiating the Mellin representation in the shift multiplies the integrand by `-t`, which is
the same as raising the Mellin variable by one.  Dominating by the integrand at half the shift,
where the exponential decay is still integrable against `t^(Re s)`, licenses the differentiation
under the integral sign, and dividing by `Gamma` turns it into

```text
∂_x zeta_2(s,x) = -s zeta_2(s+1,x).
```

This is the relation that connects the finite part at `s = 1` to the logarithmic derivative of the
double gamma.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Mellin integrand of the cone kernel is integrable on the whole half-line beyond the
abscissa. -/
theorem integrableOn_cpow_mul_barnesConeKernel_Ioi {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t) (Ioi 0) := by
  have hs0 : 0 < s.re := by linarith
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le.mpr ht')
  have h := (integrableOn_cpow_mul_barnesConeKernel_Ioc (x := x) h1 h2 hs).union
    (integrableOn_cpow_mul_barnesConeKernel_Ioi_one h1 h2 hx hs0)
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- The `x`-derivative of the cone kernel. -/
theorem hasDerivAt_barnesConeKernel (o1 o2 : ℝ) (t : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => barnesConeKernel o1 o2 y t)
      (-(t : ℂ) * barnesConeKernel o1 o2 x t) x := by
  have hlin : HasDerivAt (fun y : ℝ => -y * t) (-t) x := by
    simpa using ((hasDerivAt_id x).neg.mul_const t)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y * t)) (Real.exp (-x * t) * -t) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-x * t)).comp x hlin
  have hC : HasDerivAt (fun y : ℝ => ((Real.exp (-y * t) : ℝ) : ℂ))
      (((Real.exp (-x * t) * -t : ℝ) : ℂ)) x := hexp.ofReal_comp
  have hres := hC.div_const
    ((1 - ((Real.exp (-o1 * t) : ℝ) : ℂ)) * (1 - ((Real.exp (-o2 * t) : ℝ) : ℂ)))
  refine hres.congr_deriv ?_
  rw [barnesConeKernel]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_barnesConeKernel_eq {o1 o2 x t : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (ht : 0 < t) :
    ‖barnesConeKernel o1 o2 x t‖
      = Real.exp (-x * t) / ((1 - Real.exp (-o1 * t)) * (1 - Real.exp (-o2 * t))) := by
  rw [barnesConeKernel, norm_div, norm_mul, norm_one_sub_exp_neg_mul_ofReal h1 ht,
    norm_one_sub_exp_neg_mul_ofReal h2 ht, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_barnesConeKernel_mono {o1 o2 a y t : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (ht : 0 < t)
    (hay : a ≤ y) :
    ‖barnesConeKernel o1 o2 y t‖ ≤ ‖barnesConeKernel o1 o2 a t‖ := by
  rw [norm_barnesConeKernel_eq h1 h2 ht, norm_barnesConeKernel_eq h1 h2 ht]
  have hd : 0 < (1 - Real.exp (-o1 * t)) * (1 - Real.exp (-o2 * t)) :=
    mul_pos (one_sub_exp_neg_mul_ofReal_pos h1 ht) (one_sub_exp_neg_mul_ofReal_pos h2 ht)
  gcongr

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Differentiating the Mellin representation in the shift.**  The `x`-derivative of the Mellin
integrand is the integrand at `s + 1`, up to sign. -/
theorem hasDerivAt_mellin_barnesConeKernel {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    HasDerivAt (fun y : ℝ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 y t)
      (-∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) * barnesConeKernel o1 o2 x t) x := by
  set a : ℝ := x / 2 with hadef
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hs1 : 2 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hs0 : 0 < s.re := by linarith
  have hmeasA : AEStronglyMeasurable (barnesConeKernel o1 o2 a)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_barnesConeKernel h1 h2).aestronglyMeasurable measurableSet_Ioi
  have hboundInt : IntegrableOn
      (fun t : ℝ => t ^ ((s + 1).re - 1) * ‖barnesConeKernel o1 o2 a t‖) (Ioi 0) := by
    rw [← mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi hmeasA]
    simpa [smul_eq_mul] using integrableOn_cpow_mul_barnesConeKernel_Ioi h1 h2 ha0 hs1
  have hFmeas : ∀ y : ℝ,
      AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 y t)
        (volume.restrict (Ioi (0 : ℝ))) := fun y =>
    aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi (subset_refl _)
      (continuousOn_barnesConeKernel h1 h2) s
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (-(t : ℂ) * barnesConeKernel o1 o2 x t))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi (subset_refl _)
      (ContinuousOn.mul ?_ (continuousOn_barnesConeKernel h1 h2)) s
    exact (Complex.continuous_ofReal.neg).continuousOn
  have hball : Metric.ball x a ∈ 𝓝 x := Metric.ball_mem_nhds x ha0
  have hbnd : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y ∈ Metric.ball x a,
      ‖(t : ℂ) ^ (s - 1) * (-(t : ℂ) * barnesConeKernel o1 o2 y t)‖
        ≤ t ^ ((s + 1).re - 1) * ‖barnesConeKernel o1 o2 a t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    have ht0 : (0 : ℝ) < t := ht
    have hay : a ≤ y := by
      rw [Real.ball_eq_Ioo] at hy
      have : x - a < y := hy.1
      rw [hadef] at this ⊢
      linarith
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, Complex.sub_re, Complex.one_re,
      Complex.add_re, Complex.one_re]
    have hpow : t ^ (s.re - 1) * t = t ^ (s.re + 1 - 1) := by
      rw [show s.re + 1 - 1 = (s.re - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    calc t ^ (s.re - 1) * (t * ‖barnesConeKernel o1 o2 y t‖)
        = (t ^ (s.re - 1) * t) * ‖barnesConeKernel o1 o2 y t‖ := by ring
      _ = t ^ (s.re + 1 - 1) * ‖barnesConeKernel o1 o2 y t‖ := by rw [hpow]
      _ ≤ t ^ (s.re + 1 - 1) * ‖barnesConeKernel o1 o2 a t‖ := by
          exact mul_le_mul_of_nonneg_left (norm_barnesConeKernel_mono h1 h2 ht0 hay)
            (Real.rpow_nonneg ht0.le _)
  have hdiff : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y ∈ Metric.ball x a,
      HasDerivAt (fun y : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 y t)
        ((t : ℂ) ^ (s - 1) * (-(t : ℂ) * barnesConeKernel o1 o2 y t)) y := by
    filter_upwards with t y _
    exact (hasDerivAt_barnesConeKernel o1 o2 t y).const_mul _
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball
    (Eventually.of_forall hFmeas)
    (integrableOn_cpow_mul_barnesConeKernel_Ioi h1 h2 hx hs) hF'meas hbnd hboundInt hdiff).2
  refine hmain.congr_deriv ?_
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
  have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s + 1 - 1) := by
    rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
  rw [show (t : ℂ) ^ (s - 1) * (-(t : ℂ) * barnesConeKernel o1 o2 x t)
      = -(((t : ℂ) ^ (s - 1) * (t : ℂ)) * barnesConeKernel o1 o2 x t) by ring, hpow]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The shift derivative of the Barnes double zeta.**  Differentiating the argument lowers the
weight: `∂_x ζ₂(s,x) = -s ζ₂(s+1,x)`. -/
theorem hasDerivAt_barnesDoubleZeta_shift {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    HasDerivAt (fun y : ℝ => barnesDoubleZeta o1 o2 s (y : ℂ))
      (-s * barnesDoubleZeta o1 o2 (s + 1) (x : ℂ)) x := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by
    intro hcon
    rw [hcon] at hs0
    simp at hs0
  have hΓ : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (_root_.HTGeometry.ne_neg_natCast_of_re_pos hs0)
  have hs1 : 2 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hscaled := (hasDerivAt_mellin_barnesConeKernel h1 h2 hx hs).const_mul
    (Complex.Gamma s)⁻¹
  have heq : (fun y : ℝ => barnesDoubleZeta o1 o2 s (y : ℂ))
      =ᶠ[𝓝 x] fun y : ℝ => (Complex.Gamma s)⁻¹ *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 y t := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hval := Gamma_mul_barnesDoubleZeta_eq_mellin h1 h2 hy hs
    rw [mellin] at hval
    simp only [smul_eq_mul] at hval
    rw [← hval]
    field_simp
  refine (hscaled.congr_of_eventuallyEq heq).congr_deriv ?_
  have hval1 := Gamma_mul_barnesDoubleZeta_eq_mellin h1 h2 hx hs1
  rw [mellin] at hval1
  simp only [smul_eq_mul] at hval1
  rw [← hval1, Complex.Gamma_add_one s hsne]
  field_simp

end

end GaloisForLFunctions.HTGeometry
