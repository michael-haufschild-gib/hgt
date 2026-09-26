import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mellin inverse-tail finite parts

Continuity of the extended divided difference gives the exact logarithmic subtraction and finite limit for an integrable differentiable source.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.MellinBoundary

lemma continuous_dslope_zero {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) : Continuous (dslope f 0) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr hd
  · exact (continuousAt_dslope_of_ne hx).mpr hc.continuousAt

lemma integrableOn_div_id {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    {x : ℝ} (hx : 0 < x) : IntegrableOn (fun t => f t/t) (Ioi x) := by
  refine (hi.norm.div_const x).integrableOn.mono' ?_ ?_
  · exact (hc.continuousOn.div continuousOn_id
      (fun t ht => ne_of_gt (hx.trans ht))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_div, Real.norm_eq_abs t, abs_of_pos (hx.trans ht)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hx ht.le

lemma inverseTail_finitePart_eq {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, f t/t)-f 0*Real.log (1/x) =
      -(∫ t in (1:ℝ)..x, dslope f 0 t)+(∫ t in Ioi (1:ℝ), f t/t) := by
  have hs := continuous_dslope_zero hc hd
  have ht (t : ℝ) (ht : t ∈ uIcc x 1) : 0 < t :=
    (lt_min hx zero_lt_one).trans_le ht.1
  have hrecip : IntervalIntegrable (fun t : ℝ => 1/t) volume x 1 :=
    (continuousOn_const.div continuousOn_id (fun t h => (ht t h).ne')).intervalIntegrable
  have he : (∫ t in x..1, f t/t) =
      f 0*Real.log (1/x)+(∫ t in x..1, dslope f 0 t) := by
    calc
      _ = ∫ t in x..1, f 0*(1/t)+dslope f 0 t := by
        apply intervalIntegral.integral_congr
        intro t h
        have hmul := sub_smul_dslope f (0:ℝ) t
        simp only [sub_zero, smul_eq_mul] at hmul
        apply (div_eq_iff (ht t h).ne').mpr
        field_simp [(ht t h).ne']
        linear_combination -hmul
      _ = _ := by
        rw [intervalIntegral.integral_add (hrecip.const_mul _) (hs.intervalIntegrable x 1),
          intervalIntegral.integral_const_mul, integral_one_div_of_pos hx zero_lt_one]
  rw [← intervalIntegral.integral_interval_add_Ioi
    (integrableOn_div_id hc hi hx) (integrableOn_div_id hc hi zero_lt_one), he,
    intervalIntegral.integral_symm 1 x]
  ring

lemma inverseTail_finitePart_tendsto {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) :
    Tendsto (fun x => (∫ t in Ioi x, f t/t)-f 0*Real.log (1/x)) (𝓝[>] 0)
      (𝓝 ((∫ t in (0:ℝ)..1, dslope f 0 t)+(∫ t in Ioi (1:ℝ), f t/t))) := by
  have hs := continuous_dslope_zero hc hd
  have hprim : Continuous (fun x => -(∫ t in (1:ℝ)..x, dslope f 0 t)+
      (∫ t in Ioi (1:ℝ), f t/t)) :=
    ((intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hs.intervalIntegrable a b) (1:ℝ)).neg).add continuous_const
  have hlim : Tendsto (fun x => -(∫ t in (1:ℝ)..x, dslope f 0 t)+
      (∫ t in Ioi (1:ℝ), f t/t)) (𝓝[>] 0)
      (𝓝 (-(∫ t in (1:ℝ)..0, dslope f 0 t)+(∫ t in Ioi (1:ℝ), f t/t))) :=
    hprim.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_symm 0 1, neg_neg] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (inverseTail_finitePart_eq hc hd hi hx).symm

lemma log_inv_tendsto :
    Tendsto (fun x : ℝ => Real.log (1/x)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Real.log_inv, Function.comp_def] using
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

lemma inverseTail_log_ratio_tendsto {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (hi : Integrable f) :
    Tendsto (fun x => (∫ t in Ioi x, f t/t)/Real.log (1/x)) (𝓝[>] 0) (𝓝 (f 0)) := by
  have h := (inverseTail_finitePart_tendsto hc hd hi).div_atTop log_inv_tendsto
  have hlim := (show Tendsto (fun _ : ℝ => f 0) (𝓝[>] 0) (𝓝 (f 0))
    from tendsto_const_nhds).add h
  rw [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [log_inv_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx
  field_simp [hx.ne']
  ring

end GaloisForLFunctions.HTGeometry.MellinBoundary
