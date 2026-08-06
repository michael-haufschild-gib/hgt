import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaDeepContinuation
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaHolomorphy
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The Barnes double gamma

The deep split makes the continued double zeta an analytic function on `Re s > -1` away from its
three poles.  At `s = 0` the head's pole meets the simple zero of `1/Gamma`, and the two cancel:
replacing `A_2/s * (1/Gamma s)` by `A_2` times the divided difference of `1/Gamma` at the origin
gives a function analytic there and agreeing with the continuation off the origin.

Its derivative at the origin is `∂_s zeta_2(s,x)|_{s=0}`, the logarithm of the Barnes double gamma.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The tail integral is entire.**  The tail integrand vanishes near the origin, so no lower
bound on `Re s` is needed. -/
theorem differentiableAt_barnesConeTail_all {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesConeKernel o1 o2 x t) s := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hfun : (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesConeKernel o1 o2 x t)
      = mellin (Set.indicator (Ioi (1 : ℝ)) (barnesConeKernel o1 o2 x)) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioi hsub _ w]
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow_exp (b := s.re - 1) hx ?_
    (isBigO_indicator_barnesConeKernel_atTop h1 h2) ?_ (by linarith)
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioi hsub
        (integrableOn_barnesConeKernel_Ioi_one h1 h2 hx))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact fun hmem => absurd (mem_Ioi.mp hmem) (not_lt.mpr ht.2.le)

theorem isBigO_indicator_barnesConeCubicRemainder_zero {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) :
    Set.indicator (Ioc (0 : ℝ) 1)
        (fun t : ℝ => barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesConeCubicRemainder h1 h2 x
  refine Asymptotics.isBigO_iff.mpr ⟨max C 0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  by_cases hin : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hin]
    exact le_trans (hC t ⟨hin.1.le, hin.2⟩) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hin, norm_zero]
    exact le_max_right _ _

/-- **The subtracted head integral is holomorphic beyond the origin.** -/
theorem differentiableAt_barnesConeDeepHead {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ)
    {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w + 1 - 1) *
        barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)) s := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hfun : (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w + 1 - 1) *
        barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
      = (fun w : ℂ => mellin (Set.indicator (Ioc (0 : ℝ) 1)
          (fun t : ℝ => barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))) w)
        ∘ (fun w : ℂ => w + 1) := by
    funext w
    rw [Function.comp_apply, mellin_indicator_of_subset measurableSet_Ioc hsub _ (w + 1)]
  rw [hfun]
  have hshift : (0 : ℝ) < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  refine DifferentiableAt.comp s ?_ (differentiableAt_id.add_const 1)
  refine mellin_differentiableAt_of_isBigO_rpow (a := (s + 1).re + 1) (b := 0) ?_ ?_
    (by linarith) ?_ hshift
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioc hsub
        (((continuousOn_barnesConeCubicRemainder_ofReal h1 h2 x).integrableOn_compact
          isCompact_Icc).mono_set (fun _ ht => ⟨ht.1.le, ht.2⟩)))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact fun hmem => absurd hmem.2 (not_le.mpr ht)
  · exact isBigO_indicator_barnesConeCubicRemainder_zero h1 h2 x

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The analytic part of the deep split: the subtracted head plus the tail. -/
def barnesConeDeepPart (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
      barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
    + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t

theorem analyticAt_barnesConeDeepPart {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : -1 < s.re) : AnalyticAt ℂ (barnesConeDeepPart o1 o2 x) s := by
  have hopen : IsOpen {w : ℂ | -1 < w.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  refine DifferentiableOn.analyticAt (s := {w : ℂ | -1 < w.re}) ?_ (hopen.mem_nhds hs)
  intro w hw
  exact ((differentiableAt_barnesConeDeepHead h1 h2 x hw).add
    (differentiableAt_barnesConeTail_all h1 h2 hx w)).differentiableWithinAt

/-- **The continuation of the Barnes double zeta beyond the origin.** -/
def barnesDoubleZetaDeep (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
      + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
      + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s
      + barnesConeDeepPart o1 o2 x s) * (Complex.Gamma s)⁻¹

theorem barnesDoubleZetaDeep_eq_barnesDoubleZeta {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    barnesDoubleZetaDeep o1 o2 x s = barnesDoubleZeta o1 o2 s (x : ℂ) := by
  have hs0 : 0 < s.re := by linarith
  have hG : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (_root_.HTGeometry.ne_neg_natCast_of_re_pos hs0)
  have hcont := Gamma_mul_barnesDoubleZeta_eq_continuation_three h1 h2 hx hs
  rw [barnesDoubleZetaDeep, barnesConeDeepPart]
  rw [show (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
      + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
      + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s
      + ((∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t))
      = Complex.Gamma s * barnesDoubleZeta o1 o2 s (x : ℂ) by rw [hcont]; ring]
  field_simp

/-- The regularization of the deep continuation at the origin: the pole of the head is cancelled by
the simple zero of `1/Gamma`. -/
def barnesDoubleZetaRegZero (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  (((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
      + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
      + barnesConeDeepPart o1 o2 x s) * (Complex.Gamma s)⁻¹
    + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ)
        * analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s

theorem barnesDoubleZetaRegZero_eq {o1 o2 x : ℝ} {s : ℂ} (hs : s ≠ 0) :
    barnesDoubleZetaRegZero o1 o2 x s = barnesDoubleZetaDeep o1 o2 x s := by
  have hG0 : (Complex.Gamma (0 : ℂ))⁻¹ = 0 := by
    rw [Complex.Gamma_zero, inv_zero]
  have hslope := sub_eq_mul_analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s
  simp only [hG0, sub_zero] at hslope
  rw [barnesDoubleZetaRegZero, barnesDoubleZetaDeep]
  set Qs : ℂ := (Complex.Gamma s)⁻¹ with hQs
  set σ : ℂ := analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s with hσ
  have hQ : Qs = s * σ := by rw [hQs, hσ]; linear_combination hslope
  have key : barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s * Qs
      = barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) * σ := by
    rw [hQ]
    field_simp
  linear_combination -key

theorem analyticAt_barnesDoubleZetaRegZero {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x) :
    AnalyticAt ℂ (barnesDoubleZetaRegZero o1 o2 x) 0 := by
  have hzero : (-1 : ℝ) < (0 : ℂ).re := by norm_num
  have hQent : AnalyticAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) 0
      (Set.mem_univ 0)
  have hp2 : AnalyticAt ℂ (fun w : ℂ => ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (w - 2)) 0 := by
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro hcon
    have : (0 : ℂ) = 2 := by linear_combination hcon
    exact absurd this (by norm_num)
  have hp1 : AnalyticAt ℂ
      (fun w : ℂ => barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (w - 1)) 0 := by
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro hcon
    have : (0 : ℂ) = 1 := by linear_combination hcon
    exact absurd this (by norm_num)
  exact (((hp2.add hp1).add (analyticAt_barnesConeDeepPart h1 h2 hx hzero)).mul hQent).add
    (analyticAt_const.mul (analyticAt_analyticSlope hQent))

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The logarithm of the Barnes double gamma.**  The double zeta is regular at `s = 0`, and the
double gamma is defined by `log Gamma_2(x) = ∂_s zeta_2(s,x)|_{s=0}`. -/
def logBarnesDoubleGamma (o1 o2 x : ℝ) : ℂ :=
  deriv (barnesDoubleZetaRegZero o1 o2 x) 0

/-- The value of the continued double zeta at the origin. -/
def barnesDoubleZetaValueZero (o1 o2 x : ℝ) : ℂ := barnesDoubleZetaRegZero o1 o2 x 0

theorem differentiableAt_barnesDoubleZetaRegZero {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) : DifferentiableAt ℂ (barnesDoubleZetaRegZero o1 o2 x) 0 :=
  (analyticAt_barnesDoubleZetaRegZero h1 h2 hx).differentiableAt

end

end GaloisForLFunctions.HTGeometry
