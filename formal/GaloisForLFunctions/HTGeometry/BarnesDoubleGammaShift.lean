import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaShiftEquation

/-!
# The shift equation of the Barnes double gamma

The shift equation of the continued double zeta holds off the origin, where the regularized and the
raw continuations agree.  Both sides are analytic at the origin, so the identity extends there by
uniqueness of limits, and differentiating in `s` gives

```text
log Gamma_2(x) = log Gamma_2(x + omega_1) + log Gamma_1(omega_2; x).
```

This is the functional equation the double sine is built from: the ratio of double gammas across a
period is a one-dimensional gamma, whose reflection is the sine.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem differentiableAt_barnesRayTail_all {o x : ℝ} (ho : 0 < o) (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesRayKernel o x t) s := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hfun : (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesRayKernel o x t)
      = mellin (Set.indicator (Ioi (1 : ℝ)) (barnesRayKernel o x)) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioi hsub _ w]
  have htop : Set.indicator (Ioi (1 : ℝ)) (barnesRayKernel o x)
      =O[atTop] fun t : ℝ => Real.exp (-x * t) := by
    have hp : 0 < 1 - Real.exp (-o) := by
      simpa using one_sub_exp_neg_mul_ofReal_pos ho one_pos
    refine Asymptotics.isBigO_iff.mpr ⟨(1 - Real.exp (-o))⁻¹, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [Set.indicator_of_mem (mem_Ioi.mpr ht), Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc ‖barnesRayKernel o x t‖ ≤ Real.exp (-x * t) / (1 - Real.exp (-o)) :=
          norm_barnesRayKernel_le ho ht.le
      _ = (1 - Real.exp (-o))⁻¹ * Real.exp (-x * t) := by rw [div_eq_mul_inv]; ring
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow_exp (b := s.re - 1) hx ?_ htop ?_ (by linarith)
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioi hsub
        (by simpa using integrableOn_cpow_mul_barnesRayKernel_Ioi_one_all ho hx 1))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact fun hmem => absurd (mem_Ioi.mp hmem) (not_lt.mpr ht.2.le)

theorem isBigO_indicator_barnesRayRemainder_zero {o : ℝ} (ho : 0 < o) (x : ℝ) :
    Set.indicator (Ioc (0 : ℝ) 1)
        (fun t : ℝ => barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesRayRemainder ho x
  refine Asymptotics.isBigO_iff.mpr ⟨max C 0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  by_cases hin : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hin]
    exact le_trans (hC t ⟨hin.1.le, hin.2⟩) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hin, norm_zero]
    exact le_max_right _ _

theorem differentiableAt_barnesRayDeepHead {o : ℝ} (ho : 0 < o) (x : ℝ) {s : ℂ}
    (hs : -1 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w + 1 - 1) *
        barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)) s := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hfun : (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w + 1 - 1) *
        barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))
      = (fun w : ℂ => mellin (Set.indicator (Ioc (0 : ℝ) 1)
          (fun t : ℝ => barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))) w) ∘ (fun w : ℂ => w + 1) := by
    funext w
    rw [Function.comp_apply, mellin_indicator_of_subset measurableSet_Ioc hsub _ (w + 1)]
  rw [hfun]
  have hshift : (0 : ℝ) < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  refine DifferentiableAt.comp s ?_ (differentiableAt_id.add_const 1)
  refine mellin_differentiableAt_of_isBigO_rpow (a := (s + 1).re + 1) (b := 0) ?_ ?_
    (by linarith) ?_ hshift
  · have hcont : ContinuousOn
        (fun u : ℝ => barnesRayRemainder (o : ℂ) (x : ℂ) (u : ℂ)) (Icc 0 1) :=
      fun _ ht => (continuousAt_barnesRayRemainder_ofReal ho x ht.1).continuousWithinAt
    exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioc hsub
        ((hcont.integrableOn_compact isCompact_Icc).mono_set (fun _ ht => ⟨ht.1.le, ht.2⟩)))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact fun hmem => absurd hmem.2 (not_le.mpr ht)
  · exact isBigO_indicator_barnesRayRemainder_zero ho x

theorem analyticAt_barnesRayDeepPart {o x : ℝ} (ho : 0 < o) (hx : 0 < x) {s : ℂ}
    (hs : -1 < s.re) : AnalyticAt ℂ (barnesRayDeepPart o x) s := by
  have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  refine DifferentiableOn.analyticAt (s := {w : ℂ | -1 < w.re}) ?_ (hopen.mem_nhds hs)
  intro w hw
  exact ((differentiableAt_barnesRayDeepHead ho x hw).add
    (differentiableAt_barnesRayTail_all ho hx w)).differentiableWithinAt

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The regularization of the continued one-dimensional zeta at the origin. -/
def barnesSingleZetaRegZero (o x : ℝ) (s : ℂ) : ℂ :=
  ((o : ℂ)⁻¹ / (s - 1) + barnesRayDeepPart o x s) * (Complex.Gamma s)⁻¹
    + barnesRayLinearCoeff (o : ℂ) (x : ℂ)
        * analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s

theorem barnesSingleZetaRegZero_eq {o x : ℝ} {s : ℂ} (hs : s ≠ 0) :
    barnesSingleZetaRegZero o x s = barnesSingleZetaDeep o x s := by
  have hG0 : (Complex.Gamma (0 : ℂ))⁻¹ = 0 := by rw [Complex.Gamma_zero, inv_zero]
  have hslope := sub_eq_mul_analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s
  simp only [hG0, sub_zero] at hslope
  rw [barnesSingleZetaRegZero, barnesSingleZetaDeep, barnesSingleZetaBracket]
  set Qs : ℂ := (Complex.Gamma s)⁻¹ with hQs
  set σ : ℂ := analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s with hσ
  have hQ : Qs = s * σ := by rw [hQs, hσ]; linear_combination hslope
  have key : barnesRayLinearCoeff (o : ℂ) (x : ℂ) / s * Qs
      = barnesRayLinearCoeff (o : ℂ) (x : ℂ) * σ := by
    rw [hQ]
    field_simp
  linear_combination -key

theorem analyticAt_barnesSingleZetaRegZero {o x : ℝ} (ho : 0 < o) (hx : 0 < x) :
    AnalyticAt ℂ (barnesSingleZetaRegZero o x) 0 := by
  have hzero : (-1 : ℝ) < (0 : ℂ).re := by norm_num
  have hQent : AnalyticAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) 0
      (Set.mem_univ 0)
  have hp1 : AnalyticAt ℂ (fun w : ℂ => (o : ℂ)⁻¹ / (w - 1)) 0 := by
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro hcon
    have : (0 : ℂ) = 1 := by linear_combination hcon
    exact absurd this (by norm_num)
  exact ((hp1.add (analyticAt_barnesRayDeepPart ho hx hzero)).mul hQent).add
    (analyticAt_const.mul (analyticAt_analyticSlope hQent))

/-- **The logarithm of the one-dimensional Barnes gamma.** -/
def logBarnesSingleGamma (o x : ℝ) : ℂ := deriv (barnesSingleZetaRegZero o x) 0

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 800000 in
/-- **The shift equation of the regularized zetas holds on a neighbourhood of the origin.** -/
theorem barnesRegZero_shift_eventually {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x) :
    (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 x s)
      =ᶠ[𝓝 (0 : ℂ)] fun s : ℂ => barnesDoubleZetaRegZero o1 o2 (x + o1) s
        + barnesSingleZetaRegZero o2 x s := by
  have hx1 : 0 < x + o1 := by linarith
  have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hmem : {w : ℂ | -1 < w.re} ∈ 𝓝 (0 : ℂ) := hopen.mem_nhds (by norm_num)
  have hpunct : (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 x s)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun s : ℂ => barnesDoubleZetaRegZero o1 o2 (x + o1) s
        + barnesSingleZetaRegZero o2 x s := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with s hs hs'
    have hsne : s ≠ 0 := hs
    rw [barnesDoubleZetaRegZero_eq hsne, barnesDoubleZetaRegZero_eq hsne,
      barnesSingleZetaRegZero_eq hsne]
    exact barnesDoubleZetaDeep_shift h1 h2 hx hs'
  have hL : ContinuousAt (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 x s) 0 :=
    (analyticAt_barnesDoubleZetaRegZero h1 h2 hx).continuousAt
  have hR : ContinuousAt (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 (x + o1) s
      + barnesSingleZetaRegZero o2 x s) 0 :=
    ((analyticAt_barnesDoubleZetaRegZero h1 h2 hx1).add
      (analyticAt_barnesSingleZetaRegZero h2 hx)).continuousAt
  have hval : barnesDoubleZetaRegZero o1 o2 x 0
      = barnesDoubleZetaRegZero o1 o2 (x + o1) 0 + barnesSingleZetaRegZero o2 x 0 := by
    have t1 : Filter.Tendsto (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 x s) (𝓝[≠] (0 : ℂ))
        (𝓝 (barnesDoubleZetaRegZero o1 o2 x 0)) := hL.continuousWithinAt.tendsto
    have t2 : Filter.Tendsto (fun s : ℂ => barnesDoubleZetaRegZero o1 o2 x s) (𝓝[≠] (0 : ℂ))
        (𝓝 (barnesDoubleZetaRegZero o1 o2 (x + o1) 0 + barnesSingleZetaRegZero o2 x 0)) :=
      (hR.continuousWithinAt.tendsto).congr' hpunct.symm
    exact tendsto_nhds_unique t1 t2
  rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (0 : ℂ), Filter.eventually_sup]
  exact ⟨hpunct, by simpa using hval⟩

/-- **The shift equation of the Barnes double gamma.**  Shifting the argument by a period peels off
the one-dimensional gamma of the other period. -/
theorem logBarnesDoubleGamma_shift {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x) :
    logBarnesDoubleGamma o1 o2 x
      = logBarnesDoubleGamma o1 o2 (x + o1) + logBarnesSingleGamma o2 x := by
  have hx1 : 0 < x + o1 := by linarith
  have hdiffD : DifferentiableAt ℂ (barnesDoubleZetaRegZero o1 o2 (x + o1)) 0 :=
    (analyticAt_barnesDoubleZetaRegZero h1 h2 hx1).differentiableAt
  have hdiffS : DifferentiableAt ℂ (barnesSingleZetaRegZero o2 x) 0 :=
    (analyticAt_barnesSingleZetaRegZero h2 hx).differentiableAt
  have hderiv := (barnesRegZero_shift_eventually h1 h2 hx).deriv_eq
  rw [logBarnesDoubleGamma, hderiv, logBarnesDoubleGamma, logBarnesSingleGamma]
  exact (hdiffD.hasDerivAt.add hdiffS.hasDerivAt).deriv

end

end GaloisForLFunctions.HTGeometry
