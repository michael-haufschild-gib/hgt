import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaContinuation

/-!
# Holomorphy of the continued Barnes double zeta

The two integrals produced by splitting the Mellin transform at `t = 1` are Mellin transforms of
functions supported in `(0,1]` and in `(1,∞)`.  The first is bounded near the origin and vanishes at
infinity; the second vanishes near the origin and decays exponentially at infinity.  Both therefore
fall under the standard Mellin holomorphy criterion and are analytic on the half-plane `Re s > 0`,
so the continuation of `Gamma(s) zeta_2(s,x)` is an identity of analytic functions and not merely a
pointwise formula.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Mellin transform of a function supported in a measurable subset of the half-line is the
integral over that subset. -/
theorem mellin_indicator_of_subset {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi 0)
    (f : ℝ → ℂ) (s : ℂ) :
    mellin (Set.indicator S f) s = ∫ t in S, (t : ℂ) ^ (s - 1) * f t := by
  rw [mellin]
  have hsm : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • Set.indicator S f t
      = Set.indicator S (fun t => (t : ℂ) ^ (s - 1) * f t) t := by
    intro t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  simp only [hsm]
  rw [MeasureTheory.integral_indicator hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hSsub]

theorem integrableOn_indicator_of_integrableOn {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Ioi 0) {f : ℝ → ℂ} (hf : IntegrableOn f S) :
    IntegrableOn (Set.indicator S f) (Ioi 0) := by
  rw [IntegrableOn, MeasureTheory.integrable_indicator_iff hS]
  rw [IntegrableOn, Measure.restrict_restrict hS, Set.inter_eq_left.mpr hSsub]
  exact hf

theorem locallyIntegrableOn_of_integrableOn_Ioi {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    LocallyIntegrableOn f (Ioi (0 : ℝ)) :=
  fun _ _ => ⟨Ioi 0, self_mem_nhdsWithin, hf⟩

theorem isBigO_indicator_of_eventuallyZero {S : Set ℝ} {f : ℝ → ℂ} {l : Filter ℝ}
    {g : ℝ → ℝ} (h : ∀ᶠ t in l, t ∉ S) : Set.indicator S f =O[l] g := by
  refine Filter.EventuallyEq.trans_isBigO ?_ (isBigO_zero g l)
  filter_upwards [h] with t ht
  exact Set.indicator_of_notMem ht _

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_barnesConeKernelRemainder_Ioc {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) :
    IntegrableOn
      (fun t : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)) (Ioc 0 1) :=
  ((continuousOn_barnesConeKernelRemainder_ofReal h1 h2 x).integrableOn_compact
    isCompact_Icc).mono_set (fun _ ht => ⟨ht.1.le, ht.2⟩)

theorem integrableOn_barnesConeKernel_Ioi_one {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) : IntegrableOn (barnesConeKernel o1 o2 x) (Ioi 1) := by
  have hp1 : 0 < 1 - Real.exp (-o1) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h1 one_pos
  have hp2 : 0 < 1 - Real.exp (-o2) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h2 one_pos
  set c : ℝ := (1 - Real.exp (-o1)) * (1 - Real.exp (-o2)) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn (fun t : ℝ => c⁻¹ * Real.exp (-x * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 hx).const_mul _
  refine Integrable.mono' hdom
    (((continuousOn_barnesConeKernel h1 h2).mono hsub).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hbound := norm_barnesConeKernel_le (x := x) h1 h2 (le_of_lt ht)
  calc ‖barnesConeKernel o1 o2 x t‖ ≤ Real.exp (-x * t) / c := hbound
    _ = c⁻¹ * Real.exp (-x * t) := by rw [div_eq_mul_inv]; ring

theorem isBigO_indicator_barnesConeKernel_atTop {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) :
    Set.indicator (Ioi (1 : ℝ)) (barnesConeKernel o1 o2 x)
      =O[atTop] fun t : ℝ => Real.exp (-x * t) := by
  have hp1 : 0 < 1 - Real.exp (-o1) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h1 one_pos
  have hp2 : 0 < 1 - Real.exp (-o2) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h2 one_pos
  set c : ℝ := (1 - Real.exp (-o1)) * (1 - Real.exp (-o2)) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  refine Asymptotics.isBigO_iff.mpr ⟨c⁻¹, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [Set.indicator_of_mem (mem_Ioi.mpr ht), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖barnesConeKernel o1 o2 x t‖
      ≤ Real.exp (-x * t) / c := norm_barnesConeKernel_le h1 h2 ht.le
    _ = c⁻¹ * Real.exp (-x * t) := by rw [div_eq_mul_inv]; ring

theorem isBigO_indicator_barnesConeKernelRemainder_zero {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) :
    Set.indicator (Ioc (0 : ℝ) 1)
        (fun t : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_bound_barnesConeKernelRemainder h1 h2 x
  refine Asymptotics.isBigO_iff.mpr ⟨max C 0, ?_⟩
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with t ht ht2
  have ht0 : (0 : ℝ) < t := ht
  have htmem : t ∈ Ioc (0 : ℝ) 1 ∨ t ∉ Ioc (0 : ℝ) 1 := em _
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  rcases htmem with hin | hout
  · rw [Set.indicator_of_mem hin]
    exact le_trans (hC t ⟨hin.1.le, hin.2⟩) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hout, norm_zero]
    exact le_max_right _ _

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The subtracted head integral is holomorphic on the right half-plane.** -/
theorem differentiableAt_barnesConeHead {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (w - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)) s := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hfun : (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (w - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
      = mellin (Set.indicator (Ioc (0 : ℝ) 1)
          (fun t : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioc hsub _ w]
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) ?_ ?_ (by linarith) ?_ hs
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioc hsub
        (integrableOn_barnesConeKernelRemainder_Ioc h1 h2 x))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact fun hmem => absurd hmem.2 (not_le.mpr ht)
  · exact isBigO_indicator_barnesConeKernelRemainder_zero h1 h2 x

/-- **The tail integral is holomorphic on the right half-plane.** -/
theorem differentiableAt_barnesConeTail {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesConeKernel o1 o2 x t) s := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hfun : (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesConeKernel o1 o2 x t)
      = mellin (Set.indicator (Ioi (1 : ℝ)) (barnesConeKernel o1 o2 x)) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioi hsub _ w]
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow_exp hx ?_
    (isBigO_indicator_barnesConeKernel_atTop h1 h2) ?_ hs
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioi hsub
        (integrableOn_barnesConeKernel_Ioi_one h1 h2 hx))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact fun hmem => absurd (mem_Ioi.mp hmem) (not_lt.mpr ht.2.le)

/-- **The continued part of the Barnes double zeta is holomorphic on the right half-plane.**  The
two integrals produced by the split are analytic functions of `s` on `Re s > 0`, so the
continuation formula is an identity of analytic functions on `Re s > 2` whose right-hand side is
holomorphic on `Re s > 0` away from `s = 1` and `s = 2`. -/
theorem analyticAt_barnesConeContinuedPart {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ
      (fun w : ℂ => (∫ t in Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (w - 1) * barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * barnesConeKernel o1 o2 x t) s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) ?_ (hopen.mem_nhds hs)
  intro w hw
  exact ((differentiableAt_barnesConeHead h1 h2 x hw).add
    (differentiableAt_barnesConeTail h1 h2 hx hw)).differentiableWithinAt

end

end GaloisForLFunctions.HTGeometry
