import GaloisForLFunctions.HTGeometry.PowerTailIntegral
import Mathlib.Analysis.Calculus.LHopital

/-!
# Asymptotics of integrable power tails

A continuous integrable profile with exact pointwise power asymptotic has the corresponding exact
tail-integral asymptotic.  The proof differentiates the moving-endpoint integral and applies the
zero-over-zero form of L'Hôpital's rule at infinity.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem integral_Ioi_eq_sub_real {f : ℝ → ℝ} {c u : ℝ} (hcu : c ≤ u)
    (hint : IntegrableOn f (Ioi c) volume) :
    (∫ t in Ioi u, f t) = (∫ t in Ioi c, f t) - ∫ t in c..u, f t := by
  have hsplit : Ioi c = Ioc c u ∪ Ioi u := by
    ext t
    constructor
    · intro ht
      rcases le_or_gt t u with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact lt_of_le_of_lt hcu h
  have hdisj : Disjoint (Ioc c u) (Ioi u) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht2⟩ ht3
    exact absurd ht3 (not_lt.mpr ht2)
  have hunion : (∫ t in Ioi c, f t) =
      (∫ t in Ioc c u, f t) + ∫ t in Ioi u, f t := by
    rw [hsplit]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_left))
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_right))
  rw [intervalIntegral.integral_of_le hcu, hunion]
  ring

private theorem hasDerivAt_integral_Ioi_real {f : ℝ → ℝ} {c y : ℝ}
    (hcy : c < y) (hint : IntegrableOn f (Ioi c) volume)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 y) volume)
    (hcont : ContinuousAt f y) :
    HasDerivAt (fun u : ℝ => ∫ t in Ioi u, f t) (-f y) y := by
  have hII : IntervalIntegrable f volume c y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcy.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt
      (fun u : ℝ => (∫ t in Ioi c, f t) - ∫ t in c..u, f t) (-f y) y := by
    have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas hcont
    simpa using hbase.const_sub (∫ t in Ioi c, f t)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcy] with u hu
  exact integral_Ioi_eq_sub_real (le_of_lt hu) hint

private theorem tendsto_integral_Ioi_atTop_zero_real {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Tendsto (fun T : ℝ => ∫ x in Ioi T, f x) atTop (𝓝 0) := by
  have hmeas : ∀ T : ℝ, AEStronglyMeasurable ((Ioi T).indicator f) volume :=
    fun T => hf.aestronglyMeasurable.indicator measurableSet_Ioi
  have hbound : ∀ T : ℝ, ∀ᵐ x : ℝ, ‖(Ioi T).indicator f x‖ ≤ ‖f x‖ := by
    intro T
    filter_upwards with x
    exact norm_indicator_le_norm_self f x
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun T : ℝ => (Ioi T).indicator f x) atTop (𝓝 0) := by
    filter_upwards with x
    have hev : ∀ᶠ T : ℝ in atTop, (Ioi T).indicator f x = 0 := by
      filter_upwards [eventually_gt_atTop x] with T hT
      exact Set.indicator_of_notMem
        (by simpa only [Set.mem_Ioi, not_lt] using hT.le) f
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  simpa only [integral_indicator measurableSet_Ioi, integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound)
      hf.norm hlim

/-- Pointwise power asymptotics transfer to exact moving-endpoint tail-integral asymptotics. -/
theorem tendsto_tailIntegral_div_rpow_of_tendsto_rpow_mul
    {f : ℝ → ℝ} {p c : ℝ} (hp : 1 < p)
    (hfC : Continuous f) (hf : Integrable f volume)
    (hasymp : Tendsto (fun x : ℝ => x ^ p * f x) atTop (𝓝 c)) :
    Tendsto (fun x : ℝ => (∫ y in Ioi x, f y) / x ^ (1 - p))
      atTop (𝓝 (c / (p - 1))) := by
  apply HasDerivAt.lhopital_zero_atTop_on_Ioi (a := 1)
      (f' := fun x => -f x) (g' := fun x => (1 - p) * x ^ (-p))
  · intro x hx
    exact hasDerivAt_integral_Ioi_real hx hf.integrableOn
      (hfC.stronglyMeasurableAtFilter volume (𝓝 x)) hfC.continuousAt
  · intro x hx
    convert Real.hasDerivAt_rpow_const (x := x) (p := 1 - p)
      (Or.inl (ne_of_gt (lt_trans zero_lt_one hx))) using 1
    ring_nf
  · intro x hx
    exact mul_ne_zero (sub_ne_zero.mpr (by linarith))
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _).ne'
  · exact tendsto_integral_Ioi_atTop_zero_real hf
  · have h := tendsto_rpow_neg_atTop (show 0 < p - 1 by linarith)
    simpa only [show 1 - p = -(p - 1) by ring] using h
  · have h := hasymp.div_const (p - 1)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le]
    rw [show 1 - p = -(p - 1) by ring, neg_mul, neg_div_neg_eq]
    field_simp [(Real.rpow_pos_of_pos hx p).ne',
      (show p - 1 ≠ 0 by linarith)]

end

end GaloisForLFunctions.HTGeometry
