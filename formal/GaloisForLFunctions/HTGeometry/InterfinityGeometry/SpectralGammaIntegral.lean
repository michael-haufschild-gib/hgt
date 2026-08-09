import Mathlib

/-!
# The regularized Gamma integral below the cut

For `−1 < a < 0` the Gamma function is the regularized integral

`Γ(a) = ∫₀^∞ (e^{-t} − 1) t^{a-1} dt`,

which converges because the integrand is `O(t^a)` at the origin and `O(t^{a-1})` at infinity.  The
value is obtained by integrating by parts against the primitive `(e^{-t} − 1) t^a / a`, whose
boundary values vanish at both ends, and identifying the remaining integral with `Γ(a+1)/a`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {a : ℝ}

/-- The regularized Gamma integrand. -/
def gammaDefect (a t : ℝ) : ℝ := (Real.exp (-t) - 1) * t ^ (a - 1)

/-- The primitive used in the integration by parts. -/
def gammaPrimitive (a t : ℝ) : ℝ := (Real.exp (-t) - 1) * t ^ a / a

theorem abs_exp_neg_sub_one_le_one {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t) - 1| ≤ 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [abs_le]
  constructor <;> linarith

theorem abs_exp_neg_sub_one_le {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t) - 1| ≤ t := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  rw [abs_le]
  constructor <;> linarith

/-! ## Convergence -/

theorem integrableOn_gammaDefect_Ioc (ha : -1 < a) :
    IntegrableOn (gammaDefect a) (Ioc 0 1) := by
  have hIoo : IntegrableOn (fun t : ℝ => t ^ a) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 ha
  have hdom : IntegrableOn (fun t : ℝ => t ^ a) (Ioc 0 1) :=
    hIoo.congr_set_ae (Ioo_ae_eq_Ioc).symm
  refine Integrable.mono' hdom ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ ?_
    · exact ((Real.continuous_exp.comp continuous_neg).sub continuous_const).continuousOn
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hw : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
    have hsplit : t * t ^ (a - 1) = t ^ a := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [gammaDefect, Real.norm_eq_abs, abs_mul, abs_of_pos hw, ← hsplit]
    exact mul_le_mul_of_nonneg_right (abs_exp_neg_sub_one_le ht0.le) hw.le

theorem integrableOn_gammaDefect_Ioi_one (ha0 : a < 0) :
    IntegrableOn (gammaDefect a) (Ioi 1) := by
  have hdom : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)
  refine Integrable.mono' hdom ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact ((Real.continuous_exp.comp continuous_neg).sub continuous_const).continuousOn
    · exact continuousOn_id.rpow_const fun x hx =>
        Or.inl (ne_of_gt (lt_trans zero_lt_one (mem_Ioi.1 hx)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.1 ht)
    have hw : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
    rw [gammaDefect, Real.norm_eq_abs, abs_mul, abs_of_pos hw]
    calc |Real.exp (-t) - 1| * t ^ (a - 1) ≤ 1 * t ^ (a - 1) :=
          mul_le_mul_of_nonneg_right (abs_exp_neg_sub_one_le_one ht0.le) hw.le
      _ = t ^ (a - 1) := one_mul _

theorem integrableOn_gammaDefect (ha : -1 < a) (ha0 : a < 0) :
    IntegrableOn (gammaDefect a) (Ioi 0) := by
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  rw [hunion]
  exact (integrableOn_gammaDefect_Ioc ha).union (integrableOn_gammaDefect_Ioi_one ha0)

theorem integrableOn_gammaTail (ha : -1 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ a / a) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  simp only [add_sub_cancel_right] at h
  exact h.div_const a

/-! ## Integration by parts -/

theorem gammaPrimitive_zero (ha0 : a ≠ 0) : gammaPrimitive a 0 = 0 := by
  rw [gammaPrimitive, Real.zero_rpow ha0]
  simp

theorem hasDerivAt_gammaPrimitive (ha0 : a ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gammaPrimitive a) (gammaDefect a t - Real.exp (-t) * t ^ a / a) t := by
  have hu : HasDerivAt (fun x : ℝ => Real.exp (-x) - 1) (-Real.exp (-t)) t := by
    have h1 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) t := hasDerivAt_neg t
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := h1.exp
    simpa using h2.sub_const 1
  have hv : HasDerivAt (fun x : ℝ => x ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
  have hprod := hu.mul hv
  have hdiv := hprod.div_const a
  have heq : (-Real.exp (-t) * t ^ a + (Real.exp (-t) - 1) * (a * t ^ (a - 1))) / a =
      gammaDefect a t - Real.exp (-t) * t ^ a / a := by
    rw [gammaDefect]
    field_simp
    ring
  rw [heq] at hdiv
  exact hdiv

theorem continuousWithinAt_gammaPrimitive (ha : -1 < a) (ha0 : a ≠ 0) :
    ContinuousWithinAt (gammaPrimitive a) (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, gammaPrimitive_zero ha0]
  have hc : ContinuousAt (fun t : ℝ => t ^ (a + 1)) 0 :=
    Real.continuousAt_rpow_const 0 (a + 1) (Or.inr (by linarith))
  have h1 : Tendsto (fun t : ℝ => t ^ (a + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hct := hc.tendsto
    rw [Real.zero_rpow (by linarith : a + 1 ≠ 0)] at hct
    exact hct.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => t ^ (a + 1) / |a|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h1.div_const |a|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hw : (0 : ℝ) < t ^ a := Real.rpow_pos_of_pos ht0 _
  have hsplit : t * t ^ a = t ^ (a + 1) := by
    nth_rewrite 1 [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [gammaPrimitive, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hw, ← hsplit]
  gcongr
  exact abs_exp_neg_sub_one_le ht0.le

theorem tendsto_gammaPrimitive_atTop (ha0 : a < 0) :
    Tendsto (gammaPrimitive a) atTop (𝓝 0) := by
  have hbound : ∀ᶠ t in atTop, ‖gammaPrimitive a t‖ ≤ t ^ a / |a| := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hw : (0 : ℝ) < t ^ a := Real.rpow_pos_of_pos ht _
    have hane : a ≠ 0 := ne_of_lt ha0
    have habs : (0 : ℝ) < |a| := abs_pos.2 hane
    rw [gammaPrimitive, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hw]
    gcongr
    all_goals first
      | assumption
      | positivity
      | nlinarith [abs_exp_neg_sub_one_le_one ht.le, hw.le, abs_nonneg (Real.exp (-t) - 1)]
  have hlim : Tendsto (fun t : ℝ => t ^ a / |a|) atTop (𝓝 0) := by
    have hneg := tendsto_rpow_neg_atTop (y := -a) (by linarith)
    simp only [neg_neg] at hneg
    simpa using hneg.div_const |a|
  exact squeeze_zero_norm' hbound hlim

/-- **The regularized Gamma integral.** -/
theorem integral_gammaDefect (ha : -1 < a) (ha0 : a < 0) :
    (∫ t in Ioi (0 : ℝ), gammaDefect a t) = Real.Gamma a := by
  have hane : a ≠ 0 := ne_of_lt ha0
  have hint1 := integrableOn_gammaDefect ha ha0
  have hint2 := integrableOn_gammaTail ha
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_gammaPrimitive ha hane)
    (fun x hx => hasDerivAt_gammaPrimitive hane hx)
    (hint1.sub hint2) (tendsto_gammaPrimitive_atTop ha0)
  rw [gammaPrimitive_zero hane, sub_zero, integral_sub hint1 hint2] at hmain
  have hG : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ a / a) = Real.Gamma (a + 1) / a := by
    rw [integral_div]
    congr 1
    rw [Real.Gamma_eq_integral (by linarith : (0 : ℝ) < a + 1)]
    simp only [add_sub_cancel_right]
  rw [hG, Real.Gamma_add_one hane] at hmain
  have hval : a * Real.Gamma a / a = Real.Gamma a := by
    field_simp
  rw [hval] at hmain
  linarith

end

end GaloisForLFunctions.HTGeometry.Interfinity
