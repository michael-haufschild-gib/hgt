import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralGammaIntegral
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralFinitePart
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The exponential-integral constant

The two halves of the regularized Gamma integral at the cut add up to the Euler–Mascheroni
constant:

`∫₀¹ (e^{-t} − 1)/t dt + ∫₁^∞ e^{-t}/t dt = −γ`.

For `−1 < a < 0` the regularized Gamma integral splits as `Γ(a) = A(a) + B(a) + 1/a`, where the
two halves are continuous at `a = 0` by dominated convergence, while `Γ(a) − 1/a` is the difference
quotient of `Γ` at `1`, whose limit is `Γ'(1) = −γ`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

/-- The head of the regularized Gamma integral. -/
def gammaHead (a : ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, gammaDefect a t

/-- The tail of the ordinary Gamma integral. -/
def gammaTail (a : ℝ) : ℝ := ∫ t in Ioi (1 : ℝ), Real.exp (-t) * t ^ (a - 1)

/-! ## The split -/

theorem measurable_gammaDefect (a : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS0 : ∀ t ∈ S, 0 < t) :
    AEStronglyMeasurable (gammaDefect a) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).sub continuous_const).continuousOn
  · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem measurable_gammaTailFun (a : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : ∀ t ∈ S, 0 < t) :
    AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hS
  refine ContinuousOn.mul ?_ ?_
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hS0 x hx))

theorem integrableOn_expNeg_Ioi_one : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
  have h := exp_neg_integrableOn_Ioi (1 : ℝ) (b := 1) one_pos
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  norm_num

theorem integrableOn_gammaTailFun {a : ℝ} (ha : a ≤ 1) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 1) := by
  refine Integrable.mono' integrableOn_expNeg_Ioi_one
    (measurable_gammaTailFun a measurableSet_Ioi fun t ht => lt_trans zero_lt_one ht) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have hpow : t ^ (a - 1) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : a - 1 ≤ 0)
    rwa [Real.rpow_zero] at h
  have hpow0 : (0 : ℝ) < t ^ (a - 1) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one ht1) _
  have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hexp, abs_of_pos hpow0]
  nlinarith

theorem integrableOn_rpow_Ioi_one {a : ℝ} (ha : a < 0) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioi 1) :=
  (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)

/-- **The split of the regularized Gamma integral.** -/
theorem gamma_split {a : ℝ} (ha : -1 < a) (ha0 : a < 0) :
    Real.Gamma a = gammaHead a + gammaTail a + 1 / a := by
  have hane : a ≠ 0 := ne_of_lt ha0
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
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro t ⟨-, ht2⟩ ht3
    exact absurd ht3 (not_lt.2 ht2)
  have hsplit : (∫ t in Ioi (0 : ℝ), gammaDefect a t) =
      (∫ t in Ioc (0 : ℝ) 1, gammaDefect a t) + ∫ t in Ioi (1 : ℝ), gammaDefect a t := by
    rw [← setIntegral_union hdisj measurableSet_Ioi (integrableOn_gammaDefect_Ioc ha)
      (integrableOn_gammaDefect_Ioi_one ha0), ← hunion]
  have htail : (∫ t in Ioi (1 : ℝ), gammaDefect a t) = gammaTail a + 1 / a := by
    have hcongr : (∫ t in Ioi (1 : ℝ), gammaDefect a t) =
        ∫ t in Ioi (1 : ℝ), (Real.exp (-t) * t ^ (a - 1) - t ^ (a - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [gammaDefect]
      ring
    rw [hcongr, integral_sub (integrableOn_gammaTailFun (by linarith))
      (integrableOn_rpow_Ioi_one ha0)]
    have hpow : (∫ t in Ioi (1 : ℝ), t ^ (a - 1)) = -1 / a := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      congr 1
      ring
    rw [hpow, gammaTail]
    ring
  rw [← integral_gammaDefect ha ha0, hsplit, htail, gammaHead, ← integral_Ioc_eq_integral_Ioo]
  ring

/-! ## Continuity of the two halves at the cut -/

theorem continuousAt_gammaHead : ContinuousAt gammaHead 0 := by
  refine continuousAt_of_dominated (bound := fun t : ℝ => t ^ (-(1 : ℝ) / 2)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun a =>
      measurable_gammaDefect a measurableSet_Ioo fun t ht => ht.1
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    have haabs : |a| < 1 / 2 := by simpa [Real.dist_eq] using ha
    have halow : -(1 : ℝ) / 2 ≤ a := by
      have := (abs_lt.1 haabs).1
      linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hpow0 : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
    rw [gammaDefect, Real.norm_eq_abs, abs_mul, abs_of_pos hpow0]
    calc |Real.exp (-t) - 1| * t ^ (a - 1) ≤ t * t ^ (a - 1) :=
          mul_le_mul_of_nonneg_right (abs_exp_neg_sub_one_le ht0.le) hpow0.le
      _ = t ^ a := rpow_succ_split ht0 a
      _ ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 halow
  · exact integrableOn_rpow_of_neg_one_lt (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hcomp : ContinuousAt (fun a : ℝ => t ^ (a - 1)) 0 :=
      ContinuousAt.comp (g := fun x : ℝ => t ^ x) (f := fun a : ℝ => a - 1)
        (Real.continuousAt_const_rpow (ne_of_gt ht0)) (continuousAt_id.sub continuousAt_const)
    exact hcomp.const_mul _

theorem continuousAt_gammaTail : ContinuousAt gammaTail 0 := by
  refine continuousAt_of_dominated (bound := fun t : ℝ => Real.exp (-t)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun a =>
      measurable_gammaTailFun a measurableSet_Ioi fun t ht => lt_trans zero_lt_one ht
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    have haabs : |a| < 1 / 2 := by simpa [Real.dist_eq] using ha
    have hahigh : a ≤ 1 := by
      have := (abs_lt.1 haabs).2
      linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have hpow : t ^ (a - 1) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : a - 1 ≤ 0)
      rwa [Real.rpow_zero] at h
    have hpow0 : (0 : ℝ) < t ^ (a - 1) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one ht1) _
    have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hexp, abs_of_pos hpow0]
    nlinarith
  · exact integrableOn_expNeg_Ioi_one
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hcomp : ContinuousAt (fun a : ℝ => t ^ (a - 1)) 0 :=
      ContinuousAt.comp (g := fun x : ℝ => t ^ x) (f := fun a : ℝ => a - 1)
        (Real.continuousAt_const_rpow (ne_of_gt ht0)) (continuousAt_id.sub continuousAt_const)
    exact hcomp.const_mul _

/-! ## The Gamma difference quotient -/

theorem tendsto_gamma_sub_inv :
    Tendsto (fun a : ℝ => Real.Gamma a - 1 / a) (𝓝[≠] (0 : ℝ))
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 Real.hasDerivAt_Gamma_one
  have hmap : Tendsto (fun a : ℝ => a + 1) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun a : ℝ => a + 1) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
        simpa using (continuous_add_const (1 : ℝ)).tendsto (0 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      exact ha (by simpa using (by linarith : a = 0))
  have hcomp := hslope.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hane : a ≠ 0 := by simpa using ha
  show slope Real.Gamma 1 (a + 1) = Real.Gamma a - 1 / a
  rw [slope_def_field, Real.Gamma_one, Real.Gamma_add_one hane, add_sub_cancel_right]
  field_simp

/-- **The exponential-integral constant.** -/
theorem gammaHead_add_gammaTail :
    gammaHead 0 + gammaTail 0 = -Real.eulerMascheroniConstant := by
  have hleft : Tendsto (fun a : ℝ => gammaHead a + gammaTail a) (𝓝[<] (0 : ℝ))
      (𝓝 (gammaHead 0 + gammaTail 0)) :=
    ((continuousAt_gammaHead.add continuousAt_gammaTail).continuousWithinAt (s := Iio 0))
  have hsub : (𝓝[<] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := by
    refine nhdsWithin_mono _ ?_
    intro x hx
    simp only [mem_Iio] at hx
    simp only [mem_compl_iff, mem_singleton_iff]
    exact ne_of_lt hx
  have hright : Tendsto (fun a : ℝ => gammaHead a + gammaTail a) (𝓝[<] (0 : ℝ))
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    refine (tendsto_gamma_sub_inv.mono_left hsub).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 0)] with a ha
    have ha1 : -1 < a := ha.1
    have ha0 : a < 0 := ha.2
    rw [gamma_split ha1 ha0]
    ring
  exact tendsto_nhds_unique hleft hright

end

end GaloisForLFunctions.HTGeometry.Interfinity
