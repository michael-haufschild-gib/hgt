import GaloisForLFunctions.RHTower.PaperThetaCutBranches
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous

/-! # Absolute continuity of both unconditional theta branches

The actual integrable branch derivatives supply their interval primitives.
An increment comparison then transfers absolute continuity to confluent modes.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint

theorem absolutelyContinuous_of_increment_comparison
    {f g : ℝ → ℂ} {a b K : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b,
      ‖f x-f y‖ ≤ K*‖g x-g y‖) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg ⊢
  have hlim := hg.const_mul K
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg fun _ _ => dist_nonneg) _ hlim
  have hmem : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hmem] with E hE
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [dist_eq_norm] using hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

private theorem absolutelyContinuous_of_native_derivative
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (deriv f x) x)
    (hi : IntervalIntegrable (deriv f) volume a b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hp := GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
    hi (c := a) (by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
  have hk : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hp.fun_add hk).congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hs : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hix : IntervalIntegrable (deriv f) volume a x := hi.mono_set (by
    simpa only [uIcc_of_le hx.1, uIcc_of_le hab] using hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hc.mono hs)
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩) hix
  change (∫ v in a..x, deriv f v)+f a = f x
  rw [he]
  exact sub_add_cancel _ _

theorem absolutelyContinuousOnInterval_closedQuantileMode_right
    (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (closedQuantileMode z) c.val 1 := by
  apply absolutelyContinuous_of_native_derivative c.property.2.le
    (continuousOn_closedQuantileMode_right z c) _
    (intervalIntegrable_deriv_closedQuantileMode_right z c)
  intro t ht
  exact (differentiableAt_closedQuantileMode z
    ⟨t, c.property.1.trans ht.1, ht.2⟩).hasDerivAt

theorem absolutelyContinuousOnInterval_leftClosedQuantileMode
    (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (leftClosedQuantileMode z) 0 c.val := by
  apply absolutelyContinuous_of_native_derivative c.property.1.le
    (continuousOn_leftClosedQuantileMode z c) _
    (intervalIntegrable_deriv_leftClosedQuantileMode z c)
  intro t ht
  exact (differentiableAt_leftClosedQuantileMode z
    ⟨t, ht.1, ht.2.trans c.property.2⟩).hasDerivAt

end RHTower.PaperThetaEndpoint
