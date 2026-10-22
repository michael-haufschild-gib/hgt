import GaloisForLFunctions.RHTower.Deninger.DeningerLogPullDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The first weighted moment of the pullback derivative

The weighted derivative `u H_h'(u)` equals `h'(log u)` and so decays like `min(u², u^{-2})`.  Near
the origin it is therefore bounded and the interval has finite measure; near infinity it is
dominated by `u^{-2}`.  Hence

`∫_0^∞ u |H_h'(u)| du < ∞`,

which is the second factor of the `L¹` estimate for the canonical Möbius preimage.

* `deningerWeightedMoment_continuousOn` : the integrand is continuous on the ray.
* `deningerWeightedMoment_integrable` : **the first weighted moment is finite.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-- The integrand of the first weighted moment. -/
def deningerWeightedMomentFun (h : 𝓢(ℝ, ℂ)) (u : ℝ) : ℝ := u * ‖deningerLogPullDeriv h u‖

theorem deningerWeightedMomentFun_nonneg (h : 𝓢(ℝ, ℂ)) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ deningerWeightedMomentFun h u :=
  mul_nonneg hu (norm_nonneg _)

/-- The integrand is continuous on the positive ray. -/
theorem deningerWeightedMoment_continuousOn (h : 𝓢(ℝ, ℂ)) :
    ContinuousOn (deningerWeightedMomentFun h) (Set.Ioi 0) := by
  have hderiv : Continuous (deriv (h : ℝ → ℂ)) := h.smooth'.continuous_deriv (by simp)
  refine ContinuousOn.mul continuousOn_id ?_
  refine ContinuousOn.norm ?_
  refine ContinuousOn.mul ?_ ?_
  · exact hderiv.comp_continuousOn (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx))
  · have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt hx)
    exact Complex.continuous_ofReal.comp_continuousOn hinv

/-- **The first weighted moment is finite.** -/
theorem deningerWeightedMoment_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    IntegrableOn (deningerWeightedMomentFun h) (Set.Ioi 0) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPullDeriv_weighted_norm_le hh
  have hmeas : AEStronglyMeasurable (deningerWeightedMomentFun h)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (deningerWeightedMoment_continuousOn h).aestronglyMeasurable measurableSet_Ioi
  have hnear : IntegrableOn (deningerWeightedMomentFun h) (Set.Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Ioc 0 1) := by
      refine integrableOn_const ?_
      simp
    refine Integrable.mono' hconst
      (((deningerWeightedMoment_continuousOn h).mono
        Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : (0 : ℝ) < u := hu.1
      have hu1 : u ≤ 1 := hu.2
      rw [Real.norm_of_nonneg (deningerWeightedMomentFun_nonneg h hu0.le)]
      refine le_trans ((hC u hu0).1) ?_
      have hsq : u ^ 2 ≤ 1 := by nlinarith
      nlinarith
  have hfar : IntegrableOn (deningerWeightedMomentFun h) (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun u : ℝ => C * u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (by norm_num)).mpr (by norm_num)).const_mul C
    refine Integrable.mono' hmaj
      (((deningerWeightedMoment_continuousOn h).mono
        (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : (1 : ℝ) < u := hu
      have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
      rw [Real.norm_of_nonneg (deningerWeightedMomentFun_nonneg h hu0.le)]
      refine le_trans ((hC u hu0).2) (le_of_eq ?_)
      rw [Real.rpow_neg hu0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, ← div_eq_mul_inv]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

end

end RHTower
