import GaloisForLFunctions.RHTower.DeningerAbelTonelli

/-!
# The pullback is integrable on the ray

The two-sided power decay `‖H_h(y)‖ ≤ C min(y², y^{-2})` makes the pullback integrable on the
positive ray by the same two-branch comparison as its weighted derivative: bounded near the origin,
inverse-square at infinity.

This is what gives the zero-mass statement its shape — the mass of the canonical Möbius preimage is
the harmonic limit times this integral, and the harmonic limit is zero.

* `deningerLogPull_continuousOn` : the pullback is continuous on the ray.
* `deningerLogPull_integrable` : **the pullback is integrable on the ray.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-- The pullback is continuous on the positive ray. -/
theorem deningerLogPull_continuousOn (h : 𝓢(ℝ, ℂ)) :
    ContinuousOn (deningerLogPull h) (Set.Ioi 0) :=
  h.continuous.comp_continuousOn
    (Real.continuousOn_log.mono fun _ hx => ne_of_gt hx)

/-- **The pullback is integrable on the positive ray.** -/
theorem deningerLogPull_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    IntegrableOn (deningerLogPull h) (Set.Ioi 0) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hnear : IntegrableOn (deningerLogPull h) (Set.Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Ioc 0 1) := by
      refine integrableOn_const ?_
      simp
    refine Integrable.mono' hconst
      (((deningerLogPull_continuousOn h).mono
        Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    refine le_trans ((hC u hu0).1) ?_
    have hsq : u ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hfar : IntegrableOn (deningerLogPull h) (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun u : ℝ => C * u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (by norm_num)).mpr (by norm_num)).const_mul C
    refine Integrable.mono' hmaj
      (((deningerLogPull_continuousOn h).mono
        (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    refine le_trans ((hC u hu0).2) (le_of_eq ?_)
    rw [Real.rpow_neg hu0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

end

end RHTower
