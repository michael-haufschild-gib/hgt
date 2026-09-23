import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The weighted space carries no constant

The weighted space of the Hedenmalm pair is `H_k = L²(ℝ, k⁻¹ dx)`.  The theta source decays
exponentially, so its reciprocal grows exponentially and is not integrable; hence no nonzero
constant is square integrable against `k⁻¹`.  This is the reason the closed derivative has
trivial kernel: its formal kernel is exactly the constants.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

theorem not_integrableOn_exp_Ioi :
    ¬ IntegrableOn (fun x : ℝ => Real.exp x) (Ioi (0 : ℝ)) volume := by
  intro h
  set C : ℝ := ∫ x in Ioi (0 : ℝ), Real.exp x with hC
  have hbound : ∀ T : ℝ, 0 ≤ T → Real.exp T - 1 ≤ C := by
    intro T hT
    have hsub : Ioc (0 : ℝ) T ⊆ Ioi (0 : ℝ) := Ioc_subset_Ioi_self
    have hle : (∫ x in Ioc (0 : ℝ) T, Real.exp x) ≤ C := by
      refine setIntegral_mono_set h ?_ (Filter.Eventually.of_forall fun x hx => hsub hx)
      filter_upwards with x
      exact (Real.exp_pos x).le
    have hval : (∫ x in Ioc (0 : ℝ) T, Real.exp x) = Real.exp T - 1 := by
      rw [← intervalIntegral.integral_of_le hT, integral_exp, Real.exp_zero]
    rwa [hval] at hle
  have hlim : Tendsto (fun T : ℝ => Real.exp T - 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) Real.tendsto_exp_atTop
  obtain ⟨T, hT⟩ := (hlim.eventually_gt_atTop C).and (eventually_ge_atTop (0 : ℝ)) |>.exists
  exact absurd (hbound T hT.2) (not_le.mpr hT.1)

theorem not_integrable_exp_abs : ¬ Integrable (fun x : ℝ => Real.exp |x|) (volume : Measure ℝ) := by
  intro h
  refine not_integrableOn_exp_Ioi ?_
  refine (h.integrableOn (s := Ioi (0 : ℝ))).congr_fun (fun x hx => ?_) measurableSet_Ioi
  show Real.exp |x| = Real.exp x
  rw [abs_of_pos hx]

/-- **The reciprocal theta source is not integrable.** -/
theorem not_integrable_inv_thetaSource :
    ¬ Integrable (fun x : ℝ => (thetaCuspFullSource x)⁻¹) (volume : Measure ℝ) := by
  intro h
  refine not_integrable_exp_abs ?_
  have hC : 0 < thetaBound := by
    have h0 := abs_thetaCuspFullSource_le 0
    have hpos := thetaCuspFullSource_pos 0
    rw [abs_of_pos hpos] at h0
    simp only [abs_zero, neg_zero, Real.exp_zero, mul_one] at h0
    show 0 < thetaCuspDerivativeExpConstant 0
    linarith
  refine Integrable.mono' (h.const_mul thetaBound) ?_ ?_
  · exact (Real.continuous_exp.comp continuous_abs).aestronglyMeasurable
  · filter_upwards with x
    have hk := thetaCuspFullSource_pos x
    have hexppos : (0 : ℝ) < Real.exp |x| := Real.exp_pos _
    have hle : thetaCuspFullSource x ≤ thetaBound * Real.exp (-|x|) :=
      le_trans (le_abs_self _) (abs_thetaCuspFullSource_le x)
    have h1 : Real.exp |x| * thetaCuspFullSource x
        ≤ Real.exp |x| * (thetaBound * Real.exp (-|x|)) :=
      mul_le_mul_of_nonneg_left hle hexppos.le
    have h2 : Real.exp |x| * (thetaBound * Real.exp (-|x|)) = thetaBound := by
      rw [show Real.exp |x| * (thetaBound * Real.exp (-|x|))
          = thetaBound * (Real.exp |x| * Real.exp (-|x|)) by ring, ← Real.exp_add]
      simp
    have hmul : Real.exp |x| * thetaCuspFullSource x ≤ thetaBound := by
      rw [h2] at h1
      exact h1
    show ‖Real.exp |x|‖ ≤ thetaBound * (thetaCuspFullSource x)⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg hexppos.le,
      show thetaBound * (thetaCuspFullSource x)⁻¹ = thetaBound / thetaCuspFullSource x from
        (div_eq_mul_inv _ _).symm, le_div_iff₀ hk]
    exact hmul

/-- **No nonzero constant is square integrable against the reciprocal source.**  The formal kernel
of the closed derivative on the weighted space is therefore trivial. -/
theorem not_integrable_const_mul_inv_thetaSource {c : ℝ} (hc : c ≠ 0) :
    ¬ Integrable (fun x : ℝ => c ^ (2 : ℕ) * (thetaCuspFullSource x)⁻¹) (volume : Measure ℝ) := by
  intro h
  refine not_integrable_inv_thetaSource ?_
  have hc2 : (c : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hc
  refine (h.const_mul (c ^ (2 : ℕ))⁻¹).congr ?_
  filter_upwards with x
  show (c ^ (2 : ℕ))⁻¹ * (c ^ (2 : ℕ) * (thetaCuspFullSource x)⁻¹) = (thetaCuspFullSource x)⁻¹
  field_simp

end HedenmalmThetaSource

end

end RHTower
