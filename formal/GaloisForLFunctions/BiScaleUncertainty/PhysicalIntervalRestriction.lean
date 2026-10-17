import GaloisForLFunctions.BiScaleUncertainty.PhysicalTranslation

/-!
# Physical interval restrictions and the visible positive component

Measurable restriction constructs linear contractions on physical L². The
positive component has exactly the original logarithmic primitive; bounded
positive intervals provide integrable truncations with explicit primitive tails.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

private def restrictedVelocity (s : Set ℝ) (hs : MeasurableSet s) (q : Velocity) : Velocity :=
  (MemLp.indicator hs (Lp.memLp q)).toLp (s.indicator (q : ℝ → ℝ))

private theorem ae_restrictedVelocity (s : Set ℝ) (hs : MeasurableSet s) (q : Velocity) :
    restrictedVelocity s hs q =ᵐ[volume] s.indicator (q : ℝ → ℝ) := MemLp.coeFn_toLp _

private theorem norm_sq_restrictedVelocity (s : Set ℝ) (hs : MeasurableSet s) (q : Velocity) :
    ‖restrictedVelocity s hs q‖^2 = ∫ t in s, (q t)^2 := by
  rw [norm_sq_velocity, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [ae_restrictedVelocity s hs q] with t ht
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

private theorem norm_restrictedVelocity_le (s : Set ℝ) (hs : MeasurableSet s) (q : Velocity) :
    ‖restrictedVelocity s hs q‖ ≤ ‖q‖ := by
  have he : ‖restrictedVelocity s hs q‖^2 ≤ ‖q‖^2 := by
    rw [norm_sq_restrictedVelocity, norm_sq_velocity]
    exact setIntegral_le_integral (integrable_velocity_sq q)
      (Filter.Eventually.of_forall (fun t => sq_nonneg (q t)))
  nlinarith only [he, norm_nonneg (restrictedVelocity s hs q), norm_nonneg q]

private def physicalRestriction (s : Set ℝ) (hs : MeasurableSet s) : Velocity →L[ℝ] Velocity :=
  ({ toFun := restrictedVelocity s hs
     map_add' := by
       intro q r
       apply Lp.ext
       filter_upwards [ae_restrictedVelocity s hs (q+r), ae_restrictedVelocity s hs q,
         ae_restrictedVelocity s hs r, Lp.coeFn_add q r,
         Lp.coeFn_add (restrictedVelocity s hs q) (restrictedVelocity s hs r)] with t ht hq hr hi ho
       simp only [Pi.add_apply] at hi ho
       rw [ht, ho, hq, hr]
       by_cases hm : t ∈ s
       · simpa only [indicator_of_mem hm] using hi
       · simp only [indicator_of_notMem hm, zero_add]
     map_smul' := by
       intro c q
       change restrictedVelocity s hs (c • q) = c • restrictedVelocity s hs q
       apply Lp.ext
       filter_upwards [ae_restrictedVelocity s hs (c • q), ae_restrictedVelocity s hs q,
         Lp.coeFn_smul c q, Lp.coeFn_smul c (restrictedVelocity s hs q)] with t ht hq hi ho
       simp only [Pi.smul_apply, smul_eq_mul] at hi ho
       rw [ht, ho, hq]
       by_cases hm : t ∈ s
       · simpa only [indicator_of_mem hm] using hi
       · simp only [indicator_of_notMem hm, mul_zero] } : Velocity →ₗ[ℝ] Velocity).mkContinuous 1
    (fun q => by
      change ‖restrictedVelocity s hs q‖ ≤ 1*‖q‖
      simpa only [one_mul] using norm_restrictedVelocity_le s hs q)

def physicalIntervalRestriction (a b : ℝ) : Velocity →L[ℝ] Velocity :=
  physicalRestriction (Ioc a b) measurableSet_Ioc

def positivePhysicalVelocity : Velocity →L[ℝ] Velocity :=
  physicalRestriction (Ioi 0) measurableSet_Ioi

theorem ae_physicalIntervalRestriction (a b : ℝ) (q : Velocity) :
    physicalIntervalRestriction a b q =ᵐ[volume] (Ioc a b).indicator (q : ℝ → ℝ) :=
  ae_restrictedVelocity _ measurableSet_Ioc q

theorem ae_positivePhysicalVelocity (q : Velocity) :
    positivePhysicalVelocity q =ᵐ[volume] (Ioi (0 : ℝ)).indicator (q : ℝ → ℝ) :=
  ae_restrictedVelocity _ measurableSet_Ioi q

theorem norm_sq_physicalIntervalRestriction (a b : ℝ) (q : Velocity) :
    ‖physicalIntervalRestriction a b q‖^2 = ∫ t in Ioc a b, (q t)^2 :=
  norm_sq_restrictedVelocity _ measurableSet_Ioc q

theorem norm_sq_positivePhysicalVelocity (q : Velocity) :
    ‖positivePhysicalVelocity q‖^2 = ∫ t in Ioi (0 : ℝ), (q t)^2 :=
  norm_sq_restrictedVelocity _ measurableSet_Ioi q

theorem norm_physicalIntervalRestriction_le (a b : ℝ) (q : Velocity) :
    ‖physicalIntervalRestriction a b q‖ ≤ ‖q‖ := norm_restrictedVelocity_le _ measurableSet_Ioc q

theorem norm_positivePhysicalVelocity_le (q : Velocity) :
    ‖positivePhysicalVelocity q‖ ≤ ‖q‖ := norm_restrictedVelocity_le _ measurableSet_Ioi q

theorem positivePhysicalVelocity_eq_sub_negative (q : Velocity) :
    positivePhysicalVelocity q = q-negativePhysicalVelocity q := by
  apply Lp.ext
  filter_upwards [ae_positivePhysicalVelocity q, ae_negativePhysicalVelocity q,
    Lp.coeFn_sub q (negativePhysicalVelocity q)] with t hp hn hs
  simp only [Pi.sub_apply] at hs
  rw [hp, hs, hn]
  by_cases h : 0 < t
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

theorem primitive_positivePhysicalVelocity (q : Velocity) (t : ℝ) (ht : 0 ≤ t) :
    primitive (positivePhysicalVelocity q) t = primitive q t := by
  simp only [primitive, intervalIntegral.integral_of_le ht]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_positivePhysicalVelocity q),
    ae_restrict_mem (measurableSet_Ioc (a := (0 : ℝ)) (b := t))] with u hu hs
  rw [hu]
  exact indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hs.1) _

theorem logPrimitive_positivePhysicalVelocity (q : Velocity) (x : ℝ) :
    logPrimitive (positivePhysicalVelocity q) x = logPrimitive q x :=
  primitive_positivePhysicalVelocity q (Real.exp x) (Real.exp_pos x).le

theorem positivePhysicalVelocity_idempotent (q : Velocity) :
    positivePhysicalVelocity (positivePhysicalVelocity q) = positivePhysicalVelocity q := by
  apply Lp.ext
  filter_upwards [ae_positivePhysicalVelocity (positivePhysicalVelocity q),
    ae_positivePhysicalVelocity q] with t ht hq
  rw [ht]
  by_cases hm : t ∈ Ioi (0 : ℝ)
  · exact indicator_of_mem hm _
  · rw [indicator_of_notMem hm, hq, indicator_of_notMem hm]

theorem integrable_physicalIntervalRestriction (a b : ℝ) (q : Velocity) :
    Integrable (physicalIntervalRestriction a b q : ℝ → ℝ) := by
  have hi : IntegrableOn (q : ℝ → ℝ) (Ioc a b) volume :=
    integrableOn_Lp_of_measure_ne_top q (by norm_num) measure_Ioc_lt_top.ne
  exact (hi.integrable_indicator measurableSet_Ioc).congr
    (ae_physicalIntervalRestriction a b q).symm

theorem integral_physicalIntervalRestriction (a b : ℝ) (q : Velocity) :
    (∫ t, physicalIntervalRestriction a b q t) = ∫ t in Ioc a b, q t := by
  rw [← integral_indicator measurableSet_Ioc]
  exact integral_congr_ae (ae_physicalIntervalRestriction a b q)

theorem primitive_physicalIntervalRestriction_left (a b : ℝ) (q : Velocity)
    (ha : 0 ≤ a) (t : ℝ) (ht : t ≤ a) :
    primitive (physicalIntervalRestriction a b q) t = 0 := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_physicalIntervalRestriction a b q] with u hu
      intro hs
      rw [hu]
      apply indicator_of_notMem
      intro hm
      exact (not_lt_of_ge (hs.2.trans (max_le ha ht))) hm.1
    _ = 0 := by simp

theorem primitive_physicalIntervalRestriction_right (a b : ℝ) (q : Velocity)
    (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) (ht : b ≤ t) :
    primitive (physicalIntervalRestriction a b q) t = ∫ u in a..b, q u := by
  rw [primitive, intervalIntegral.integral_of_le (ha.trans (hab.trans ht)),
    intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ u in Ioc (0 : ℝ) t, (Ioc a b).indicator (q : ℝ → ℝ) u :=
      integral_congr_ae (ae_restrict_of_ae (ae_physicalIntervalRestriction a b q))
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
      have he : Ioc a b ∩ Ioc (0 : ℝ) t = Ioc a b := by
        apply Set.inter_eq_left.mpr
        intro u hu
        exact ⟨lt_of_le_of_lt ha hu.1, hu.2.trans ht⟩
      rw [he]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
