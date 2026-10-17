import GaloisForLFunctions.BiScaleUncertainty.PhysicalDilation

/-!
# Actual physical translations and primitive anchoring

Measure-preserving pullback constructs the full L² translation isometry.
Its primitive has an explicit anchor correction and determines the velocity.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def physicalTranslation (b : ℝ) : Velocity →ₗᵢ[ℝ] Velocity :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => t+b) (measurePreserving_add_right volume b)

theorem ae_physicalTranslation (b : ℝ) (q : Velocity) :
    physicalTranslation b q =ᵐ[volume] (fun t => q (t+b)) := by
  change (Lp.compMeasurePreserving (fun t : ℝ => t+b)
    (measurePreserving_add_right volume b) q : ℝ → ℝ) =ᵐ[volume] _
  exact Lp.coeFn_compMeasurePreserving q (measurePreserving_add_right volume b)

theorem ae_physicalTranslate_pullback (b : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun t => f (t+b)) =ᵐ[volume] (fun t => g (t+b)) := by
  simpa only [Function.comp_def] using
    (measurePreserving_add_right (volume : Measure ℝ) b).quasiMeasurePreserving.ae_eq h

theorem physicalTranslation_norm (b : ℝ) (q : Velocity) :
    ‖physicalTranslation b q‖ = ‖q‖ := (physicalTranslation b).norm_map q

theorem physicalTranslation_zero (q : Velocity) : physicalTranslation 0 q = q := by
  apply Lp.ext
  simpa only [add_zero] using ae_physicalTranslation 0 q

theorem physicalTranslation_comp (b c : ℝ) (q : Velocity) :
    physicalTranslation b (physicalTranslation c q) = physicalTranslation (b+c) q := by
  apply Lp.ext
  filter_upwards [ae_physicalTranslation b (physicalTranslation c q),
    ae_physicalTranslate_pullback b (ae_physicalTranslation c q),
    ae_physicalTranslation (b+c) q] with t ht hc he
  rw [ht, hc, he, add_assoc]

theorem physicalTranslation_comm (b c : ℝ) (q : Velocity) :
    physicalTranslation b (physicalTranslation c q) = physicalTranslation c (physicalTranslation b q) := by
  rw [physicalTranslation_comp, physicalTranslation_comp, add_comm b c]

theorem physicalTranslation_inverse (b : ℝ) (q : Velocity) :
    physicalTranslation (-b) (physicalTranslation b q) = q := by
  rw [physicalTranslation_comp, neg_add_cancel, physicalTranslation_zero]

theorem physicalTranslation_surjective (b : ℝ) : Function.Surjective (physicalTranslation b) := by
  intro q
  refine ⟨physicalTranslation (-b) q, ?_⟩
  rw [physicalTranslation_comp, add_neg_cancel, physicalTranslation_zero]

theorem primitive_at_zero (q : Velocity) : primitive q 0 = 0 := by simp [primitive]

theorem primitive_zero_velocity (t : ℝ) : primitive 0 t = 0 := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with u hu
      exact fun _ => hu
    _ = 0 := by simp

theorem primitive_add_velocity (q r : Velocity) (t : ℝ) :
    primitive (q+r) t = primitive q t+primitive r t := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, q u+r u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_add q r] with u hu
      exact fun _ => hu
    _ = _ := intervalIntegral.integral_add
      (intervalIntegrable_velocity q 0 t) (intervalIntegrable_velocity r 0 t)

theorem primitive_neg_velocity (q : Velocity) (t : ℝ) :
    primitive (-q) t = -primitive q t := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, -q u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_neg q] with u hu
      exact fun _ => hu
    _ = _ := intervalIntegral.integral_neg

theorem primitive_sub_velocity (q r : Velocity) (t : ℝ) :
    primitive (q-r) t = primitive q t-primitive r t := by
  rw [sub_eq_add_neg, primitive_add_velocity, primitive_neg_velocity, sub_eq_add_neg]

theorem primitive_injective : Function.Injective primitive := by
  intro q r h
  apply Lp.ext
  filter_upwards [ae_hasDerivAt_primitive q, ae_hasDerivAt_primitive r] with t hq hr
  rw [h] at hq
  exact hq.unique hr

theorem primitive_physicalTranslation (b : ℝ) (q : Velocity) (t : ℝ) :
    primitive (physicalTranslation b q) t = primitive q (t+b)-primitive q b := by
  rw [primitive_sub]
  unfold primitive
  calc
    _ = ∫ u in 0..t, q (u+b) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_physicalTranslation b q] with u hu
      exact fun _ => hu
    _ = _ := by
      simpa only [zero_add] using
        intervalIntegral.integral_comp_add_right (a := 0) (b := t) (q : ℝ → ℝ) b

theorem log_physicalTranslation (b : ℝ≥0) (q : Velocity) (x : ℝ) :
    logPrimitive (physicalTranslation b q) x =
      logPrimitive q (Real.log (Real.exp x+b))-primitive q b := by
  rw [logPrimitive, primitive_physicalTranslation, logPrimitive,
    Real.exp_log (by positivity)]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
