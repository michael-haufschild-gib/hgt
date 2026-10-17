import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxAverage

/-!
# Exact positive variance of the physical box producer

Averaging loss equals both the centered orbit variance and half the pair
variance. Every integral is finite because the actual translation orbit is
strongly continuous, and every cross-shift Gram term is retained.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem integral_physicalTranslation_sub_sq (q r : Velocity) (h : ℝ) :
    (∫ u in 0..h, ‖physicalTranslation u q-r‖^2) =
      h*(‖q‖^2+‖r‖^2)-2*⟪r, physicalOrbitPrimitive q h⟫ := by
  have hi : IntervalIntegrable (fun u => ⟪r, physicalTranslation u q⟫) volume 0 h :=
    (continuous_const.inner (continuous_physicalTranslation q)).intervalIntegrable 0 h
  calc
    _ = ∫ u in 0..h, (‖q‖^2+‖r‖^2)-2*⟪r, physicalTranslation u q⟫ := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [norm_sub_sq_real, physicalTranslation_norm, real_inner_comm]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hi.const_mul 2),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_inner_physicalTranslation]
      simp only [sub_zero, smul_eq_mul, physicalOrbitPrimitive]

theorem physicalBoxAverage_centered_variance (s : ℝ) (q : Velocity) :
    (∫ u in 0..Real.exp s, ‖physicalTranslation u q-physicalBoxAverage s q‖^2) =
      Real.exp s*(‖q‖^2-‖physicalBoxAverage s q‖^2) := by
  rw [integral_physicalTranslation_sub_sq, ← exp_smul_physicalBoxAverage,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem integral_physicalTranslation_pair_sq (q : Velocity) (h : ℝ) :
    (∫ u in 0..h, ∫ v in 0..h, ‖physicalTranslation u q-physicalTranslation v q‖^2) =
      2*h^2*‖q‖^2-2*‖physicalOrbitPrimitive q h‖^2 := by
  have hv (u : ℝ) :
      (∫ v in 0..h, ‖physicalTranslation u q-physicalTranslation v q‖^2) =
        2*h*‖q‖^2-2*⟪physicalOrbitPrimitive q h, physicalTranslation u q⟫ := by
    calc
      _ = ∫ v in 0..h, ‖physicalTranslation v q-physicalTranslation u q‖^2 := by
        apply intervalIntegral.integral_congr
        intro v _
        rw [norm_sub_rev]
      _ = _ := by
        rw [integral_physicalTranslation_sub_sq, physicalTranslation_norm, real_inner_comm]
        ring
  simp_rw [hv]
  have hi : IntervalIntegrable (fun u => ⟪physicalOrbitPrimitive q h, physicalTranslation u q⟫)
      volume 0 h :=
    (continuous_const.inner (continuous_physicalTranslation q)).intervalIntegrable 0 h
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hi.const_mul 2),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_inner_physicalTranslation]
  change (h-0)*(2*h*‖q‖^2)-2*⟪physicalOrbitPrimitive q h, physicalOrbitPrimitive q h⟫ = _
  rw [real_inner_self_eq_norm_sq]
  ring

theorem physicalBoxAverage_pair_variance (s : ℝ) (q : Velocity) :
    (∫ u in 0..Real.exp s, ∫ v in 0..Real.exp s,
      ‖physicalTranslation u q-physicalTranslation v q‖^2) =
        2*(Real.exp s)^2*(‖q‖^2-‖physicalBoxAverage s q‖^2) := by
  rw [integral_physicalTranslation_pair_sq, ← exp_smul_physicalBoxAverage,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  ring

theorem physicalBoxAverage_energy_loss (s : ℝ) (q : Velocity) :
    ‖q‖^2-‖physicalBoxAverage s q‖^2 =
      (∫ u in 0..Real.exp s, ∫ v in 0..Real.exp s,
        ‖physicalTranslation u q-physicalTranslation v q‖^2) / (2*(Real.exp s)^2) := by
  rw [physicalBoxAverage_pair_variance]
  field_simp

theorem physicalBoxAverage_variance_nonneg (s : ℝ) (q : Velocity) :
    0 ≤ ‖q‖^2-‖physicalBoxAverage s q‖^2 := by
  have h := physicalBoxAverage_norm_le s q
  nlinarith only [h, norm_nonneg q, norm_nonneg (physicalBoxAverage s q)]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
