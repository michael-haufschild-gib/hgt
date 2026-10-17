import GaloisForLFunctions.BiScaleUncertainty.PhysicalTranslationContinuity

/-!
# Actual physical box averages

Bochner integration of the strongly continuous translation orbit constructs
a bounded linear contraction at every positive exponential width. Translation
covariance gives exact moving-window and endpoint-cancellation formulas.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def physicalBoxAverageValue (s : ℝ) (q : Velocity) : Velocity :=
  (Real.exp s)⁻¹ • physicalOrbitPrimitive q (Real.exp s)

theorem physicalBoxAverageValue_norm_le (s : ℝ) (q : Velocity) :
    ‖physicalBoxAverageValue s q‖ ≤ ‖q‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := Real.exp s) (C := ‖q‖)
    (fun u _ => (physicalTranslation_norm u q).le)
  rw [sub_zero, abs_of_pos (Real.exp_pos s)] at h
  rw [physicalBoxAverageValue, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.exp_pos s))]
  calc
    _ ≤ (Real.exp s)⁻¹ * (‖q‖ * Real.exp s) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = ‖q‖ := by field_simp

def physicalBoxAverage (s : ℝ) : Velocity →L[ℝ] Velocity :=
  LinearMap.mkContinuous
    { toFun := physicalBoxAverageValue s
      map_add' := fun q r => by
        simp only [physicalBoxAverageValue, physicalOrbitPrimitive, map_add]
        rw [intervalIntegral.integral_add (intervalIntegrable_physicalTranslation q _ _)
          (intervalIntegrable_physicalTranslation r _ _), smul_add]
      map_smul' := fun a q => by
        simp only [physicalBoxAverageValue, physicalOrbitPrimitive, map_smul,
          intervalIntegral.integral_smul, smul_comm (Real.exp s)⁻¹ a]
        rfl }
    1 (fun q => by
      change ‖physicalBoxAverageValue s q‖ ≤ 1*‖q‖
      simpa only [one_mul] using physicalBoxAverageValue_norm_le s q)

theorem physicalBoxAverage_apply (s : ℝ) (q : Velocity) :
    physicalBoxAverage s q = (Real.exp s)⁻¹ • ∫ u in 0..Real.exp s, physicalTranslation u q := rfl

theorem physicalBoxAverage_norm_le (s : ℝ) (q : Velocity) :
    ‖physicalBoxAverage s q‖ ≤ ‖q‖ := physicalBoxAverageValue_norm_le s q

theorem norm_physicalBoxAverage_le (s : ℝ) : ‖physicalBoxAverage s‖ ≤ 1 :=
  (physicalBoxAverage s).opNorm_le_bound (by norm_num)
    (fun q => by simpa only [one_mul] using physicalBoxAverage_norm_le s q)

theorem exp_smul_physicalBoxAverage (s : ℝ) (q : Velocity) :
    Real.exp s • physicalBoxAverage s q = physicalOrbitPrimitive q (Real.exp s) := by
  rw [physicalBoxAverage_apply, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero s), one_smul]
  rfl

theorem physicalBoxAverage_translation (s c : ℝ) (q : Velocity) :
    physicalBoxAverage s (physicalTranslation c q) = physicalTranslation c (physicalBoxAverage s q) := by
  simp only [physicalBoxAverage_apply, map_smul]
  rw [← (physicalTranslation c).intervalIntegral_comp_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  exact physicalTranslation_comm u c q

theorem physicalTranslation_boxAverage (s c : ℝ) (q : Velocity) :
    physicalTranslation c (physicalBoxAverage s q) =
      (Real.exp s)⁻¹ • (physicalOrbitPrimitive q (c+Real.exp s)-physicalOrbitPrimitive q c) := by
  rw [physicalBoxAverage_apply, map_smul,
    ← (physicalTranslation c).intervalIntegral_comp_comm]
  simp only [physicalTranslation_comp]
  rw [intervalIntegral.integral_comp_add_left (a := 0) (b := Real.exp s)
    (fun u => physicalTranslation u q) c, add_zero, physicalOrbitPrimitive_sub]

theorem physicalBoxAverage_shift_difference (s c : ℝ) (q : Velocity) :
    physicalTranslation c (physicalBoxAverage s q)-physicalBoxAverage s q =
      (Real.exp s)⁻¹ • ∫ u in 0..c,
        (physicalTranslation (u+Real.exp s) q-physicalTranslation u q) := by
  rw [physicalTranslation_boxAverage, physicalBoxAverage_apply, ← smul_sub]
  congr 1
  have hi : IntervalIntegrable (fun u => physicalTranslation (u+Real.exp s) q) volume 0 c :=
    ((continuous_physicalTranslation q).comp
      (continuous_id.add continuous_const)).intervalIntegrable 0 c
  rw [intervalIntegral.integral_sub hi (intervalIntegrable_physicalTranslation q 0 c)]
  rw [intervalIntegral.integral_comp_add_right (a := 0) (b := c)
    (fun u => physicalTranslation u q) (Real.exp s), zero_add,
    ← physicalOrbitPrimitive_sub q (Real.exp s) (c+Real.exp s)]
  change physicalOrbitPrimitive q (c+Real.exp s)-physicalOrbitPrimitive q c-
    physicalOrbitPrimitive q (Real.exp s) =
      (physicalOrbitPrimitive q (c+Real.exp s)-physicalOrbitPrimitive q (Real.exp s))-
        physicalOrbitPrimitive q c
  abel

def physicalBoxDerivative (s : ℝ) : Velocity →L[ℝ] Velocity :=
  (Real.exp s)⁻¹ • ((physicalTranslation (Real.exp s)).toContinuousLinearMap-
    ContinuousLinearMap.id ℝ Velocity)

theorem physicalBoxDerivative_apply (s : ℝ) (q : Velocity) :
    physicalBoxDerivative s q = (Real.exp s)⁻¹ • (physicalTranslation (Real.exp s) q-q) := rfl

theorem physicalBoxDerivative_norm_le (s : ℝ) (q : Velocity) :
    ‖physicalBoxDerivative s q‖ ≤ (2/Real.exp s)*‖q‖ := by
  rw [physicalBoxDerivative_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.exp_pos s))]
  have h := norm_sub_le (physicalTranslation (Real.exp s) q) q
  rw [physicalTranslation_norm] at h
  calc
    _ ≤ (Real.exp s)⁻¹*(‖q‖+‖q‖) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
