import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxVariance
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Constructed affine regularity and strong approximation

Physical box averages have an explicit strong translation derivative. Their
commutators obey the gap-to-width bound, and they converge strongly to every
physical velocity as the width tends to zero.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem hasDerivAt_translation_physicalBoxAverage (s c : ℝ) (q : Velocity) :
    HasDerivAt (fun u => physicalTranslation u (physicalBoxAverage s q))
      (physicalTranslation c (physicalBoxDerivative s q)) c := by
  have he : (fun u => physicalTranslation u (physicalBoxAverage s q)) =
      (fun u => (Real.exp s)⁻¹ •
        (physicalOrbitPrimitive q (u+Real.exp s)-physicalOrbitPrimitive q u)) :=
    funext fun u => physicalTranslation_boxAverage s u q
  rw [he]
  have h := (((hasDerivAt_physicalOrbitPrimitive q (c+Real.exp s)).comp_add_const
    c (Real.exp s)).sub (hasDerivAt_physicalOrbitPrimitive q c)).const_smul (Real.exp s)⁻¹
  simpa only [Pi.smul_apply, Pi.sub_apply, physicalBoxDerivative_apply,
    map_smul, map_sub, physicalTranslation_comp] using h

theorem physicalBoxAverage_shift_norm_le_two (s c : ℝ) (q : Velocity) :
    ‖physicalTranslation c (physicalBoxAverage s q)-physicalBoxAverage s q‖ ≤ 2*‖q‖ := by
  have h := norm_sub_le (physicalTranslation c (physicalBoxAverage s q)) (physicalBoxAverage s q)
  rw [physicalTranslation_norm] at h
  linarith only [h, physicalBoxAverage_norm_le s q]

theorem physicalBoxAverage_shift_norm_le_gap (s c : ℝ) (q : Velocity) :
    ‖physicalTranslation c (physicalBoxAverage s q)-physicalBoxAverage s q‖ ≤
      (2*|c|/Real.exp s)*‖q‖ := by
  have hb (u : ℝ) : ‖physicalTranslation (u+Real.exp s) q-physicalTranslation u q‖ ≤ 2*‖q‖ := by
    have h := norm_sub_le (physicalTranslation (u+Real.exp s) q) (physicalTranslation u q)
    simpa only [physicalTranslation_norm, two_mul] using h
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := c) (fun u _ => hb u)
  rw [physicalBoxAverage_shift_difference, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.exp_pos s))]
  calc
    _ ≤ (Real.exp s)⁻¹ * ((2*‖q‖)*|c-0|) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [sub_zero]; ring

theorem physicalBoxAverage_shift_norm_le (s c : ℝ) (q : Velocity) :
    ‖physicalTranslation c (physicalBoxAverage s q)-physicalBoxAverage s q‖ ≤
      2*min 1 (|c|/Real.exp s)*‖q‖ := by
  rw [mul_min_of_nonneg 1 (|c|/Real.exp s) (by norm_num : (0 : ℝ) ≤ 2),
    min_mul_of_nonneg _ _ (norm_nonneg q), mul_one]
  apply le_min (physicalBoxAverage_shift_norm_le_two s c q)
  simpa only [mul_div_assoc] using physicalBoxAverage_shift_norm_le_gap s c q

theorem physicalBoxAverage_affine_energy_le (a b s : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b (physicalBoxAverage s q)‖^2 ≤
      4*|a|*(min 1 (|b*(a-1)|/Real.exp s))^2*‖q‖^2 := by
  have h := physicalBoxAverage_shift_norm_le s (b*(a-1)) q
  have hm : 0 ≤ min 1 (|b*(a-1)|/Real.exp s) := min_nonneg (by norm_num) (by positivity)
  have hn : 0 ≤ 2*min 1 (|b*(a-1)|/Real.exp s)*‖q‖ := by positivity
  have hs : ‖physicalTranslation (b*(a-1)) (physicalBoxAverage s q)-physicalBoxAverage s q‖^2 ≤
      (2*min 1 (|b*(a-1)|/Real.exp s)*‖q‖)^2 := by
    nlinarith only [h, hn,
      norm_nonneg (physicalTranslation (b*(a-1)) (physicalBoxAverage s q)-physicalBoxAverage s q)]
  rw [physicalAffineCommutator_energy]
  calc
    _ ≤ |a|*(2*min 1 (|b*(a-1)|/Real.exp s)*‖q‖)^2 :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg a)
    _ = _ := by ring

theorem physicalBoxAverage_affine_norm_le (a b s : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b (physicalBoxAverage s q)‖ ≤
      2*Real.sqrt |a|*min 1 (|b*(a-1)|/Real.exp s)*‖q‖ := by
  have he := physicalBoxAverage_affine_energy_le a b s q
  have hm : 0 ≤ min 1 (|b*(a-1)|/Real.exp s) := min_nonneg (by norm_num) (by positivity)
  have hn : 0 ≤ 2*Real.sqrt |a|*min 1 (|b*(a-1)|/Real.exp s)*‖q‖ := by positivity
  have hs : (2*Real.sqrt |a|*min 1 (|b*(a-1)|/Real.exp s)*‖q‖)^2 =
      4*|a|*(min 1 (|b*(a-1)|/Real.exp s))^2*‖q‖^2 := by
    simp only [mul_pow, Real.sq_sqrt (abs_nonneg a)]
    ring
  nlinarith only [he, hs, hn, norm_nonneg (physicalAffineCommutator a b (physicalBoxAverage s q))]

theorem norm_affineCommutator_comp_boxAverage_le (a b s : ℝ) :
    ‖(physicalAffineCommutator a b).comp (physicalBoxAverage s)‖ ≤
      2*Real.sqrt |a|*min 1 (|b*(a-1)|/Real.exp s) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply mul_nonneg (by positivity)
    exact min_nonneg (by norm_num) (by positivity)
  · intro q
    exact physicalBoxAverage_affine_norm_le a b s q

theorem physicalBoxAverage_tendsto (q : Velocity) :
    Tendsto (fun s : ℝ => physicalBoxAverage s q) atBot (𝓝 q) := by
  have h := ((hasDerivAt_physicalOrbitPrimitive q 0).tendsto_slope_zero_right).comp
    Real.tendsto_exp_atBot_nhdsGT
  simpa only [zero_add, physicalOrbitPrimitive_zero, sub_zero, physicalTranslation_zero,
    physicalOrbitPrimitive, ← physicalBoxAverage_apply] using h

theorem physicalBoxAverage_energy_loss_tendsto (q : Velocity) :
    Tendsto (fun s : ℝ => ‖q‖^2-‖physicalBoxAverage s q‖^2) atBot (𝓝 0) := by
  simpa only [sub_self] using
    tendsto_const_nhds.sub ((physicalBoxAverage_tendsto q).norm.pow 2)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
