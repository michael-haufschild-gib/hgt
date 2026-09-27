import GaloisForLFunctions.RHTower.LogarithmicEntryIntegration
import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction

/-!
# Exact quadrature for logarithmic dilations of a primitive

The delay sum of an integrable force's primitive is a reverse-time floor
integral. Its continuous main term leaves an exact fractional-part work.
The force may have jumps at logarithmic integer times.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

theorem logarithmicEntrySum_one (t : ℝ) :
    logarithmicEntrySum (fun _ => 1) t = (⌊Real.exp t⌋₊ : ℝ) := by
  simp [logarithmicEntrySum, Nat.card_Icc]

theorem logarithmicDilationSum_primitive_eq_floor_integral (g : ℝ → ℝ)
    {T : ℝ} (hg : IntervalIntegrable g volume 0 T) (hT : 0 ≤ T) :
    logarithmicDilationSum (fun u => ∫ t in (0 : ℝ)..u, g t) T =
      ∫ s in (0 : ℝ)..T, g (T - s) * (⌊Real.exp s⌋₊ : ℝ) := by
  have hr : IntervalIntegrable (fun s => g (T - s)) volume 0 T := by
    simpa only [sub_zero, sub_self] using (hg.comp_sub_left T).symm
  have hi := integral_mul_logarithmicEntrySum_of_intervalIntegrable
    (fun _ => 1) (fun s => g (T - s)) hr hT
  simp only [logarithmicEntrySum_one, one_mul,
    intervalIntegral.integral_comp_sub_left, sub_self] at hi
  simpa only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul] using hi.symm

theorem intervalIntegrable_reverse_mul_fract_exp (g : ℝ → ℝ)
    {T : ℝ} (hg : IntervalIntegrable g volume 0 T) (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => g (T - s) * Int.fract (Real.exp s)) volume 0 T := by
  have hr : IntervalIntegrable (fun s => g (T - s)) volume 0 T := by
    simpa only [sub_zero, sub_self] using (hg.comp_sub_left T).symm
  have hf := intervalIntegrable_mul_logarithmicEntrySum_of_intervalIntegrable
    (fun _ => 1) (fun s => g (T - s)) hr hT
  have he := hr.mul_continuousOn Real.continuous_exp.continuousOn
  apply (he.sub hf).congr
  intro s _
  dsimp only
  rw [logarithmicEntrySum_one,
    natCast_floor_eq_intCast_floor (Real.exp_pos s).le, Int.fract]
  ring

theorem logarithmicDilationSum_primitive_quadrature (g : ℝ → ℝ)
    {T : ℝ} (hg : IntervalIntegrable g volume 0 T) (hT : 0 ≤ T) :
    logarithmicDilationSum (fun u => ∫ t in (0 : ℝ)..u, g t) T =
      Real.exp T * (∫ t in (0 : ℝ)..T, Real.exp (-t) * g t) -
        ∫ s in (0 : ℝ)..T, g (T - s) * Int.fract (Real.exp s) := by
  have hr : IntervalIntegrable (fun s => g (T - s)) volume 0 T := by
    simpa only [sub_zero, sub_self] using (hg.comp_sub_left T).symm
  have he := hr.mul_continuousOn Real.continuous_exp.continuousOn
  have hf := intervalIntegrable_reverse_mul_fract_exp g hg hT
  rw [logarithmicDilationSum_primitive_eq_floor_integral g hg hT]
  have hsplit : (∫ s in (0 : ℝ)..T, g (T - s) * (⌊Real.exp s⌋₊ : ℝ)) =
      (∫ s in (0 : ℝ)..T, g (T - s) * Real.exp s) -
        ∫ s in (0 : ℝ)..T, g (T - s) * Int.fract (Real.exp s) := by
    rw [← intervalIntegral.integral_sub he hf]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [natCast_floor_eq_intCast_floor (Real.exp_pos s).le, Int.fract]
    ring
  rw [hsplit]
  congr 1
  calc
    _ = ∫ s in (0 : ℝ)..T, Real.exp T * (Real.exp (-(T - s)) * g (T - s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [← mul_assoc, ← Real.exp_add]
      rw [show T + -(T - s) = s by ring]
      exact mul_comm _ _
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t => Real.exp (-t) * g t)]
      simp only [sub_self, sub_zero]

end RHTower
