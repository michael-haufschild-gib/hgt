import GaloisForLFunctions.HTGeometry.CosineCornerCoordinates
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Discrete parameters approach the analytic corner -/

namespace GaloisForLFunctions.HTGeometry.CosineCornerSequence

open Complex Filter LabeledCosineDescent CosineCornerCoordinates CosineCornerMarker
open scoped Topology

noncomputable section

def parameters (n : ℕ) : ℂ × ℂ := ((n : ℂ)⁻¹, exponentialParameter n)

theorem inverse_parameter_limit : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

theorem exponential_parameter_limit : Tendsto exponentialParameter atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hb : Tendsto (fun n : ℕ ↦ -(2 * Real.pi * (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hp hn)
  have he := Complex.continuous_ofReal.continuousAt.tendsto.comp (Real.tendsto_exp_atBot.comp hb)
  unfold exponentialParameter
  simpa [Function.comp_def, exponentialParameter, Complex.ofReal_exp, mul_comm, mul_left_comm] using he

theorem parameters_limit : Tendsto parameters atTop (𝓝 (0, 0)) := by
  rw [nhds_prod_eq]
  exact inverse_parameter_limit.prodMk exponential_parameter_limit

theorem squareCoordinate_im (u : ℂ) :
    (squareCoordinate u).im = 27 * (2 * u.re * u.im) / (4 * Real.pi ^ 2) := by
  have he : (4 * (Real.pi : ℂ) ^ 2) = ((4 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [squareCoordinate, he, sub_im, Complex.div_ofReal_im]
  simp [pow_two]
  ring

theorem point_nonreal_of_parts {n : ℕ} {u : ℂ} (hu : u.im ≠ 0)
    (hr : (lifted n u).re ≠ 0) : (point n u).im ≠ 0 := by
  rw [point, squareCoordinate_im]
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hr)
      (by simpa [lifted] using hu))
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)

theorem eventually_nonreal {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 root)) :
    ∀ᶠ n in atTop, (u n).im ≠ 0 ∧ (point n (u n)).im ≠ 0 := by
  have hi : Tendsto (fun n ↦ (u n).im) atTop (𝓝 root.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hu
  have hr : Tendsto (fun n : ℕ ↦ 2 * Real.pi + (n : ℝ)⁻¹ * (u n).re)
      atTop (𝓝 (2 * Real.pi)) := by
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add
      (ht.mul (Complex.continuous_re.continuousAt.tendsto.comp hu))
  have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  filter_upwards [hi.eventually_ne root_im_ne_zero, hr.eventually_ne hp,
    eventually_gt_atTop (0 : ℕ)] with n hni hnr hn
  refine ⟨hni, point_nonreal_of_parts hni ?_⟩
  intro hzero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  have he : 2 * Real.pi + (n : ℝ)⁻¹ * (u n).re = (n : ℝ)⁻¹ * (lifted n (u n)).re := by
    simp [lifted]
    field_simp
    ring
  exact hnr (by rw [he, hzero, mul_zero])

theorem index_eq_of_point_eq {n m : ℕ} {u : ℂ} (hu : u.im ≠ 0)
    (h : point n u = point m u) : n = m := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)
  have hs : lifted n u ^ 2 = lifted m u ^ 2 := by
    have h' : 27 * lifted n u ^ 2 / (4 * (Real.pi : ℂ) ^ 2) =
        27 * lifted m u ^ 2 / (4 * (Real.pi : ℂ) ^ 2) := by
      dsimp [point, squareCoordinate] at h
      linear_combination h
    have hh := (div_left_inj' hd).mp h'
    exact mul_left_cancel₀ (by norm_num : (27 : ℂ) ≠ 0) hh
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · have hn : (n : ℂ) = m := by
      apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp)
      dsimp [lifted] at he
      linear_combination he
    exact_mod_cast hn
  · have hi := congrArg Complex.im he
    simp [lifted] at hi
    exact False.elim (hu (by linear_combination (1 / 2 : ℝ) * hi))

end

end GaloisForLFunctions.HTGeometry.CosineCornerSequence
