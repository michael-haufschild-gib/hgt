import GaloisForLFunctions.HTGeometry.ModularLambdaGrowth

/-!
# Exponential Schottky growth on the disk

The modular covering, Schwarz--Pick and the explicit cusp-height bound give
the required reciprocal-boundary-distance exponent for two omitted values.
-/

open Complex Metric Set
open Bottcher

namespace GaloisForLFunctions.HTGeometry

/-- A disk map omitting zero and one has an exponential Schottky bound. -/
theorem exists_exp_bound_of_omitting_disk {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ < 1 →
      ‖f z‖ ≤ 20001 * Real.exp (C / (1 - ‖z‖)) := by
  obtain ⟨g, hgd, hgb, hge⟩ := omitting_lift_member_strict
    (c := 0) (by norm_num : (0 : ℝ) < 1) f hf
    (fun z hz => mem_compl01.mpr (homit z hz))
  have ha : ‖g 0‖ < 1 := hgb 0 (mem_ball_self (by norm_num))
  let A := (1 - ‖g 0‖) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  let C := 4 * Real.pi / A
  have hC : 0 < C := div_pos (by positivity) hA
  refine ⟨C, hC, fun z hz => ?_⟩
  have hzm : z ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hg : ‖g z‖ < 1 := hgb z hzm
  have hblas := blaschke_lift_norm_le_dist_div
    (by norm_num : (0 : ℝ) < 1) hgd (fun w hw => (hgb w hw).le) ha hzm
  simp only [dist_zero_right, div_one] at hblas
  have hsq := norm_le_of_blaschke_le (norm_nonneg z) hz le_rfl ha hg.le hblas
  have hcoef : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hdelta : (1 - ‖z‖) * A ≤ 1 - ‖g z‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hcoef hA.le
    change (1 - ‖z‖) * (1 - ‖g 0‖) ^ 2 ≤ _ at hm ⊢
    linarith
  have hD : 0 < (1 - ‖z‖) * A := mul_pos (sub_pos.mpr hz) hA
  have hG : 0 < 1 - ‖g z‖ ^ 2 := by nlinarith [norm_nonneg (g z)]
  have hheight : max (cayleyInv (g z)).im (1 / (cayleyInv (g z)).im) ≤
      4 / ((1 - ‖z‖) * A) := by
    apply (cayleyInv_height_max_le hg).trans
    rw [div_le_div_iff₀ hG hD]
    nlinarith
  have him := cayleyInv_im_pos_of_norm_lt_one hg
  have hnorm := norm_modularLambda_le_exp_height ⟨cayleyInv (g z), him⟩
  have harg : Real.pi * max (cayleyInv (g z)).im (1 / (cayleyInv (g z)).im) ≤
      C / (1 - ‖z‖) := by
    calc
      _ ≤ Real.pi * (4 / ((1 - ‖z‖) * A)) :=
        mul_le_mul_of_nonneg_left hheight Real.pi_pos.le
      _ = C / (1 - ‖z‖) := by dsimp [C]; field_simp
  calc
    ‖f z‖ = ‖modularLambda (cayleyInv (g z))‖ := congrArg norm (hge hzm).symm
    _ ≤ 20001 * Real.exp (Real.pi * max (cayleyInv (g z)).im
        (1 / (cayleyInv (g z)).im)) := hnorm
    _ ≤ 20001 * Real.exp (C / (1 - ‖z‖)) := by gcongr

end GaloisForLFunctions.HTGeometry
