import GaloisForLFunctions.HTGeometry.CosineProductRepair
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The nonreal corner over a nontrivial cube root

These are exact fixed-marker identities. The branch construction uses the
analytic corner submersions, independently of growth or approximation bounds.
-/

namespace GaloisForLFunctions.HTGeometry.CosineCornerMarker

open Complex LabeledCosineDescent

noncomputable section

def side : ℂ := (Real.sqrt 3 : ℝ)
def realTarget : ℝ := Real.cos (Real.pi / 9) + Real.sqrt 3
def root : ℂ := (Real.arcosh realTarget : ℂ) * I
def slope : ℂ := -side⁻¹
def mark : ℂ := (-1 - I * side) / 2
def conicConstant : ℂ := 2 * (Real.pi : ℂ) ^ 2 / 81

theorem side_sq : side ^ 2 = 3 := by
  dsimp [side]
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

theorem side_ne_zero : side ≠ 0 := by
  intro h
  have hs := side_sq
  rw [h] at hs
  norm_num at hs

theorem realTarget_gt_one : 1 < realTarget := by
  have hc : 0 < Real.cos (Real.pi / 9) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : 1 < Real.sqrt 3 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  dsimp [realTarget]
  linarith

theorem root_cos : cos root = source 0 + side := by
  rw [root, Complex.cos_mul_I, ← Complex.ofReal_cosh,
    Real.cosh_arcosh (le_of_lt realTarget_gt_one), CosineBasepointRepair.source_zero]
  simp [realTarget, side, Complex.ofReal_cos]

theorem root_im_ne_zero : root.im ≠ 0 := by
  have hn : Real.arcosh realTarget ≠ 0 := by
    exact ne_of_gt (Real.arcosh_pos realTarget_gt_one)
  simpa [root] using hn

theorem root_cos_ne_source : cos root ≠ source 0 := by
  rw [root_cos]
  exact add_ne_left.mpr side_ne_zero

theorem root_sin_ne_zero : sin root ≠ 0 := by
  intro hs
  have hc := Complex.sin_sq_add_cos_sq root
  rw [hs, zero_pow (by norm_num : 2 ≠ 0), zero_add] at hc
  have hx : cos root = (realTarget : ℂ) := by
    rw [root, Complex.cos_mul_I, ← Complex.ofReal_cosh,
      Real.cosh_arcosh (le_of_lt realTarget_gt_one)]
  rw [hx] at hc
  have hr : realTarget ^ 2 = 1 := by exact_mod_cast hc
  rcases sq_eq_one_iff.mp hr with h | h <;> linarith [realTarget_gt_one]

theorem root_slope : -(cos root - source 0)⁻¹ = slope := by
  simp [root_cos, slope]

theorem slope_sub_I_ne_zero : slope - I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [slope, side] at hi

theorem mark_im_ne_zero : mark.im ≠ 0 := by
  have hs : Real.sqrt 3 ≠ 0 := by
    intro h
    exact side_ne_zero (by simp [side, h])
  simp [mark, side, hs]

theorem mark_ne_one : mark ≠ 1 := by
  intro h
  exact mark_im_ne_zero (by simp [h])

theorem mark_cube : mark ^ 3 = 1 := by
  have h3 : side ^ 3 = 3 * side := by rw [pow_succ, side_sq]
  have hi3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  dsimp [mark]
  ring_nf
  simp only [I_sq, hi3, side_sq, h3]
  ring

theorem slope_mark_relation : slope + I = mark * (slope - I) := by
  dsimp [slope, mark]
  field_simp [side_ne_zero]
  ring_nf
  simp only [I_sq, side_sq]
  ring

theorem mark_ne_zero : mark ≠ 0 := by
  intro h
  have hc := mark_cube
  rw [h] at hc
  norm_num at hc

theorem inverse_mark_cube : (mark⁻¹) ^ 3 = 1 := by
  rw [inv_pow, mark_cube, inv_one]

theorem inverse_mark_ne_one : mark⁻¹ ≠ 1 := by
  intro h
  have hh := congrArg Inv.inv h
  exact mark_ne_one (by simpa using hh)

theorem mark_ne_inverse : mark ≠ mark⁻¹ := by
  intro h
  have h2 : mark * mark = 1 := by
    calc
      _ = mark * mark⁻¹ := congrArg (fun z : ℂ ↦ mark * z) h
      _ = 1 := mul_inv_cancel₀ mark_ne_zero
  have h3 : mark ^ 3 = mark := by rw [pow_succ, pow_two, h2, one_mul]
  exact mark_ne_one (h3.symm.trans mark_cube)

end

end GaloisForLFunctions.HTGeometry.CosineCornerMarker
