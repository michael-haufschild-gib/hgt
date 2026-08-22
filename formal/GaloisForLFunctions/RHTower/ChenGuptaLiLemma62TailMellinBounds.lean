import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailEulerBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalDecay
import GaloisForLFunctions.RHTower.MellinUniformBoundedStripAllOrder

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A point of CGL's tail rectangle. -/
structure CGLLemma62TailMellinPoint (d : CGLLemma62TailContourDepth) where
  x : ℝ
  y : ℝ
  lower : -2 * (d.value : ℝ) ≤ x
  upper : x ≤ -1

/-- The explicit all-order Mellin budget uniform on CGL's tail rectangle. -/
def cglLemma62TailMellinUniformBudget (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) (n : ℕ) : ℝ :=
  ∫ u : ℝ, deningerMeyerBoundedMellinMajorant (cglLemma62StrongLogSource w)
    ⟨2 + 2 * (d.value : ℝ), by positivity⟩ n u

/-- CGL's Mellin kernel has every prescribed decay order uniformly on its
entire tail rectangle. -/
theorem cglLemma62_mellinTransform_tail_uniformAllOrderDecay
    (w : CGLRealSmoothBump) (d : CGLLemma62TailContourDepth) (n : ℕ)
    (p : CGLLemma62TailMellinPoint d) :
    |p.y| ^ n * ‖cglLemma62MellinTransform w ((p.x : ℂ) + (p.y : ℂ) * I)‖ ≤
      cglLemma62TailMellinUniformBudget w d n := by
  let S : DeningerMeyerBoundedMellinStrip :=
    ⟨2 + 2 * (d.value : ℝ), by positivity⟩
  let sigma : DeningerMeyerBoundedMellinAbscissa S := ⟨2 - p.x, by
    linarith [p.upper], by
    dsimp [S]
    linarith [p.lower]⟩
  have hstrong := abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_bounded
    (cglLemma62StrongLogSource w) S n sigma (-p.y)
  have harg :
      ((sigma.value : ℝ) : ℂ) + ((-p.y : ℝ) : ℂ) * I =
        2 - ((p.x : ℂ) + (p.y : ℂ) * I) := by
    dsimp [sigma]
    push_cast
    ring
  rw [harg] at hstrong
  rw [← cglLemma62_mellinTransform_eq_strongLogMellin] at hstrong
  simpa [cglLemma62TailMellinUniformBudget, S] using hstrong

/-- On every CGL tail-rectangle point the positive length factor is at most one. -/
theorem cglLemma62_lengthPower_tail_norm_le_one
    (N : CGLPositiveLength) (d : CGLLemma62TailContourDepth)
    (p : CGLLemma62TailMellinPoint d) :
    ‖(N.value : ℂ) ^ ((p.x : ℂ) + (p.y : ℂ) * I)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos N.positive]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive)
  · simp
    linarith [p.upper]

/-- On CGL's far-left line, the positive-length factor has its exact source
value; retaining it is necessary for the `N` cancellation in the `I₂` bound. -/
theorem cglLemma62_lengthPower_farLeft_norm_eq
    (N : CGLPositiveLength) (d : CGLLemma62TailContourDepth) (v : ℝ) :
    ‖(N.value : ℂ) ^ cglLemma62FarLeftPoint d v‖ =
      (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by
  rw [Complex.norm_natCast_cpow_of_pos N.positive]
  congr 1
  simp [cglLemma62FarLeftPoint]

end

end RHTower
