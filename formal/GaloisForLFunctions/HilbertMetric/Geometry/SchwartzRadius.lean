import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# A uniform positive radius matrix from Schwartz decay

Polynomial multiples of the first two derivatives remain Schwartz.
Their zeroth seminorms give an explicit positive scale at which the
stereographic radius matrix dominates half the identity everywhere.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzRadius
open GaloisForLFunctions.HTGeometry.GaussBonnet BonnetSupport
noncomputable section

private def dx (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  SchwartzMap.evalCLM ℝ (ℝ × ℝ) ℝ (1, 0) (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℝ f)

private def dy (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  SchwartzMap.evalCLM ℝ (ℝ × ℝ) ℝ (0, 1) (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℝ f)

private theorem dx_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) : dx f p = px f p := rfl
private theorem dy_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) : dy f p = py f p := rfl

private theorem fst_temperate : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.1) := by
  change Function.HasTemperateGrowth (ContinuousLinearMap.fst ℝ ℝ ℝ)
  fun_prop
private theorem snd_temperate : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.2) := by
  change Function.HasTemperateGrowth (ContinuousLinearMap.snd ℝ ℝ ℝ)
  fun_prop
private theorem denominator_temperate : Function.HasTemperateGrowth denominator := by
  have hf := fst_temperate
  have hs := snd_temperate
  unfold denominator
  fun_prop

private def scalarError (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  (1 / 2 : ℝ) • (f - SchwartzMap.smulLeftCLM ℝ Prod.fst (dx f) -
    SchwartzMap.smulLeftCLM ℝ Prod.snd (dy f))

/-- The first diagonal perturbation of the round radius matrix. -/
def errorXX (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  scalarError f + (1 / 4 : ℝ) • SchwartzMap.smulLeftCLM ℝ denominator (dx (dx f))

/-- The second diagonal perturbation of the round radius matrix. -/
def errorYY (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  scalarError f + (1 / 4 : ℝ) • SchwartzMap.smulLeftCLM ℝ denominator (dy (dy f))

/-- The off-diagonal perturbation of the round radius matrix. -/
def errorXY (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  (1 / 4 : ℝ) • SchwartzMap.smulLeftCLM ℝ denominator (dy (dx f))

private theorem scalarError_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    scalarError f p = (f p - p.1 * px f p - p.2 * py f p) / 2 := by
  simp only [scalarError, smul_apply, sub_apply,
    SchwartzMap.smulLeftCLM_apply_apply fst_temperate,
    SchwartzMap.smulLeftCLM_apply_apply snd_temperate, smul_eq_mul, dx_apply, dy_apply]
  ring

/-- The perturbation is an actual Schwartz matrix, not an assumed bounded coefficient field. -/
theorem radius_eq (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    radiusXX (support f ε) p = 1 + ε * errorXX f p ∧
    radiusYY (support f ε) p = 1 + ε * errorYY f p ∧
    radiusXY (support f ε) p = ε * errorXY f p := by
  obtain ⟨hx, hy, hm⟩ := radius_decomposition (U := (f : ℝ × ℝ → ℝ)) (f.smooth ⊤) ε p
  have hdx : (dx f : ℝ × ℝ → ℝ) = px f := rfl
  have hdy : (dy f : ℝ × ℝ → ℝ) = py f := rfl
  simp only [errorXX, errorYY, errorXY, add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply denominator_temperate,
    smul_eq_mul, dx_apply, dy_apply, hdx, hdy, scalarError_apply]
  rw [hx, hy, hm]
  unfold scalarPart
  constructor
  · ring
  constructor <;> ring

/-- A concrete finite bound for all three entries. -/
def radiusBound (f : SchwartzMap (ℝ × ℝ) ℝ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (errorXX f) + SchwartzMap.seminorm ℝ 0 0 (errorYY f) +
    SchwartzMap.seminorm ℝ 0 0 (errorXY f)

theorem radiusBound_nonneg (f : SchwartzMap (ℝ × ℝ) ℝ) : 0 ≤ radiusBound f := by
  unfold radiusBound
  positivity

theorem error_le (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    |errorXX f p| ≤ radiusBound f ∧ |errorYY f p| ≤ radiusBound f ∧
      |errorXY f p| ≤ radiusBound f := by
  have hx := (errorXX f).norm_le_seminorm ℝ p
  have hy := (errorYY f).norm_le_seminorm ℝ p
  have hm := (errorXY f).norm_le_seminorm ℝ p
  rw [Real.norm_eq_abs] at hx hy hm
  have hxx : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (errorXX f) := by positivity
  have hyy : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (errorYY f) := by positivity
  have hxy : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (errorXY f) := by positivity
  unfold radiusBound
  exact ⟨by linarith only [hx, hyy, hxy], by linarith only [hy, hxx, hxy],
    by linarith only [hm, hxx, hyy]⟩

/-- Explicit scale obtained only from Schwartz seminorms. -/
def positiveScale (f : SchwartzMap (ℝ × ℝ) ℝ) : ℝ := 1 / (4 * (1 + radiusBound f))

theorem positiveScale_pos (f : SchwartzMap (ℝ × ℝ) ℝ) : 0 < positiveScale f := by
  have := radiusBound_nonneg f
  unfold positiveScale
  positivity

private theorem scaled_error_bound (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    |positiveScale f * errorXX f p| ≤ 1 / 4 ∧
    |positiveScale f * errorYY f p| ≤ 1 / 4 ∧
    |positiveScale f * errorXY f p| ≤ 1 / 4 := by
  have hs := (positiveScale_pos f).le
  have hscale : positiveScale f * radiusBound f ≤ 1 / 4 := by
    have hc := radiusBound_nonneg f
    unfold positiveScale
    have hd : 0 < 4 * (1 + radiusBound f) := by positivity
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hd).mpr
    linarith only
  obtain ⟨hx, hy, hm⟩ := error_le f p
  simp only [abs_mul, abs_of_nonneg hs]
  exact ⟨(mul_le_mul_of_nonneg_left hx hs).trans hscale,
    (mul_le_mul_of_nonneg_left hy hs).trans hscale,
    (mul_le_mul_of_nonneg_left hm hs).trans hscale⟩

/-- The actual radius quadratic form uniformly dominates half the Euclidean square norm. -/
theorem radius_uniform_positive (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) (a b : ℝ) :
    (a ^ 2 + b ^ 2) / 2 ≤
      radiusXX (support f (positiveScale f)) p * a ^ 2 +
      2 * radiusXY (support f (positiveScale f)) p * a * b +
      radiusYY (support f (positiveScale f)) p * b ^ 2 := by
  obtain ⟨hx, hy, hm⟩ := radius_eq f (positiveScale f) p
  rw [hx, hy, hm]
  obtain ⟨hxx, hyy, hxy⟩ := scaled_error_bound f p
  have hdx : (3 / 4 : ℝ) ≤ 1 + positiveScale f * errorXX f p := by
    linarith only [(abs_le.mp hxx).1]
  have hdy : (3 / 4 : ℝ) ≤ 1 + positiveScale f * errorYY f p := by
    linarith only [(abs_le.mp hyy).1]
  have hab : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := abs_le.mpr
    ⟨by nlinarith only [sq_nonneg (a + b)], by nlinarith only [sq_nonneg (a - b)]⟩
  have hprod := mul_le_mul hxy hab (abs_nonneg (a * b)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← abs_mul] at hprod
  have hcross := (abs_le.mp hprod).1
  have hxa := mul_le_mul_of_nonneg_right hdx (sq_nonneg a)
  have hyb := mul_le_mul_of_nonneg_right hdy (sq_nonneg b)
  nlinarith only [hcross, hxa, hyb]

#print axioms radius_eq
#print axioms radius_uniform_positive
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzRadius
