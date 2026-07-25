import GaloisForLFunctions.RHTower.SmoothAFEGaussianNonzero
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Removable part of the Gaussian Mellin kernel

Write the full inverse-Mellin integrand as `H(w) / w`, where

`H(w) = x⁻ʷ exp(w²)` and `H(0) = 1`.

The divided difference `dslope H 0` gives an everywhere-differentiable extension of
`(H(w) - 1) / w`.  Consequently, away from zero the integrand decomposes exactly as

`1 / w + dslope H 0 w`.

This isolates the simple pole and its unit residue for the upcoming residue-crossing contour.
-/

noncomputable section

namespace RHTower

open Complex Set

def smoothAFENumerator (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ (-w) * Complex.exp (w ^ 2)

def smoothAFERegularPart (x : ℝ) : ℂ → ℂ :=
  dslope (smoothAFENumerator x) 0

theorem smoothAFENumerator_zero (x : ℝ) :
    smoothAFENumerator x 0 = 1 := by
  simp [smoothAFENumerator]

theorem differentiable_smoothAFENumerator {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (smoothAFENumerator x) := by
  haveI : NeZero (x : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  exact ((differentiable_const_cpow_of_neZero (x : ℂ)).comp
    differentiable_neg).mul (differentiable_exp.comp (differentiable_pow 2))

theorem differentiable_smoothAFERegularPart {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (smoothAFERegularPart x) := by
  apply differentiableOn_univ.1
  rw [smoothAFERegularPart, differentiableOn_dslope Filter.univ_mem]
  exact (differentiable_smoothAFENumerator hx).differentiableOn

theorem smoothAFEMellinIntegrand_eq_inv_add_regularPart
    (x : ℝ) {w : ℂ} (hw : w ≠ 0) :
    smoothAFEMellinIntegrand x w = w⁻¹ + smoothAFERegularPart x w := by
  rw [smoothAFERegularPart, dslope_of_ne _ hw, slope_def_field]
  simp only [sub_zero]
  rw [smoothAFEMellinIntegrand, smoothAFEGaussianKernel,
    smoothAFENumerator_zero]
  unfold smoothAFENumerator
  field_simp
  ring

end RHTower
