import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion
import GaloisForLFunctions.RHTower.CCM.CCMShiftedXiCancellation
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Two-pole decomposition of the smooth zeta Mellin integrand

For `s ≠ 1`, put `ρ = 1 - s`.  Filling the zeta pole gives the entire numerator

`N(w) = x^w exp(w²) ((s+w-1) ζ(s+w))`.

Away from `w = 0, ρ`, the smooth zeta Mellin integrand is

`N(w) / (w (w-ρ))`.

Two successive divided differences split this quotient exactly into its two Cauchy kernels and an
entire remainder.  The residues are `ζ(s)` at `0` and
`x^(1-s) exp((1-s)²)/(1-s)` at `1-s`.
-/

noncomputable section

namespace RHTower

open Complex Set

def smoothAFEZetaPoleNumerator (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ)) * regularizedRiemannZeta (s + w)

def smoothAFEZetaPoleRemainder (s : ℂ) (x : ℝ) : ℂ → ℂ :=
  dslope (dslope (smoothAFEZetaPoleNumerator s x) 0) (1 - s)

def smoothAFEZetaShiftedPoleResidue (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) / (1 - s)

theorem differentiable_smoothAFEZetaPoleNumerator
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Differentiable ℂ (smoothAFEZetaPoleNumerator s x) := by
  haveI : NeZero (x : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  exact (((differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_id).mul
    (differentiable_exp.comp (differentiable_pow 2))).mul
      (differentiable_regularizedRiemannZeta.comp
        (by fun_prop))

theorem differentiable_smoothAFEZetaPoleRemainder
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Differentiable ℂ (smoothAFEZetaPoleRemainder s x) := by
  have hN : Differentiable ℂ (smoothAFEZetaPoleNumerator s x) :=
    differentiable_smoothAFEZetaPoleNumerator hx s
  have hQ : Differentiable ℂ (dslope (smoothAFEZetaPoleNumerator s x) 0) := by
    apply differentiableOn_univ.1
    rw [differentiableOn_dslope Filter.univ_mem]
    exact hN.differentiableOn
  apply differentiableOn_univ.1
  rw [smoothAFEZetaPoleRemainder, differentiableOn_dslope Filter.univ_mem]
  exact hQ.differentiableOn

theorem smoothAFEZetaPoleNumerator_zero
    {s : ℂ} (hs : s ≠ 1) (x : ℝ) :
    smoothAFEZetaPoleNumerator s x 0 = (s - 1) * riemannZeta s := by
  rw [smoothAFEZetaPoleNumerator, add_zero,
    regularizedRiemannZeta_of_ne_one hs]
  simp

theorem smoothAFEZetaPoleNumerator_shiftedPole
    (s : ℂ) (x : ℝ) :
    smoothAFEZetaPoleNumerator s x (1 - s) =
      (x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) := by
  rw [smoothAFEZetaPoleNumerator, show s + (1 - s) = 1 by ring,
    regularizedRiemannZeta_one, mul_one]

private theorem two_pole_quotient_decomposition
    {Nw N0 Nρ w ρ : ℂ} (hw : w ≠ 0) (hρ : ρ ≠ 0) (hwρ : w - ρ ≠ 0) :
    Nw / (w * (w - ρ)) =
      (-N0 / ρ) * w⁻¹ + (Nρ / ρ) * (w - ρ)⁻¹ +
        (((Nw - N0) / w) - ((Nρ - N0) / ρ)) / (w - ρ) := by
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hw, hρ, hwρ]
  ring

theorem smoothAFEZetaMellinIntegrand_eq_two_poles_add_remainder
    {s w : ℂ} {x : ℝ} (hs : s ≠ 1) (hw0 : w ≠ 0) (hwρ : w ≠ 1 - s) :
    smoothAFEZetaMellinIntegrand s x w =
      riemannZeta s * w⁻¹ +
        smoothAFEZetaShiftedPoleResidue s x * (w - (1 - s))⁻¹ +
          smoothAFEZetaPoleRemainder s x w := by
  have hρ0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hspole : s + w ≠ 1 := by
    intro h
    apply hwρ
    linear_combination h
  have hwρ0 : w - (1 - s) ≠ 0 := sub_ne_zero.mpr hwρ
  have hquot :
      smoothAFEZetaMellinIntegrand s x w =
        smoothAFEZetaPoleNumerator s x w /
          (w * (w - (1 - s))) := by
    rw [smoothAFEZetaMellinIntegrand, smoothAFEGaussianKernel,
      smoothAFEZetaPoleNumerator,
      regularizedRiemannZeta_of_ne_one hspole]
    have hcoord : s + w - 1 = w - (1 - s) := by ring
    rw [hcoord]
    field_simp [hw0, hwρ0]
  have hres0 :
      -smoothAFEZetaPoleNumerator s x 0 / (1 - s) =
        riemannZeta s := by
    rw [smoothAFEZetaPoleNumerator_zero hs]
    field_simp [hρ0]
    ring
  have hresρ :
      smoothAFEZetaPoleNumerator s x (1 - s) / (1 - s) =
        smoothAFEZetaShiftedPoleResidue s x := by
    rw [smoothAFEZetaPoleNumerator_shiftedPole,
      smoothAFEZetaShiftedPoleResidue]
  have hrem :
      smoothAFEZetaPoleRemainder s x w =
        (((smoothAFEZetaPoleNumerator s x w -
              smoothAFEZetaPoleNumerator s x 0) / w) -
            ((smoothAFEZetaPoleNumerator s x (1 - s) -
              smoothAFEZetaPoleNumerator s x 0) / (1 - s))) /
          (w - (1 - s)) := by
    rw [smoothAFEZetaPoleRemainder,
      dslope_of_ne _ hwρ, slope_def_field,
      dslope_of_ne _ hw0, slope_def_field,
      dslope_of_ne _ hρ0, slope_def_field]
    simp only [sub_zero]
  rw [hquot,
    two_pole_quotient_decomposition
      (N0 := smoothAFEZetaPoleNumerator s x 0)
      (Nρ := smoothAFEZetaPoleNumerator s x (1 - s))
      hw0 hρ0 hwρ0,
    hres0, hresρ, ← hrem]

end RHTower
