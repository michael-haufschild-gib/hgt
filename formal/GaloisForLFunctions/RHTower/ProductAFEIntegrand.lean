import GaloisForLFunctions.RHTower.RectangleThreePoleResidue
import GaloisForLFunctions.RHTower.SmoothAFEZetaResidueDecomposition

/-!
# The product zeta Mellin integrand and its three-pole decomposition

For two base points `s₁, s₂` the Gaussian Mellin integrand of the product `ζ(s₁+w)ζ(s₂+w)` is

`ζ(s₁+w) ζ(s₂+w) x^w e^{w²} / w`.

Filling both zeta poles gives the entire numerator
`N(w) = x^w e^{w²} ((s₁+w−1)ζ(s₁+w)) ((s₂+w−1)ζ(s₂+w))`, and away from `w = 0, 1−s₁, 1−s₂` the
integrand is `N(w) / (w (w−(1−s₁)) (w−(1−s₂)))`.  Three iterated divided differences split this
exactly into three Cauchy kernels and an entire remainder.  The residues are `ζ(s₁)ζ(s₂)` at `0`,
`x^{1−s₁} e^{(1−s₁)²} ζ(s₂+1−s₁)/(1−s₁)` at `1−s₁`, and the symmetric value at `1−s₂`.  The
rectangle residue theorem then gives the finite contour identity.
-/

noncomputable section

namespace RHTower

open Complex Set

/-- `ζ(s₁+w) ζ(s₂+w) x^w e^{w²}/w`. -/
def productAFEIntegrand (s₁ s₂ : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (s₁ + w) * riemannZeta (s₂ + w) * (x : ℂ) ^ w * smoothAFEGaussianKernel w

/-- The entire numerator `x^w e^{w²} ((s₁+w−1)ζ(s₁+w)) ((s₂+w−1)ζ(s₂+w))`. -/
def productAFEPoleNumerator (s₁ s₂ : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ w * Complex.exp (w ^ 2) * regularizedRiemannZeta (s₁ + w) *
    regularizedRiemannZeta (s₂ + w)

/-- The entire remainder: the third divided difference of the numerator at `0, 1−s₁, 1−s₂`. -/
def productAFEPoleRemainder (s₁ s₂ : ℂ) (x : ℝ) : ℂ → ℂ :=
  dslope (dslope (dslope (productAFEPoleNumerator s₁ s₂ x) 0) (1 - s₁)) (1 - s₂)

/-- The residue at `w = 1 − s₁`: `x^{1−s₁} e^{(1−s₁)²} ζ(s₂ + 1 − s₁)/(1 − s₁)`. -/
def productAFEShiftedResidue (s₁ s₂ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (1 - s₁) * Complex.exp ((1 - s₁) ^ 2) * riemannZeta (s₂ + (1 - s₁)) / (1 - s₁)

theorem differentiable_productAFEPoleNumerator {x : ℝ} (hx : 0 < x) (s₁ s₂ : ℂ) :
    Differentiable ℂ (productAFEPoleNumerator s₁ s₂ x) := by
  haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  exact ((((differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_id).mul
    (differentiable_exp.comp (differentiable_pow 2))).mul
      (differentiable_regularizedRiemannZeta.comp (by fun_prop))).mul
      (differentiable_regularizedRiemannZeta.comp (by fun_prop))

theorem differentiable_dslope_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  apply differentiableOn_univ.1
  rw [differentiableOn_dslope Filter.univ_mem]
  exact hf.differentiableOn

theorem differentiable_productAFEPoleRemainder {x : ℝ} (hx : 0 < x) (s₁ s₂ : ℂ) :
    Differentiable ℂ (productAFEPoleRemainder s₁ s₂ x) :=
  differentiable_dslope_of_differentiable (differentiable_dslope_of_differentiable
    (differentiable_dslope_of_differentiable (differentiable_productAFEPoleNumerator hx s₁ s₂) 0)
    (1 - s₁)) (1 - s₂)

theorem productAFEPoleNumerator_zero {s₁ s₂ : ℂ} (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (x : ℝ) :
    productAFEPoleNumerator s₁ s₂ x 0 =
      (s₁ - 1) * riemannZeta s₁ * ((s₂ - 1) * riemannZeta s₂) := by
  rw [productAFEPoleNumerator, add_zero, add_zero, regularizedRiemannZeta_of_ne_one h₁,
    regularizedRiemannZeta_of_ne_one h₂]
  have h0 : (x : ℂ) ^ (0 : ℂ) * Complex.exp ((0 : ℂ) ^ 2) = 1 := by simp
  calc (x : ℂ) ^ (0 : ℂ) * Complex.exp ((0 : ℂ) ^ 2) * ((s₁ - 1) * riemannZeta s₁)
        * ((s₂ - 1) * riemannZeta s₂)
      = ((x : ℂ) ^ (0 : ℂ) * Complex.exp ((0 : ℂ) ^ 2))
        * ((s₁ - 1) * riemannZeta s₁ * ((s₂ - 1) * riemannZeta s₂)) := by ring
    _ = _ := by rw [h0, one_mul]

theorem productAFEPoleNumerator_shiftedPole {s₁ s₂ : ℂ} (hne : s₁ ≠ s₂) (x : ℝ) :
    productAFEPoleNumerator s₁ s₂ x (1 - s₁) =
      (x : ℂ) ^ (1 - s₁) * Complex.exp ((1 - s₁) ^ 2)
        * ((s₂ - s₁) * riemannZeta (s₂ + (1 - s₁))) := by
  have h : s₂ + (1 - s₁) ≠ 1 := by
    intro h
    apply hne
    linear_combination -h
  rw [productAFEPoleNumerator, show s₁ + (1 - s₁) = 1 by ring, regularizedRiemannZeta_one,
    regularizedRiemannZeta_of_ne_one h, mul_one, show s₂ + (1 - s₁) - 1 = s₂ - s₁ by ring]

theorem productAFEPoleNumerator_shiftedPole' {s₁ s₂ : ℂ} (hne : s₁ ≠ s₂) (x : ℝ) :
    productAFEPoleNumerator s₁ s₂ x (1 - s₂) =
      (x : ℂ) ^ (1 - s₂) * Complex.exp ((1 - s₂) ^ 2)
        * ((s₁ - s₂) * riemannZeta (s₁ + (1 - s₂))) := by
  have h : s₁ + (1 - s₂) ≠ 1 := by
    intro h
    apply hne
    linear_combination h
  rw [productAFEPoleNumerator, show s₂ + (1 - s₂) = 1 by ring, regularizedRiemannZeta_one,
    regularizedRiemannZeta_of_ne_one h, mul_one, show s₁ + (1 - s₂) - 1 = s₁ - s₂ by ring]

private theorem three_pole_quotient_decomposition
    {Nw N0 N1 N2 w a b : ℂ} (hw : w ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (hwa : w - a ≠ 0) (hwb : w - b ≠ 0) :
    Nw / (w * (w - a) * (w - b)) =
      (N0 / (a * b)) * w⁻¹ + (N1 / (a * (a - b))) * (w - a)⁻¹ + (N2 / (b * (b - a))) * (w - b)⁻¹ +
      (((Nw - N0) / w - (N1 - N0) / a) / (w - a) - ((N2 - N0) / b - (N1 - N0) / a) / (b - a))
        / (w - b) := by
  have hba : b - a ≠ 0 := by
    intro h
    apply hab
    linear_combination -h
  rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div]
  field_simp
  ring

/-- **Three-pole decomposition of the product integrand.** -/
theorem productAFEIntegrand_eq_three_poles_add_remainder {s₁ s₂ w : ℂ} {x : ℝ}
    (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂)
    (hw0 : w ≠ 0) (hw1 : w ≠ 1 - s₁) (hw2 : w ≠ 1 - s₂) :
    productAFEIntegrand s₁ s₂ x w =
      riemannZeta s₁ * riemannZeta s₂ * w⁻¹ +
        (productAFEShiftedResidue s₁ s₂ x * (w - (1 - s₁))⁻¹ +
          (productAFEShiftedResidue s₂ s₁ x * (w - (1 - s₂))⁻¹ +
            productAFEPoleRemainder s₁ s₂ x w)) := by
  set N := productAFEPoleNumerator s₁ s₂ x with hN
  have hρ₁ : (1 : ℂ) - s₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  have hρ₂ : (1 : ℂ) - s₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂)
  have hρ₁₂ : (1 - s₁) - (1 - s₂) ≠ 0 := by
    intro h
    apply hne
    linear_combination -h
  have hρ₂₁ : (1 - s₂) ≠ (1 - s₁) := by
    intro h
    apply hne
    linear_combination h
  have hwρ₁ : w - (1 - s₁) ≠ 0 := sub_ne_zero.mpr hw1
  have hwρ₂ : w - (1 - s₂) ≠ 0 := sub_ne_zero.mpr hw2
  have hs₁w : s₁ + w ≠ 1 := by
    intro h
    apply hw1
    linear_combination h
  have hs₂w : s₂ + w ≠ 1 := by
    intro h
    apply hw2
    linear_combination h
  have hquot : productAFEIntegrand s₁ s₂ x w = N w / (w * (w - (1 - s₁)) * (w - (1 - s₂))) := by
    rw [hN, productAFEIntegrand, smoothAFEGaussianKernel, productAFEPoleNumerator,
      regularizedRiemannZeta_of_ne_one hs₁w, regularizedRiemannZeta_of_ne_one hs₂w,
      show s₁ + w - 1 = w - (1 - s₁) by ring, show s₂ + w - 1 = w - (1 - s₂) by ring]
    field_simp
  have hrem : productAFEPoleRemainder s₁ s₂ x w =
      (((N w - N 0) / w - (N (1 - s₁) - N 0) / (1 - s₁)) / (w - (1 - s₁))
        - ((N (1 - s₂) - N 0) / (1 - s₂) - (N (1 - s₁) - N 0) / (1 - s₁)) / ((1 - s₂) - (1 - s₁)))
        / (w - (1 - s₂)) := by
    rw [productAFEPoleRemainder, ← hN, dslope_of_ne _ hw2, slope_def_field,
      dslope_of_ne _ hw1, dslope_of_ne _ hρ₂₁, slope_def_field, slope_def_field,
      dslope_of_ne _ hw0, dslope_of_ne _ hρ₁, dslope_of_ne _ hρ₂, slope_def_field,
      slope_def_field, slope_def_field, sub_zero, sub_zero, sub_zero]
  have hres0 : N 0 / ((1 - s₁) * (1 - s₂)) = riemannZeta s₁ * riemannZeta s₂ := by
    rw [hN, productAFEPoleNumerator_zero h₁ h₂]
    field_simp
    ring
  have hres1 : N (1 - s₁) / ((1 - s₁) * ((1 - s₁) - (1 - s₂))) = productAFEShiftedResidue s₁ s₂ x := by
    rw [hN, productAFEPoleNumerator_shiftedPole hne, productAFEShiftedResidue]
    have hs : s₂ - s₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    field_simp
    ring
  have hres2 : N (1 - s₂) / ((1 - s₂) * ((1 - s₂) - (1 - s₁))) = productAFEShiftedResidue s₂ s₁ x := by
    rw [hN, productAFEPoleNumerator_shiftedPole' hne, productAFEShiftedResidue]
    have hs : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  rw [hquot, three_pole_quotient_decomposition hw0 hρ₁ hρ₂ hρ₁₂ hwρ₁ hwρ₂, hres0, hres1, hres2,
    ← hrem]
  ring

/-- **The finite rectangle identity for the product integrand.** -/
theorem rectIntegral_productAFEIntegrand_eq {s₁ s₂ : ℂ} {x : ℝ} {z₁ z₂ : ℂ} (hx : 0 < x)
    (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂)
    (h01 : z₁.re < 0) (h02 : 0 < z₂.re) (h03 : z₁.im < 0) (h04 : 0 < z₂.im)
    (hρ1 : z₁.re < (1 - s₁).re) (hρ2 : (1 - s₁).re < z₂.re)
    (hρ3 : z₁.im < (1 - s₁).im) (hρ4 : (1 - s₁).im < z₂.im)
    (hσ1 : z₁.re < (1 - s₂).re) (hσ2 : (1 - s₂).re < z₂.re)
    (hσ3 : z₁.im < (1 - s₂).im) (hσ4 : (1 - s₂).im < z₂.im) :
    rectIntegral (productAFEIntegrand s₁ s₂ x) z₁ z₂ =
      2 * Real.pi * I * (riemannZeta s₁ * riemannZeta s₂ +
        productAFEShiftedResidue s₁ s₂ x + productAFEShiftedResidue s₂ s₁ x) := by
  apply rectIntegral_eq_three_pole_residues (p := 0) (q := 1 - s₁) (r := 1 - s₂)
    (R := productAFEPoleRemainder s₁ s₂ x) h01 h02 h03 h04 hρ1 hρ2 hρ3 hρ4 hσ1 hσ2 hσ3 hσ4
    (differentiable_productAFEPoleRemainder hx s₁ s₂)
  intro z hz0 hz1 hz2
  simpa only [sub_zero] using
    productAFEIntegrand_eq_three_poles_add_remainder (x := x) h₁ h₂ hne hz0 hz1 hz2

end RHTower

end
