import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Reflection-folded Hedenmalm Dirac defect

The centered Xi function is even, so every Hedenmalm spectral parameter `alpha` is accompanied by
`-alpha`.  Folding the two removable Fourier solutions exposes an exact parity-graded first-order
system.  Reflection is no longer an identification to be supplied: the only remaining defect is
the single common theta source `XiC`.

This module proves the entire Fourier-side identities.  It does not assert a positive or
self-adjoint realization of the forced system.
-/

open Complex

noncomputable section

namespace RHTower

/-- Reflection-even fold of the two Hedenmalm removable Fourier solutions. -/
def xiHedenmalmEvenFold (alpha z : ℂ) : ℂ :=
  (xiThetaEigenFourier alpha z - xiThetaEigenFourier (-alpha) z) / 2

/-- Reflection-odd fold of the two Hedenmalm removable Fourier solutions. -/
def xiHedenmalmOddFold (alpha z : ℂ) : ℂ :=
  (xiThetaEigenFourier alpha z + xiThetaEigenFourier (-alpha) z) / 2

/-- Physical reflection exchanges the two Hedenmalm parameters with a minus sign. -/
theorem xiThetaEigenFourier_reflection
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    xiThetaEigenFourier alpha (-z) =
      -xiThetaEigenFourier (-alpha) z := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  by_cases hz : z = -alpha
  · subst z
    rw [neg_neg, xiThetaEigenFourier_self, xiThetaEigenFourier_self]
    have hderiv := iteratedDeriv_XiC_neg 1 alpha
    simp only [iteratedDeriv_one, pow_one] at hderiv
    rw [hderiv]
    ring
  · have hz' : -z ≠ alpha := by
      intro h
      apply hz
      calc
        z = -(-z) := by ring
        _ = -alpha := by rw [h]
    have hden : alpha + z ≠ 0 := by
      intro h
      apply hz
      linear_combination h
    rw [xiThetaEigenFourier_eq_div halpha hz',
      xiThetaEigenFourier_eq_div hneg hz, XiC_even]
    field_simp [hden]
    ring

/-- The difference fold is even under spectral reflection. -/
theorem xiHedenmalmEvenFold_neg
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    xiHedenmalmEvenFold alpha (-z) =
      xiHedenmalmEvenFold alpha z := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  rw [xiHedenmalmEvenFold, xiHedenmalmEvenFold,
    xiThetaEigenFourier_reflection halpha,
    xiThetaEigenFourier_reflection hneg]
  simp only [neg_neg]
  ring

/-- The sum fold is odd under spectral reflection. -/
theorem xiHedenmalmOddFold_neg
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    xiHedenmalmOddFold alpha (-z) =
      -xiHedenmalmOddFold alpha z := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  rw [xiHedenmalmOddFold, xiHedenmalmOddFold,
    xiThetaEigenFourier_reflection halpha,
    xiThetaEigenFourier_reflection hneg]
  simp only [neg_neg]
  ring

/-- The first folded Dirac equation.  The common Xi source cancels from the difference channel. -/
theorem xiHedenmalmEvenFold_equation
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    z * xiHedenmalmEvenFold alpha z =
      alpha * xiHedenmalmOddFold alpha z := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  have hp := xiThetaEigenFourier_equation halpha z
  have hm := xiThetaEigenFourier_equation hneg z
  unfold xiHedenmalmEvenFold xiHedenmalmOddFold
  linear_combination -(hp - hm) / 2

/-- The second folded Dirac equation.  All failure of a homogeneous reflected system is the one
literal completed theta source `XiC`. -/
theorem xiHedenmalmOddFold_equation
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    z * xiHedenmalmOddFold alpha z =
      alpha * xiHedenmalmEvenFold alpha z + I * XiC z := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  have hp := xiThetaEigenFourier_equation halpha z
  have hm := xiThetaEigenFourier_equation hneg z
  unfold xiHedenmalmEvenFold xiHedenmalmOddFold
  linear_combination -(hp + hm) / 2

/-- The even fold is a source-forced quadratic Helmholtz mode. -/
theorem xiHedenmalmEvenFold_quadratic
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    (z ^ 2 - alpha ^ 2) * xiHedenmalmEvenFold alpha z =
      I * alpha * XiC z := by
  have he := xiHedenmalmEvenFold_equation halpha z
  have ho := xiHedenmalmOddFold_equation halpha z
  calc
    (z ^ 2 - alpha ^ 2) * xiHedenmalmEvenFold alpha z =
        z * (z * xiHedenmalmEvenFold alpha z) -
          alpha * (alpha * xiHedenmalmEvenFold alpha z) := by ring
    _ = z * (alpha * xiHedenmalmOddFold alpha z) -
          alpha * (alpha * xiHedenmalmEvenFold alpha z) := by rw [he]
    _ = alpha *
          (z * xiHedenmalmOddFold alpha z -
            alpha * xiHedenmalmEvenFold alpha z) := by ring
    _ = I * alpha * XiC z := by rw [ho]; ring

/-- The odd fold is the companion source-forced quadratic Helmholtz mode. -/
theorem xiHedenmalmOddFold_quadratic
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    (z ^ 2 - alpha ^ 2) * xiHedenmalmOddFold alpha z =
      I * z * XiC z := by
  have he := xiHedenmalmEvenFold_equation halpha z
  have ho := xiHedenmalmOddFold_equation halpha z
  calc
    (z ^ 2 - alpha ^ 2) * xiHedenmalmOddFold alpha z =
        z * (z * xiHedenmalmOddFold alpha z) -
          alpha * (alpha * xiHedenmalmOddFold alpha z) := by ring
    _ = z * (alpha * xiHedenmalmEvenFold alpha z + I * XiC z) -
          alpha * (z * xiHedenmalmEvenFold alpha z) := by rw [ho, ← he]
    _ = I * z * XiC z := by ring

/-- No Xi zero is the centered origin. -/
theorem ne_zero_of_XiC_eq_zero {alpha : ℂ} (halpha : XiC alpha = 0) :
    alpha ≠ 0 := by
  intro hzero
  subst alpha
  exact XiC_zero_ne halpha

/-- At a Xi zero, the even reflection fold retains exactly half of the first Xi conormal. -/
theorem xiHedenmalmEvenFold_self
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiHedenmalmEvenFold alpha alpha = I * deriv XiC alpha / 2 := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  have hcross : xiThetaEigenFourier (-alpha) alpha = 0 := by
    apply xiThetaEigenFourier_eq_zero_of_XiC_eq_zero hneg halpha
    intro heq
    apply ne_zero_of_XiC_eq_zero halpha
    linear_combination heq
  rw [xiHedenmalmEvenFold, xiThetaEigenFourier_self, hcross]
  ring

/-- At a Xi zero, the odd reflection fold retains the same first Xi conormal. -/
theorem xiHedenmalmOddFold_self
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiHedenmalmOddFold alpha alpha = I * deriv XiC alpha / 2 := by
  have hneg : XiC (-alpha) = 0 := by
    rw [XiC_even]
    exact halpha
  have hcross : xiThetaEigenFourier (-alpha) alpha = 0 := by
    apply xiThetaEigenFourier_eq_zero_of_XiC_eq_zero hneg halpha
    intro heq
    apply ne_zero_of_XiC_eq_zero halpha
    linear_combination heq
  rw [xiHedenmalmOddFold, xiThetaEigenFourier_self, hcross]
  ring

/-- At a simple Xi zero, each parity channel is individually source-faithful. -/
theorem xiHedenmalmFolds_self_ne_zero_of_deriv_ne_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) (hderiv : deriv XiC alpha ≠ 0) :
    xiHedenmalmEvenFold alpha alpha ≠ 0 ∧
      xiHedenmalmOddFold alpha alpha ≠ 0 := by
  rw [xiHedenmalmEvenFold_self halpha, xiHedenmalmOddFold_self halpha]
  constructor <;> exact div_ne_zero (mul_ne_zero I_ne_zero hderiv) (by norm_num)

/-- The folded system is source-faithful: its even mode cannot vanish identically. -/
theorem xiHedenmalmEvenFold_ne_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiHedenmalmEvenFold alpha ≠ 0 := by
  intro hfold
  have hzero := xiHedenmalmOddFold_equation halpha 0
  rw [hfold] at hzero
  simp only [Pi.zero_apply, mul_zero, zero_mul, zero_add] at hzero
  exact XiC_zero_ne ((mul_eq_zero.mp hzero.symm).resolve_left I_ne_zero)

end RHTower
