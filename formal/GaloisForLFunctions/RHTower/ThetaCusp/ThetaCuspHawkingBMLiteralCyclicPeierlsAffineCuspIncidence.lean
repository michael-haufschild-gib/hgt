import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticMixedCurrent

/-!
# Affine cusp incidence in the literal cyclic Peierls square-reader face

The literal square-reader cusp face has three distinct principal powers.  This
leaf computes their exact Weyl coefficients on an actual Xi occurrence.  Its
lower physical-reader coefficient vanishes exactly when the affine descendant
`2ρ - 1` is another completed-Lambda zero.  Such a descendant cannot lie left
of the critical line.

Proof-chain role:
`literal residual face -> coefficientwise B2 cancellation -> Λ(2ρ - 1) = 0`
`-> affine zero cannot be left of critical line -> reflection -> RH`.

This proves the algebraic and exterior-zero-free part of that chain.  It does
not assert the still-open coefficientwise metric-current boundary cancellation.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsAffineCuspIncidence

open Set
open D4BMCuspProjection D4BMGlobalAngularResponse D4BMQuadraticMixedSource

noncomputable section
set_option autoImplicit false

/-- Exact two-Weyl principal part at an actual Xi occurrence.  The coefficients
are `Λ(2ρ)` and `Λ(2ρ - 1)`, not `Λ(ρ)`. -/
theorem principal_center_weyl_coefficients (q : XiZeroCopy) (y : Ioi (0 : ℝ)) :
    principal (D4BMGlobalAngularResponse.center q) ![0, y.val] =
      reflectedCompletedLambda (2 * (q.1 : ℂ)) * (y.val : ℂ) ^ (q.1 : ℂ) +
        reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) *
          (y.val : ℂ) ^ (1 - (q.1 : ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent
      (D4BMGlobalAngularResponse.center q) false =
      1 - (q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign,
      D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent
      (D4BMGlobalAngularResponse.center q) true =
      (q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign,
      D4BMGlobalAngularResponse.center]
  have hminus : 2 * D4BMGlobalAngularResponse.center q =
      2 * (q.1 : ℂ) - 1 := by
    unfold D4BMGlobalAngularResponse.center
    ring
  rw [principal]
  simp only [d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor, mul_one, hm, hp,
    Matrix.cons_val_one, Matrix.cons_val_zero,
    d4BMCompletedEisensteinCuspConstantCoefficient]
  simp [hminus]
  ring

/-- Exact three-power expansion of the literal principal square. -/
theorem principal_center_square_weyl_coefficients (q : XiZeroCopy) (y : Ioi (0 : ℝ)) :
    principal (D4BMGlobalAngularResponse.center q) ![0, y.val] ^ (2 : ℕ) =
      reflectedCompletedLambda (2 * (q.1 : ℂ)) ^ (2 : ℕ) * (y.val : ℂ) ^ (2 * (q.1 : ℂ)) +
        (2 * reflectedCompletedLambda (2 * (q.1 : ℂ)) *
          reflectedCompletedLambda (2 * (q.1 : ℂ) - 1)) * (y.val : ℂ) +
        reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) *
          (y.val : ℂ) ^ (2 - 2 * (q.1 : ℂ)) := by
  rw [principal_center_weyl_coefficients]
  simpa using (cusp_power_square (q.1 : ℂ)
    (reflectedCompletedLambda (2 * (q.1 : ℂ)))
    (reflectedCompletedLambda (2 * (q.1 : ℂ) - 1)) ![0, y.val] y.property).symm

/-- The three principal powers cannot merge at an actual Xi occurrence. -/
theorem principal_weyl_exponents_pairwise_ne (q : XiZeroCopy) :
    2 * (q.1 : ℂ) ≠ 1 ∧
      2 * (q.1 : ℂ) ≠ 2 - 2 * (q.1 : ℂ) ∧
        1 ≠ 2 - 2 * (q.1 : ℂ) := by
  have him : ((q.1 : ℂ)).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  constructor
  · intro h
    have hi := congrArg Complex.im h
    norm_num [Complex.mul_im] at hi
    exact him (by linarith)
  constructor
  · intro h
    have hi := congrArg Complex.im h
    norm_num [Complex.mul_im, Complex.sub_im] at hi
    exact him (by linarith)
  · intro h
    have hi := congrArg Complex.im h
    norm_num [Complex.mul_im, Complex.sub_im] at hi
    exact him (by linarith)

/-- The physical reader's shifted completed-Lambda coefficient cannot vanish. -/
theorem reader_completion_ne_zero (q : XiZeroCopy) :
    reflectedCompletedLambda ((q.1 : ℂ) - 1) ≠ 0 := by
  have hi : ((q.1 : ℂ) - 1).im ≠ 0 := by
    simpa using xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    exact hi (by rw [h]; rfl)
  have he : reflectedCompletedLambda ((q.1 : ℂ) - 1) =
      completedRiemannZeta ((q.1 : ℂ) - 1) := by
    rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero h0]
    field_simp [gammaR_ne_zero_of_im_ne hi]
  have hr : 1 < (2 - (q.1 : ℂ)).re := by
    change 1 < 2 - (q.1 : ℂ).re
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  have hn : 2 - (q.1 : ℂ) ≠ 0 := by
    intro h
    have hj : (2 - (q.1 : ℂ)).im ≠ 0 := by
      simpa using neg_ne_zero.mpr (xi_divisor_support_im_ne_zero q.1)
    exact hj (by rw [h]; rfl)
  rw [he, ← completedRiemannZeta_one_sub ((q.1 : ℂ) - 1),
    show 1 - ((q.1 : ℂ) - 1) = 2 - (q.1 : ℂ) by ring]
  intro hz
  apply riemannZeta_ne_zero_of_one_lt_re hr
  rw [riemannZeta_def_of_ne_zero hn, hz, zero_div]

/-- The physical reader's vertical principal derivative has nonzero indicial
factor at every Xi occurrence. -/
theorem reader_power_ne_zero (q : XiZeroCopy) :
    1 - (q.1 : ℂ) / 2 ≠ 0 := by
  intro h
  have hq : (q.1 : ℂ) = 2 := by
    linear_combination -2 * h
  apply xi_divisor_support_im_ne_zero q.1
  have hi := congrArg Complex.im hq
  norm_num at hi ⊢
  exact hi

/-- Lower Weyl coefficient in the physical-reader square face. -/
def lowerWeylFaceCoefficient (q : XiZeroCopy) : ℂ :=
  (1 / 2 : ℂ) * reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) *
    reflectedCompletedLambda ((q.1 : ℂ) - 1) * (1 - (q.1 : ℂ) / 2)

/-- Vanishing of the lower physical-reader principal coefficient is exactly
the affine Xi-incidence condition that B2 must decide. -/
theorem lowerWeylFaceCoefficient_eq_zero_iff (q : XiZeroCopy) :
    lowerWeylFaceCoefficient q = 0 ↔
      reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) = 0 := by
  constructor
  · intro h
    by_contra hzero
    have hne : lowerWeylFaceCoefficient q ≠ 0 := by
      unfold lowerWeylFaceCoefficient
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 hzero))
          (reader_completion_ne_zero q))
        (reader_power_ne_zero q)
    exact hne h
  · intro h
    simp [lowerWeylFaceCoefficient, h]

/-- A zero of the affine lower coefficient cannot occur to the left of the
critical line. -/
theorem affine_lower_lambda_zero_not_left (q : XiZeroCopy) :
    ¬ (reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) = 0 ∧
      (q.1 : ℂ).re < 1 / 2) := by
  rintro ⟨hz, hq⟩
  have hsi : (2 * (q.1 : ℂ) - 1).im ≠ 0 := by
    intro h
    apply xi_divisor_support_im_ne_zero q.1
    norm_num [Complex.mul_im, Complex.sub_im] at h
    linarith
  have hs0 : 2 * (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    exact hsi (by rw [h]; rfl)
  have he : reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) =
      completedRiemannZeta (2 * (q.1 : ℂ) - 1) := by
    rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero hs0]
    field_simp [gammaR_ne_zero_of_im_ne hsi]
  have ht : 1 < (2 - 2 * (q.1 : ℂ)).re := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have hti : (2 - 2 * (q.1 : ℂ)).im ≠ 0 := by
    intro h
    apply xi_divisor_support_im_ne_zero q.1
    norm_num [Complex.mul_im, Complex.sub_im] at h
    linarith
  have ht0 : 2 - 2 * (q.1 : ℂ) ≠ 0 := by
    intro h
    exact hti (by rw [h]; rfl)
  have hne : reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ≠ 0 := by
    rw [he, ← completedRiemannZeta_one_sub (2 * (q.1 : ℂ) - 1),
      show 1 - (2 * (q.1 : ℂ) - 1) = 2 - 2 * (q.1 : ℂ) by ring]
    intro h
    apply riemannZeta_ne_zero_of_one_lt_re ht
    rw [riemannZeta_def_of_ne_zero ht0, h, zero_div]
  exact hne hz

end

end RHTower.D4BMLiteralCyclicPeierlsAffineCuspIncidence
