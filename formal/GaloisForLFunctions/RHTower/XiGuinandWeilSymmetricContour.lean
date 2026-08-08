import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle

/-!
# Symmetric Euler-line contour for the rectangular Guinand--Weil test

The centered completed function XiC and the rectangular two-edge transform are even. Hence the
rectangular test multiplied by XiC'/XiC is odd. On a rectangle symmetric about the origin this
folds both the top edge onto the bottom Euler edge and the left edge onto the right edge.

The bottom edge lies in the absolutely convergent prime half-plane as soon as its depth is greater
than 1/2. The last theorem identifies its logarithmic derivative pointwise with the honest
von-Mangoldt L-series minus the completed archimedean logarithmic derivative. These identities
reduce the remaining rectangular explicit-formula proof to Fourier inversion on the bottom edge
and decay of one vertical edge.
-/

open Complex Function intervalIntegral Set

namespace RHTower

noncomputable section

/-- The bilateral two-edge transform is even in its Laplace variable. -/
theorem rectangularTwoEdgeTransform_neg (L a : ℝ) (w : ℂ) :
    rectangularTwoEdgeTransform L a (-w) = rectangularTwoEdgeTransform L a w :=
  rectangularTwoEdgeTransform_even L a w

/-- The centered Xi-coordinate form of the rectangular transform is even. -/
theorem xiRectangularTwoEdgeTransform_neg (L a : ℝ) (z : ℂ) :
    xiRectangularTwoEdgeTransform L a (-z) =
      xiRectangularTwoEdgeTransform L a z := by
  rw [xiRectangularTwoEdgeTransform, xiRectangularTwoEdgeTransform]
  have harg : I * -z = -(I * z) := by ring
  rw [harg, rectangularTwoEdgeTransform_neg]

/-- The logarithmic derivative of the centered even function XiC is odd. -/
theorem logDeriv_XiC_neg (z : ℂ) :
    logDeriv XiC (-z) = -logDeriv XiC z := by
  rw [logDeriv_XiC_eq_mul_I_logDeriv_xi,
    logDeriv_XiC_eq_mul_I_logDeriv_xi]
  have hcoord : 1 / 2 + -z * I = 1 - (1 / 2 + z * I) := by ring
  rw [hcoord, logDeriv_xi_reciprocity]
  ring

/-- The squared rectangular test times the completed logarithmic derivative is odd. -/
theorem rectangularLogDerivIntegrand_neg (L a : ℝ) (z : ℂ) :
    xiRectangularTwoEdgeTransform L a (-z) ^ 2 * logDeriv XiC (-z) =
      -(xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z) := by
  rw [xiRectangularTwoEdgeTransform_neg, logDeriv_XiC_neg]
  ring

/-- An odd complex function folds the upper horizontal edge of a symmetric rectangle onto the
negative of its lower horizontal edge. -/
theorem intervalIntegral_horizontal_neg_of_odd
    (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (R c : ℝ) :
    (∫ x in -R..R, f ((x : ℂ) + c * I)) =
      -(∫ x in -R..R, f ((x : ℂ) - c * I)) := by
  calc
    (∫ x in -R..R, f ((x : ℂ) + c * I)) =
        ∫ x in -R..R, -f ((-x : ℂ) - c * I) := by
          apply intervalIntegral.integral_congr
          intro x _
          have harg : -((x : ℂ) + c * I) = (-x : ℂ) - c * I := by ring
          have hrev := hodd (-((x : ℂ) + c * I))
          simp only [neg_neg] at hrev
          rw [harg] at hrev
          exact hrev
    _ = -(∫ x in -R..R, f ((-x : ℂ) - c * I)) := by
          rw [intervalIntegral.integral_neg]
    _ = -(∫ x in -R..R, f ((x : ℂ) - c * I)) := by
          have hcomp := intervalIntegral.integral_comp_neg
            (f := fun x : ℝ => f ((x : ℂ) - c * I)) (a := -R) (b := R)
          simpa only [neg_neg, ofReal_neg] using congrArg Neg.neg hcomp

/-- An odd complex function folds the left vertical edge of a symmetric rectangle onto the
negative of its right vertical edge. -/
theorem intervalIntegral_vertical_neg_of_odd
    (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (R c : ℝ) :
    (∫ y in -c..c, f (((-R : ℝ) : ℂ) + y * I)) =
      -(∫ y in -c..c, f ((R : ℂ) + y * I)) := by
  calc
    (∫ y in -c..c, f (((-R : ℝ) : ℂ) + y * I)) =
        ∫ y in -c..c, -f ((R : ℂ) + (-y) * I) := by
          apply intervalIntegral.integral_congr
          intro y _
          have harg : -(((R : ℝ) : ℂ) + (-y) * I) =
              (((-R : ℝ) : ℂ) + y * I) := by
            push_cast
            ring
          have hrev := hodd (((R : ℝ) : ℂ) + (-y) * I)
          rw [harg] at hrev
          exact hrev
    _ = -(∫ y in -c..c, f ((R : ℂ) + (-y) * I)) := by
          rw [intervalIntegral.integral_neg]
    _ = -(∫ y in -c..c, f ((R : ℂ) + y * I)) := by
          have hcomp := intervalIntegral.integral_comp_neg
            (f := fun y : ℝ => f ((R : ℂ) + y * I)) (a := -c) (b := c)
          simpa only [neg_neg, ofReal_neg] using congrArg Neg.neg hcomp

/-- The upper rectangular logarithmic-derivative edge is the negative lower edge. -/
theorem rectangularLogDeriv_horizontal_fold (L a R c : ℝ) :
    (∫ x in -R..R,
        xiRectangularTwoEdgeTransform L a ((x : ℂ) + c * I) ^ 2 *
          logDeriv XiC ((x : ℂ) + c * I)) =
      -(∫ x in -R..R,
        xiRectangularTwoEdgeTransform L a ((x : ℂ) - c * I) ^ 2 *
          logDeriv XiC ((x : ℂ) - c * I)) := by
  exact intervalIntegral_horizontal_neg_of_odd
    (fun z => xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z)
    (rectangularLogDerivIntegrand_neg L a) R c

/-- A symmetric rectangle integral of an odd function is twice one bottom edge plus one right
edge. -/
theorem rectIntegral_symmetric_eq_two_bottom_add_vertical
    (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (R c : ℝ) :
    rectIntegral f (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * ((∫ x in -R..R, f ((x : ℂ) - c * I)) +
        I • (∫ y in -c..c, f ((R : ℂ) + y * I))) := by
  have hz₁re : ((((-R : ℝ) : ℂ) - c * I)).re = -R := by
    simp [Complex.mul_re]
  have hz₁im : ((((-R : ℝ) : ℂ) - c * I)).im = -c := by
    simp [Complex.mul_im]
  have hz₂re : ((((R : ℝ) : ℂ) + c * I)).re = R := by
    simp [Complex.mul_re]
  have hz₂im : ((((R : ℝ) : ℂ) + c * I)).im = c := by
    simp [Complex.mul_im]
  have hbottom :
      (∫ x in -R..R, f ((x : ℂ) - c * I)) =
        ∫ x in -R..R, f (-(c * I) + (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hbottomNeg :
      (∫ x in -R..R, f ((x : ℂ) + (-c : ℂ) * I)) =
        ∫ x in -R..R, f ((x : ℂ) - c * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  unfold rectIntegral
  rw [hz₁re, hz₁im, hz₂re, hz₂im]
  simp only [sub_eq_add_neg, ofReal_neg]
  rw [intervalIntegral_horizontal_neg_of_odd f hodd R c]
  have hvertical := intervalIntegral_vertical_neg_of_odd f hodd R c
  simp only [ofReal_neg] at hvertical
  rw [hvertical]
  simp only [smul_eq_mul]
  linear_combination hbottomNeg

/-- Symmetric-contour reduction for the exact squared rectangular Xi test. -/
theorem rectIntegral_rectangularLogDeriv_symmetric (L a R c : ℝ) :
    rectIntegral
        (fun z => xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * ((∫ x in -R..R,
          xiRectangularTwoEdgeTransform L a ((x : ℂ) - c * I) ^ 2 *
            logDeriv XiC ((x : ℂ) - c * I)) +
        I • (∫ y in -c..c,
          xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ 2 *
            logDeriv XiC ((R : ℂ) + y * I))) := by
  exact rectIntegral_symmetric_eq_two_bottom_add_vertical
    (fun z => xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z)
    (rectangularLogDerivIntegrand_neg L a) R c

/-- Below depth 1/2, the symmetric contour's bottom edge is exactly the honest von-Mangoldt
L-series minus the completed archimedean logarithmic derivative. -/
theorem logDeriv_XiC_bottom_eq_primeArch
    {c : ℝ} (hc : 1 / 2 < c) (x : ℝ) :
    logDeriv XiC ((x : ℂ) - c * I) =
      -I *
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (((1 / 2 + c : ℝ) : ℂ) + x * I) -
          logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)) := by
  let z : ℂ := (x : ℂ) - c * I
  have hcoord : 1 / 2 + z * I = (((1 / 2 + c : ℝ) : ℂ) + x * I) := by
    dsimp only [z]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hs : 1 < (1 / 2 + z * I).re := by
    rw [hcoord]
    simp
    linarith
  have hadm := XiExplicitAdmissible_of_one_lt_re hs
  have hXi := XiC_ne_zero_of_admissible hadm
  rw [logDeriv_XiC_eq_relativeResolventTrace hXi,
    ← primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hs,
    primeArchSourceRelativeTrace, hcoord]

end

end RHTower
