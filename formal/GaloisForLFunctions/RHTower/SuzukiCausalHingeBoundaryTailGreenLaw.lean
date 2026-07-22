import GaloisForLFunctions.RHTower.SuzukiMarkedSecantMidpointLorentzCompletion

/-!
# Suzuki causal hinge boundary--tail Green law

On the positive half-line, one von-Mangoldt prime-power source is a delayed hinge
`a * (t - ell)₊`.  Its one-sided multiplier is `-a * exp (I*z*ell) / z^2`.
At finite aperture, direct integration of the compact Volterra triangle leaves one truncated
source tail and two boundary moments.  The algebraic cancellation is formalized below.

For delays beyond twice the aperture the triangle is zero, so the normalized jump retains the
pure far-prime atom `-I*a*exp(I*z*ell)/z^2`.  Its Pick diagonal has both signs in the upper half
plane: positive on the imaginary axis and negative at the phase-aligned point
`2*pi/ell + I*pi/ell`.  Multiplication by any nonzero compound denominator preserves the negative
diagonal.  Hence an atomwise direct-sum prime Gram cannot factor Suzuki's compound Bezoutian;
prime, Gamma/polar, and aperture-entry terms must be assembled before positivity.

No RH premise, positivity assumption, estimate, numerical computation, or Xi-zero data is used.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Delayed-hinge cancellation before the aperture limit -/

/-- One-sided Fourier--Laplace multiplier of the unit delayed hinge `(t-ell)₊`. -/
def suzukiDelayedHingeMultiplier (ell : ℝ) (z : ℂ) : ℂ :=
  -Complex.exp (Complex.I * z * (ell : ℂ)) / z ^ 2

/-- Closed form of the compact Volterra triangle after cutting the source at `c=a-ell`.
`Wlow` is the Fourier mass below the cut, while `A` and `B` are its first boundary moment and
mass. -/
def suzukiDelayedHingeTriangleFromCut
    (a ell : ℝ) (Wlow A B z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (a : ℂ)) *
      (A / (Complex.I * z) + B / z ^ 2) -
    Complex.exp (Complex.I * z * (ell : ℂ)) * Wlow / z ^ 2

/-- Right exterior after subtracting the compact triangle from multiplier times total source. -/
def suzukiDelayedHingeExteriorFromCut
    (a ell : ℝ) (Wlow Whigh A B z : ℂ) : ℂ :=
  suzukiDelayedHingeMultiplier ell z * (Wlow + Whigh) -
    suzukiDelayedHingeTriangleFromCut a ell Wlow A B z

/-- **Boundary--tail Green law.**  The low Fourier mass cancels exactly before any limit.  What
remains is the truncated upper source tail and two endpoint moments. -/
theorem suzukiDelayedHingeExteriorFromCut_eq_boundaryTail
    (a ell : ℝ) (Wlow Whigh A B z : ℂ) (hz : z ≠ 0) :
    suzukiDelayedHingeExteriorFromCut a ell Wlow Whigh A B z =
      -Complex.exp (Complex.I * z * (ell : ℂ)) * Whigh / z ^ 2 -
        Complex.exp (Complex.I * z * (a : ℂ)) *
          (A / (Complex.I * z) + B / z ^ 2) := by
  simp only [suzukiDelayedHingeExteriorFromCut, suzukiDelayedHingeMultiplier,
    suzukiDelayedHingeTriangleFromCut]
  field_simp [hz, Complex.I_ne_zero]
  ring

/-- At the aperture-entry wall the truncated mass and both boundary moments vanish, so the
boundary--tail law joins continuously to the pure far-delay multiplier. -/
theorem suzukiDelayedHingeExteriorFromCut_entryWall
    (a : ℝ) (W z : ℂ) :
    suzukiDelayedHingeExteriorFromCut a (2 * a) 0 W 0 0 z =
      suzukiDelayedHingeMultiplier (2 * a) z * W := by
  simp [suzukiDelayedHingeExteriorFromCut, suzukiDelayedHingeTriangleFromCut]

/-- A delay outside the local aperture is a pure global multiplier channel. -/
theorem suzukiDelayedHingeMultiplier_mul
    (ell : ℝ) (W z : ℂ) :
    suzukiDelayedHingeMultiplier ell z * W =
      -Complex.exp (Complex.I * z * (ell : ℂ)) * W / z ^ 2 := by
  simp [suzukiDelayedHingeMultiplier]
  ring_nf

/-! ## Xi-real far-prime jump atom -/

/-- Xi-real normalized jump contribution of one far prime-power hinge with positive coefficient
`weight`.  Physical multiplier is `-exp(I*z*ell)/z^2`; the jump is `I` times the right exterior. -/
def suzukiCriticalDelayedHingeJumpAtom
    (weight ell : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * (weight : ℂ) *
    Complex.exp (Complex.I * z * (ell : ℂ)) / z ^ 2

/-- Physical far exterior rotates to the Xi-real jump atom with the correct quarter-turn. -/
theorem I_mul_suzukiDelayedHingeMultiplier
    (weight ell : ℝ) (W z : ℂ) :
    Complex.I * ((weight : ℂ) * suzukiDelayedHingeMultiplier ell z * W) =
      suzukiCriticalDelayedHingeJumpAtom weight ell z * W := by
  simp [suzukiDelayedHingeMultiplier, suzukiCriticalDelayedHingeJumpAtom]
  ring

/-- Diagonal Pick kernel is exactly `Im m(z) / Im z`. -/
theorem suzukiScalarPickKernel_self_eq_im_div
    (m : ℂ → ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    suzukiScalarPickKernel m z z = ((m z).im / z.im : ℝ) := by
  apply Complex.ext
  · simp [suzukiScalarPickKernel, Complex.div_re, Complex.normSq_apply]
    field_simp [hz]
  · simp [suzukiScalarPickKernel, Complex.div_im, Complex.normSq_apply]

/-- The far-prime jump atom has positive imaginary part at a vertical upper-half-plane node. -/
theorem suzukiCriticalDelayedHingeJumpAtom_im_pos_vertical
    (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell) :
    0 < (suzukiCriticalDelayedHingeJumpAtom weight ell
      (Complex.I * (Real.pi / ell : ℝ))).im := by
  have hell0 : ell ≠ 0 := ne_of_gt hell
  rw [suzukiCriticalDelayedHingeJumpAtom]
  simp [Complex.div_im, Complex.exp_re, Complex.exp_im, hell0]
  norm_num [pow_two, Complex.mul_re]
  positivity

/-- At the phase-aligned upper-half-plane node `2*pi/ell + I*pi/ell`, the same atom has strictly
negative imaginary part. -/
theorem suzukiCriticalDelayedHingeJumpAtom_im_neg_phaseAligned
    (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell) :
    (suzukiCriticalDelayedHingeJumpAtom weight ell
      ((2 * Real.pi / ell : ℝ) +
        Complex.I * (Real.pi / ell : ℝ))).im < 0 := by
  have hell0 : ell ≠ 0 := ne_of_gt hell
  rw [suzukiCriticalDelayedHingeJumpAtom]
  simp [Complex.div_im, Complex.exp_re, Complex.exp_im, hell0]
  norm_num [pow_two, Complex.mul_re]
  have hnorm : 0 < Complex.normSq
      (2 * (Real.pi : ℂ) / (ell : ℂ) +
        Complex.I * ((Real.pi : ℂ) / (ell : ℂ))) := by
    rw [Complex.normSq_apply]
    norm_num
    positivity
  have hnum : 0 <
      2 * Real.pi / ell * (2 * Real.pi / ell) -
        Real.pi / ell * (Real.pi / ell) := by
    rw [show 2 * Real.pi / ell * (2 * Real.pi / ell) -
        Real.pi / ell * (Real.pi / ell) = 3 * (Real.pi / ell) ^ 2 by ring]
    positivity
  have hden : 0 <
      Complex.normSq (2 * (Real.pi : ℂ) / (ell : ℂ) +
          Complex.I * ((Real.pi : ℂ) / (ell : ℂ))) *
        Complex.normSq (2 * (Real.pi : ℂ) / (ell : ℂ) +
          Complex.I * ((Real.pi : ℂ) / (ell : ℂ))) :=
    mul_pos hnorm hnorm
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (mul_pos (mul_pos hweight (Real.exp_pos _)) hnum)) hden

/-- The far-prime Pick diagonal is strictly positive at the vertical node. -/
theorem suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_pos_vertical
    (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell) :
    0 < (suzukiScalarPickKernel
      (suzukiCriticalDelayedHingeJumpAtom weight ell)
      (Complex.I * (Real.pi / ell : ℝ))
      (Complex.I * (Real.pi / ell : ℝ))).re := by
  rw [suzukiScalarPickKernel_self_eq_im_div _ _ (by simp; positivity)]
  simp only [ofReal_re]
  exact div_pos
    (suzukiCriticalDelayedHingeJumpAtom_im_pos_vertical weight ell hweight hell)
    (by simp; positivity)

/-- **Atomwise Gram falsifier.**  The same far-prime Pick diagonal is strictly negative at a
phase-aligned node in the upper half-plane. -/
theorem suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_neg_phaseAligned
    (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell) :
    (suzukiScalarPickKernel
      (suzukiCriticalDelayedHingeJumpAtom weight ell)
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))).re < 0 := by
  rw [suzukiScalarPickKernel_self_eq_im_div _ _ (by simp; positivity)]
  simp only [ofReal_re]
  exact div_neg_of_neg_of_pos
    (suzukiCriticalDelayedHingeJumpAtom_im_neg_phaseAligned weight ell hweight hell)
    (by simp; positivity)

/-! ## Compound-denominator sign preservation -/

/-- Pick kernel after the positive diagonal congruence contributed by a compound denominator. -/
def suzukiCompoundDenominatorScaledPick
    (D m : ℂ → ℂ) (z w : ℂ) : ℂ :=
  D z * (starRingEnd ℂ) (D w) * suzukiScalarPickKernel m z w

/-- On the diagonal, compound-denominator scaling is multiplication by `normSq (D z)`. -/
theorem suzukiCompoundDenominatorScaledPick_self_eq
    (D m : ℂ → ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    suzukiCompoundDenominatorScaledPick D m z z =
      (Complex.normSq (D z) * ((m z).im / z.im) : ℝ) := by
  rw [suzukiCompoundDenominatorScaledPick,
    suzukiScalarPickKernel_self_eq_im_div m z hz]
  rw [show D z * (starRingEnd ℂ) (D z) = (Complex.normSq (D z) : ℝ) by
    exact Complex.mul_conj (D z)]
  push_cast
  ring

/-- A nonzero compound denominator cannot repair the negative phase-aligned far-prime diagonal. -/
theorem suzukiCompoundDenominatorScaledPick_delayedHinge_neg_phaseAligned
    (D : ℂ → ℂ) (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell)
    (hD : D ((2 * Real.pi / ell : ℝ) +
      Complex.I * (Real.pi / ell : ℝ)) ≠ 0) :
    (suzukiCompoundDenominatorScaledPick D
      (suzukiCriticalDelayedHingeJumpAtom weight ell)
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))).re < 0 := by
  rw [suzukiCompoundDenominatorScaledPick_self_eq _ _ _ (by simp; positivity)]
  simp only [ofReal_re]
  exact mul_neg_of_pos_of_neg
    ((Complex.normSq_pos).2 hD)
    (div_neg_of_neg_of_pos
      (suzukiCriticalDelayedHingeJumpAtom_im_neg_phaseAligned
        weight ell hweight hell)
      (by simp; positivity))

end

end RHTower
