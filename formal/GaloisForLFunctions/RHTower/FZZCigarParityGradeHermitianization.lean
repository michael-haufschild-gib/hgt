import GaloisForLFunctions.RHTower.FZZCigarParityHermitianChiralOrientationClassification

/-!
# Exact Hermitianization of the FZZ parity grade crossing

Two source-side orientation mechanisms had previously appeared separate.  The literal FZZ Krein
grade crossing `C_beta(u)=B_beta(u,D u)` has an oriented imaginary part, while the complete
Hermitian reporter classification shows that only the imaginary off-diagonal coefficient can see
complex-conjugate states.  They are in fact the same mechanism on every two-coordinate state:

`2 Im(C_beta(u)) = -Q(beta) H_chiral(u)`.

Here `H_chiral` is the unit Hermitian block `[[0,i],[-i,0]]`; its scalar value is real.  At every
positive scale `Q(beta)>0`, so positive and negative grade chambers are exactly the opposite
Hermitian chiral chambers.  More generally, the antiunitary-odd part of an arbitrary Hermitian
reporter is `2c H_chiral`.  Hence such a reporter is antiunitary-blind on `u` exactly when either
its chiral coefficient vanishes or the literal FZZ grade crossing lies on its zero wall.

This eliminates a separate finite-block Hermitian producer from the FZZ-P burden: the source grade
already contains the unique chiral reporter.  It does not construct the still-missing interacting
FZZ/GFZZ divisor incidence law.  Targeted searches of FZZ duality, cigar spectral-asymmetry, and
general Krein-signature literature located no source-specific identity of this form.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every Hermitian reporter splits into its real-symmetric part plus its chiral coefficient times
the unit imaginary off-diagonal reporter. -/
theorem fzzCigarParityHermitianQuadraticObservable_sub_realSymmetric
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d u -
        fzzCigarParityHermitianQuadraticObservable a b 0 d u =
      (c : ℂ) * fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u := by
  simp [fzzCigarParityHermitianQuadraticObservable]
  ring

/-- Exact antiunitary-odd decomposition: conjugation cancels the whole real-symmetric reporter and
doubles only its chiral component. -/
theorem fzzCigarParityHermitianQuadraticObservable_antiunitaryOddPart
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d u -
        fzzCigarParityHermitianQuadraticObservable a b c d
          (star u.1, star u.2) =
      (2 * c : ℂ) *
        fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u := by
  rw [fzzCigarParityHermitianQuadraticObservable_conjugate_eq_neg_chiral]
  simp [fzzCigarParityHermitianQuadraticObservable]
  ring

/-- **FZZ grade Hermitianization law.**  On every state and at every real scale, the imaginary
grade crossing is exactly `-Q(beta)/2` times the unit chiral Hermitian reporter. -/
theorem fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral
    (beta : ℝ) (u : ℂ × ℂ) :
    2 * (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im =
      -fzzKreinQAt beta *
        (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re := by
  rw [fzzCigarParityDilatedTwoScaleGradeCrossing,
    fzzCigarParityDilatedTwoScaleGrade,
    fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityHermitianQuadraticObservable]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/-- At positive scale the Hermitian chiral reporter is the source-normalized imaginary grade
crossing. -/
theorem fzzCigarParityHermitianUnitChiral_eq_normalizedGradeCrossing
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re =
      -2 * (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im /
        fzzKreinQAt beta := by
  have hQ := fzzKreinQAt_pos hbeta
  have h := fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral beta u
  field_simp
  nlinarith

/-- Positive FZZ grade chamber equals the negative unit-chiral Hermitian chamber for every state. -/
theorem fzzCigarParityDilatedTwoScaleGradeCrossing_im_pos_iff_chiral_neg
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    0 < (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im ↔
      (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re < 0 := by
  have hQ := fzzKreinQAt_pos hbeta
  have h := fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral beta u
  constructor
  · intro hcross
    by_contra hnot
    have hobs : 0 ≤
        (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re :=
      le_of_not_gt hnot
    have hprod := mul_nonneg hQ.le hobs
    nlinarith
  · intro hobs
    have hprod : fzzKreinQAt beta *
        (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re < 0 :=
      mul_neg_of_pos_of_neg hQ hobs
    nlinarith

/-- Negative FZZ grade chamber equals the positive unit-chiral Hermitian chamber for every state. -/
theorem fzzCigarParityDilatedTwoScaleGradeCrossing_im_neg_iff_chiral_pos
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im < 0 ↔
      0 < (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re := by
  have hQ := fzzKreinQAt_pos hbeta
  have h := fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral beta u
  constructor
  · intro hcross
    by_contra hnot
    have hobs :
        (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re ≤ 0 :=
      le_of_not_gt hnot
    have hprod := mul_nonpos_of_nonneg_of_nonpos hQ.le hobs
    nlinarith
  · intro hobs
    have hprod : 0 < fzzKreinQAt beta *
        (fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u).re :=
      mul_pos hQ hobs
    nlinarith

/-- The unit chiral Hermitian zero wall is exactly the imaginary-grade zero wall. -/
theorem fzzCigarParityHermitianUnitChiral_eq_zero_iff_gradeCrossing_im_eq_zero
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u = 0 ↔
      (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im = 0 := by
  have hQ := fzzKreinQAt_pos hbeta
  have h := fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral beta u
  constructor
  · intro hzero
    have hre := congrArg Complex.re hzero
    simp only [zero_re] at hre
    rw [hre] at h
    linarith
  · intro hcross
    apply Complex.ext
    · simp only [zero_re]
      rw [hcross] at h
      nlinarith
    · rw [fzzCigarParityHermitianQuadraticObservable_im_eq_zero]
      exact zero_im

/-- **Complete all-state blindness classification.**  At positive scale, a Hermitian reporter
cannot distinguish a state from its coordinatewise conjugate exactly in the two expected cases:
the reporter has no chiral coefficient, or the state lies on the literal FZZ grade zero wall. -/
theorem fzzCigarParityHermitianQuadraticObservable_antiunitaryBlind_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d u =
        fzzCigarParityHermitianQuadraticObservable a b c d
          (star u.1, star u.2) ↔
      c = 0 ∨ (fzzCigarParityDilatedTwoScaleGradeCrossing beta u).im = 0 := by
  rw [← sub_eq_zero,
    fzzCigarParityHermitianQuadraticObservable_antiunitaryOddPart,
    mul_eq_zero,
    fzzCigarParityHermitianUnitChiral_eq_zero_iff_gradeCrossing_im_eq_zero hbeta]
  simp

end

end RHTower
