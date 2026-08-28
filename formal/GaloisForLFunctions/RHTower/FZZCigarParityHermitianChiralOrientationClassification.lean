import GaloisForLFunctions.RHTower.FZZCigarParityAllScaleKreinCrossing

/-!
# Hermitian chiral orientation classification for the FZZ parity eigenpair

The literal dilated FZZ parity source has a conjugate neutral Krein eigenpair at every positive
scale.  This module classifies the complete four-real-parameter family of Hermitian quadratic
reporters on that pair.  Write the reporter block as

`[[a, b + i c], [b - i c, d]]`.

Complex conjugation fixes its diagonal and real-symmetric parts and reverses only `c`.  On the
canonical FZZ pair the exact reporter gap is

`-4 Q(beta) c sqrt(Delta(beta))`.

Consequently, at every positive scale, the reporter distinguishes the two orientations exactly
when `c != 0`; its ordering is exactly opposite the sign of `c`.  Every real-symmetric reporter is
blind, while the unit imaginary off-diagonal reporter is strictly oriented.

This closes a source-side classification, not RH.  A surviving FZZ/GFZZ proof must now construct a
physical interaction whose compression has nonzero imaginary off-diagonal coefficient and then
land the Xi divisor modes in the corresponding source eigenlines.  FZZ duality and cigar spectral
asymmetry are treated in Hikida--Schomerus (arXiv:0805.3931) and Ashok--Troost
(arXiv:1101.1059); general Krein collision theory is treated by Kapitula--Kevrekidis--Yan
(arXiv:1212.2951).  A targeted literature search located none of the exact source-specific
classification proved here.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hermitian quadratic reporter with block `[[a, b + i c], [b - i c, d]]`.  These four real
parameters are the diagonal, real-symmetric, and imaginary off-diagonal coordinates of a complex
Hermitian `2 x 2` block. -/
def fzzCigarParityHermitianQuadraticObservable
    (a b c d : ℝ) (u : ℂ × ℂ) : ℂ :=
  star u.1 * ((a : ℂ) * u.1 + ((b : ℂ) + Complex.I * (c : ℂ)) * u.2) +
    star u.2 * (((b : ℂ) - Complex.I * (c : ℂ)) * u.1 + (d : ℂ) * u.2)

/-- A Hermitian reporter has a real scalar value on every vector. -/
theorem fzzCigarParityHermitianQuadraticObservable_star_self
    (a b c d : ℝ) (u : ℂ × ℂ) :
    star (fzzCigarParityHermitianQuadraticObservable a b c d u) =
      fzzCigarParityHermitianQuadraticObservable a b c d u := by
  simp [fzzCigarParityHermitianQuadraticObservable, star_add, star_mul,
    Complex.conj_ofReal]
  ring

/-- Real-valuedness of the Hermitian reporter, in imaginary-part form. -/
theorem fzzCigarParityHermitianQuadraticObservable_im_eq_zero
    (a b c d : ℝ) (u : ℂ × ℂ) :
    (fzzCigarParityHermitianQuadraticObservable a b c d u).im = 0 := by
  exact Complex.conj_eq_iff_im.mp
    (fzzCigarParityHermitianQuadraticObservable_star_self a b c d u)

/-- Complex conjugation reverses precisely the imaginary off-diagonal coefficient. -/
theorem fzzCigarParityHermitianQuadraticObservable_star
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (star u.1, star u.2) =
      star (fzzCigarParityHermitianQuadraticObservable a b (-c) d u) := by
  simp [fzzCigarParityHermitianQuadraticObservable, star_add, star_mul,
    Complex.conj_ofReal]
  ring

/-- Since Hermitian reporter values are real, conjugating the vector acts only by `c -> -c`. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugate_eq_neg_chiral
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (star u.1, star u.2) =
      fzzCigarParityHermitianQuadraticObservable a b (-c) d u := by
  rw [fzzCigarParityHermitianQuadraticObservable_star,
    fzzCigarParityHermitianQuadraticObservable_star_self]

/-- The negative-imaginary FZZ source eigenvector is coordinatewise conjugate to the
positive-imaginary one at every scale. -/
theorem fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_eq_star
    (beta : ℝ) :
    fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta =
      (star (fzzCigarParityDilatedTwoScaleKreinEigenvector beta).1,
        star (fzzCigarParityDilatedTwoScaleKreinEigenvector beta).2) := by
  simp [fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector,
    fzzCigarParityDilatedTwoScaleKreinEigenvector, Complex.conj_ofReal]

/-- **Exact FZZ Hermitian orientation law.**  Diagonal and real-symmetric coordinates cancel;
the whole conjugate-pair gap is the imaginary off-diagonal coefficient times the source's positive
Krein crossing amplitude. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub
    (beta a b c d : ℝ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) -
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta) =
      ((-4 * fzzKreinQAt beta * c *
        Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) : ℝ) : ℂ) := by
  rw [fzzCigarParityHermitianQuadraticObservable,
    fzzCigarParityHermitianQuadraticObservable,
    fzzCigarParityDilatedTwoScaleKreinEigenvector,
    fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector,
    fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp [Complex.conj_ofReal, star_sub, star_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Sharp blindness classification.** At every positive FZZ scale, a Hermitian reporter is blind
to the conjugate source pair exactly when its imaginary off-diagonal coefficient vanishes. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugatePair_eq_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) =
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta) ↔
      c = 0 := by
  rw [← sub_eq_zero,
    fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub]
  have hQ := (fzzKreinQAt_pos hbeta).ne'
  have hD := (Real.sqrt_pos.2
    (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta)).ne'
  push_cast
  simp [hQ, hD]

/-- **Real-symmetric no-go.** Every real-symmetric reporter is blind at every real scale, without a
positivity assumption. -/
theorem fzzCigarParityRealSymmetricQuadraticObservable_conjugatePair_eq
    (beta a b d : ℝ) :
    fzzCigarParityHermitianQuadraticObservable a b 0 d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) =
      fzzCigarParityHermitianQuadraticObservable a b 0 d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta) := by
  rw [← sub_eq_zero,
    fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub]
  norm_num

/-- Equivalent nonvanishing form of the sharp classification. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugatePair_ne_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) ≠
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta) ↔
      c ≠ 0 := by
  exact not_congr
    (fzzCigarParityHermitianQuadraticObservable_conjugatePair_eq_iff hbeta a b c d)

/-- Positive chiral coefficient orders the positive-imaginary FZZ eigenline strictly below its
conjugate. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub_re_neg_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    (fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) -
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)).re < 0 ↔
      0 < c := by
  rw [fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub]
  simp only [ofReal_re]
  have hfactor : 0 < 4 * fzzKreinQAt beta *
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) := by
    have hQ := fzzKreinQAt_pos hbeta
    have hD := Real.sqrt_pos.2
      (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta)
    positivity
  rw [show -4 * fzzKreinQAt beta * c *
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) =
        -(4 * fzzKreinQAt beta *
          Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta)) * c by ring]
  constructor
  · intro h
    by_contra hc
    have hc0 : c ≤ 0 := le_of_not_gt hc
    exact (not_lt_of_ge
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hfactor.le) hc0)) h
  · intro hc
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfactor) hc

/-- Negative chiral coefficient reverses the strict ordering. -/
theorem fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub_re_pos_iff
    {beta : ℝ} (hbeta : 0 < beta) (a b c d : ℝ) :
    0 < (fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) -
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)).re ↔
      c < 0 := by
  rw [fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub]
  simp only [ofReal_re]
  have hfactor : 0 < 4 * fzzKreinQAt beta *
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) := by
    have hQ := fzzKreinQAt_pos hbeta
    have hD := Real.sqrt_pos.2
      (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta)
    positivity
  rw [show -4 * fzzKreinQAt beta * c *
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) =
        -(4 * fzzKreinQAt beta *
          Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta)) * c by ring]
  constructor
  · intro h
    by_contra hc
    have hc0 : 0 ≤ c := le_of_not_gt hc
    exact (not_lt_of_ge
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfactor.le) hc0)) h
  · intro hc
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hfactor) hc

/-- The unit imaginary off-diagonal reporter supplies a strict orientation at every positive
scale.  This is the strongest positive survivor of the real-symmetric no-go. -/
theorem fzzCigarParityUnitChiralQuadraticObservable_conjugatePair_sub_re_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    (fzzCigarParityHermitianQuadraticObservable 0 0 1 0
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) -
      fzzCigarParityHermitianQuadraticObservable 0 0 1 0
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)).re < 0 := by
  exact
    (fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub_re_neg_iff
      hbeta 0 0 1 0).2 zero_lt_one

end

end RHTower
