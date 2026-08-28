import GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilization

/-!
# FZZ parity diagonal Riesz stability phase diagram

The literal Fermi-delay source defines an indefinite two-scale Krein form, its canonical
Krein-self-adjoint generator, and the Riesz interaction representing second-scale diagonal energy.
Earlier work exhibited one negative coupling with real spectrum but did not classify the full real
coupling line.

This module proves the exact phase diagram at every positive physical scale. The characteristic
discriminant is a positive square times a completed-square window coordinate. Every eigenvalue is
real exactly when that discriminant is nonnegative. Inside the complementary bounded open window,
an explicit positive-imaginary eigenvalue and nonzero neutral eigenvector witness instability.
Outside it, two disjoint unbounded coupling rays are spectrally real.

Consequently local diagonal Riesz stability is highly nonunique and cannot orient FZZ parity-Mellin
divisor modes. Together with the all-coupling chiral instability theorem, this retires both pure
single-reporter interaction axes as standalone local selectors; viable FZZ-P dynamics must mix the
directions genuinely or use nonlinear, nonlocal, or singular data.
-/

open Complex

namespace RHTower

noncomputable section

/-- Center of the dimensionless diagonal-coupling instability window. -/
def fzzCigarParityDilatedDiagonalStabilityCenter (beta : ℝ) : ℝ :=
  2 * fzzCigarParityDilatedTwoScaleKreinDiscriminant beta /
    fzzKreinPAt beta ^ 2

/-- Radius of the dimensionless diagonal-coupling instability window. -/
def fzzCigarParityDilatedDiagonalStabilityRadius (beta : ℝ) : ℝ :=
  2 * Real.sqrt
      (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta *
        (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta +
          fzzKreinPAt beta ^ 2)) /
    fzzKreinPAt beta ^ 2

theorem fzzCigarParityDilatedDiagonalStabilityRadius_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityDilatedDiagonalStabilityRadius beta := by
  rw [fzzCigarParityDilatedDiagonalStabilityRadius]
  have hD := fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta
  have hP := fzzKreinPAt_pos hbeta
  positivity

/-- Completed-square normal form of the full diagonal-coupling discriminant. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq_squareWindow
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma =
      fzzKreinPAt beta ^ 2 *
        ((gamma / fzzCigarParityDilatedTwoScaleKreinGap beta -
            fzzCigarParityDilatedDiagonalStabilityCenter beta) ^ 2 -
          fzzCigarParityDilatedDiagonalStabilityRadius beta ^ 2) := by
  have hP := fzzKreinPAt_pos hbeta
  have hE := fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta
  have hD := fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta
  have hsqrt :
      Real.sqrt
          (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta *
            (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta +
              fzzKreinPAt beta ^ 2)) ^ 2 =
        fzzCigarParityDilatedTwoScaleKreinDiscriminant beta *
          (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta +
            fzzKreinPAt beta ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq,
    fzzCigarParityDilatedDiagonalStabilityCenter,
    fzzCigarParityDilatedDiagonalStabilityRadius]
  field_simp [hP.ne', hE.ne']
  nlinarith

/-- Negative discriminant is exactly the bounded open source-normalized coupling window. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_neg_iff
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0 ↔
      |gamma / fzzCigarParityDilatedTwoScaleKreinGap beta -
          fzzCigarParityDilatedDiagonalStabilityCenter beta| <
        fzzCigarParityDilatedDiagonalStabilityRadius beta := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq_squareWindow
    hbeta]
  have hP2 : 0 < fzzKreinPAt beta ^ 2 := sq_pos_of_pos (fzzKreinPAt_pos hbeta)
  have hr := fzzCigarParityDilatedDiagonalStabilityRadius_pos hbeta
  let x := gamma / fzzCigarParityDilatedTwoScaleKreinGap beta -
    fzzCigarParityDilatedDiagonalStabilityCenter beta
  let r := fzzCigarParityDilatedDiagonalStabilityRadius beta
  have hr' : 0 < r := by simpa [r] using hr
  constructor
  · intro h
    have hs : x ^ 2 < r ^ 2 := by
      change fzzKreinPAt beta ^ 2 * (x ^ 2 - r ^ 2) < 0 at h
      nlinarith
    change |x| < r
    simpa [abs_of_pos hr'] using (sq_lt_sq.mp hs)
  · intro h
    have hs : x ^ 2 < r ^ 2 := by
      change |x| < r at h
      exact sq_lt_sq.mpr (by simpa [abs_of_pos hr'] using h)
    change fzzKreinPAt beta ^ 2 * (x ^ 2 - r ^ 2) < 0
    nlinarith

/-- Nonnegative discriminant is the complement of the open instability window. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_nonneg_iff
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    0 ≤ fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma ↔
      fzzCigarParityDilatedDiagonalStabilityRadius beta ≤
        |gamma / fzzCigarParityDilatedTwoScaleKreinGap beta -
          fzzCigarParityDilatedDiagonalStabilityCenter beta| := by
  rw [← not_lt, ← not_lt,
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_neg_iff
      hbeta gamma]

private theorem complexQuadraticRoot_eq_star_of_discriminant_nonneg
    {T D : ℝ} {lambda : ℂ}
    (hdisc : 0 ≤ T ^ 2 - 4 * D)
    (hroot : lambda ^ 2 - (T : ℂ) * lambda + (D : ℂ) = 0) :
    lambda = star lambda := by
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  norm_num [Complex.mul_re, Complex.mul_im, pow_two] at hre him
  by_cases hli : lambda.im = 0
  · apply Complex.ext
    · simp
    · simp [hli]
  · have hreal : lambda.re = T / 2 := by
      have hfactor : (2 * lambda.re - T) * lambda.im = 0 := by
        nlinarith
      have := (mul_eq_zero.mp hfactor).resolve_right hli
      linarith
    have hdiscEq : T ^ 2 - 4 * D = -4 * lambda.im ^ 2 := by
      nlinarith
    nlinarith [sq_pos_of_ne_zero hli]

private theorem twoByTwoRealEigenvalue_quadratic
    {a b c d : ℝ} {lambda : ℂ} {v : ℂ × ℂ}
    (hv : v ≠ 0)
    (heigen :
      ((a : ℂ) * v.1 + (b : ℂ) * v.2,
          (c : ℂ) * v.1 + (d : ℂ) * v.2) = lambda • v) :
    lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda + ((a * d - b * c : ℝ) : ℂ) = 0 := by
  rcases v with ⟨x, y⟩
  have hfirst := congrArg Prod.fst heigen
  have hsecond := congrArg Prod.snd heigen
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfirst hsecond
  have hfirstZero : (a : ℂ) * x + (b : ℂ) * y - lambda * x = 0 :=
    sub_eq_zero.mpr hfirst
  have hsecondZero : (c : ℂ) * x + (d : ℂ) * y - lambda * y = 0 :=
    sub_eq_zero.mpr hsecond
  have hxprod :
      (lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda +
          ((a * d - b * c : ℝ) : ℂ)) * x = 0 := by
    calc
      (lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda +
            ((a * d - b * c : ℝ) : ℂ)) * x =
          -((lambda - (d : ℂ)) *
              ((a : ℂ) * x + (b : ℂ) * y - lambda * x) +
            (b : ℂ) * ((c : ℂ) * x + (d : ℂ) * y - lambda * y)) := by
              push_cast
              ring
      _ = 0 := by rw [hfirstZero, hsecondZero]; ring
  have hyprod :
      (lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda +
          ((a * d - b * c : ℝ) : ℂ)) * y = 0 := by
    calc
      (lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda +
            ((a * d - b * c : ℝ) : ℂ)) * y =
          -((c : ℂ) *
              ((a : ℂ) * x + (b : ℂ) * y - lambda * x) +
            (lambda - (a : ℂ)) *
              ((c : ℂ) * x + (d : ℂ) * y - lambda * y)) := by
              push_cast
              ring
      _ = 0 := by rw [hfirstZero, hsecondZero]; ring
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      simp [hx, hy]
    exact (mul_eq_zero.mp hyprod).resolve_right hy
  · exact (mul_eq_zero.mp hxprod).resolve_right hx

private theorem twoByTwoReal_eigenpair_of_quadratic_root
    {a b c d : ℝ} {lambda : ℂ}
    (hroot :
      lambda ^ 2 - ((a + d : ℝ) : ℂ) * lambda +
        ((a * d - b * c : ℝ) : ℂ) = 0) :
    ((a : ℂ) * (b : ℂ) + (b : ℂ) * (lambda - (a : ℂ)),
        (c : ℂ) * (b : ℂ) + (d : ℂ) * (lambda - (a : ℂ))) =
      lambda • ((b : ℂ), lambda - (a : ℂ)) := by
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [Prod.smul_snd, smul_eq_mul]
    push_cast at hroot ⊢
    linear_combination -hroot

/-- Every eigenvalue of the literal diagonal perturbation satisfies its displayed real quadratic. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbed_eigenvalue_characteristic
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ)
    {lambda : ℂ} {v : ℂ × ℂ} (hv : v ≠ 0)
    (heigen :
      fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma v =
        lambda • v) :
    lambda ^ 2 -
        (fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma : ℂ) * lambda +
        (fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma : ℂ) = 0 := by
  let a : ℝ := fzzKreinPAt beta
  let b : ℝ := fzzKreinQAt beta *
    (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta)
  let c : ℝ := -(fzzKreinPAt beta * fzzKreinQAt beta / fzzKreinRAt beta)
  let d : ℝ := -fzzKreinPAt beta *
    (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta)
  have heigen' :
      ((a : ℂ) * v.1 + (b : ℂ) * v.2,
          (c : ℂ) * v.1 + (d : ℂ) * v.2) = lambda • v := by
    rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_matrix] at heigen
    simpa [a, b, c, d, sub_eq_add_neg] using heigen
  have hroot := twoByTwoRealEigenvalue_quadratic hv heigen'
  have htrace : a + d =
      fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma := by
    simp [a, d, fzzCigarParityDilatedSecondDiagonalPerturbedTrace]
    ring
  have hdet : a * d - b * c =
      fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma := by
    have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
    have hR := (fzzKreinRAt_pos hbeta).ne'
    simp [a, b, c, d,
      fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant,
      fzzCigarParityDilatedTwoScaleKreinDiscriminant]
    field_simp [hE, hR]
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    ring
  rwa [htrace, hdet] at hroot

/-- Nonnegative characteristic discriminant forces every eigenvalue to be real. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_of_discriminant_nonneg
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ)
    (hdisc : 0 ≤
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta gamma := by
  intro lambda v hv heigen
  apply complexQuadraticRoot_eq_star_of_discriminant_nonneg
  · simpa [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant]
      using hdisc
  · exact fzzCigarParityDilatedSecondDiagonalPerturbed_eigenvalue_characteristic
      hbeta gamma hv heigen

/-- Upper-right real coefficient of the diagonal Riesz perturbation. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedUpper
    (beta gamma : ℝ) : ℝ :=
  fzzKreinQAt beta *
    (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta)

/-- Positive-imaginary eigenvalue inside the exact diagonal instability window. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
    (beta gamma : ℝ) : ℂ :=
  (fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma / 2 : ℝ) +
    Complex.I *
      (Real.sqrt
        (-fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant
          beta gamma) / 2 : ℝ)

/-- Source-coordinate eigenvector inside the exact diagonal instability window. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector
    (beta gamma : ℝ) : ℂ × ℂ :=
  ((fzzCigarParityDilatedSecondDiagonalPerturbedUpper beta gamma : ℝ),
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma -
      (fzzKreinPAt beta : ℝ))

theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_root
    {beta gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma ^ 2 -
        (fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma : ℂ) *
          fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma +
        (fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma : ℂ) = 0 := by
  let T := fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma
  let D := fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma
  let disc :=
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma
  let y := Real.sqrt (-disc) / 2
  have hdiscEq : disc = T ^ 2 - 4 * D := by
    rfl
  have hnonneg : 0 ≤ -disc := by
    dsimp [disc]
    linarith
  have hy2 : y ^ 2 = -disc / 4 := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hnonneg]
    norm_num
  have heigenvalue :
      fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma =
        (T / 2 : ℝ) + Complex.I * (y : ℝ) := by
    rfl
  rw [heigenvalue]
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [hy2, hdiscEq]
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]
    ring

theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_im_pos
    {beta gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    0 <
      (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma).im := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue]
  simp only [add_im, ofReal_im, zero_add, mul_im, I_re, mul_zero, I_im,
    ofReal_re]
  have hsqrt := Real.sqrt_pos.2 (neg_pos.mpr hdisc)
  nlinarith

theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_not_real
    {beta gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma ≠
      star (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma) := by
  intro h
  have him := congrArg Complex.im h
  have hstar :
      (star
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
          beta gamma)).im =
        -(fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
          beta gamma).im := by
    change ((starRingEnd ℂ)
      (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
        beta gamma)).im = _
    exact Complex.conj_im _
  rw [hstar] at him
  linarith [
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_im_pos hdisc]

theorem fzzCigarParityDilatedSecondDiagonalPerturbedUpper_ne_zero_of_discriminant_neg
    {beta : ℝ} (hbeta : 0 < beta) {gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedSecondDiagonalPerturbedUpper beta gamma ≠ 0 := by
  intro hupper
  have hQ := (fzzKreinQAt_pos hbeta).ne'
  have halpha :
      1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta = 0 :=
    (mul_eq_zero.mp hupper).resolve_left hQ
  have hdet :
      fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma = 0 := by
    simp [fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant, halpha]
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant,
    hdet] at hdisc
  nlinarith [sq_nonneg
    (fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma)]

theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp only [fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector,
    Prod.fst_zero] at hfirst
  exact (Complex.ofReal_ne_zero.mpr
    (fzzCigarParityDilatedSecondDiagonalPerturbedUpper_ne_zero_of_discriminant_neg
      hbeta hdisc)) hfirst

/-- Every coupling in the open instability window has an explicit nonreal eigenpair. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenpair
    {beta : ℝ} (hbeta : 0 < beta) {gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) =
      fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma •
        fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma := by
  let a : ℝ := fzzKreinPAt beta
  let b : ℝ := fzzCigarParityDilatedSecondDiagonalPerturbedUpper beta gamma
  let c : ℝ := -(fzzKreinPAt beta * fzzKreinQAt beta / fzzKreinRAt beta)
  let d : ℝ := -fzzKreinPAt beta *
    (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta)
  have htrace : a + d =
      fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma := by
    simp [a, d, fzzCigarParityDilatedSecondDiagonalPerturbedTrace]
    ring
  have hdet : a * d - b * c =
      fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma := by
    have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
    have hR := (fzzKreinRAt_pos hbeta).ne'
    simp [a, b, c, d, fzzCigarParityDilatedSecondDiagonalPerturbedUpper,
      fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant,
      fzzCigarParityDilatedTwoScaleKreinDiscriminant]
    field_simp [hE, hR]
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    ring
  have hroot :=
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_root hdisc
  have hroot' :
      fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma ^ 2 -
          ((a + d : ℝ) : ℂ) *
            fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma +
          ((a * d - b * c : ℝ) : ℂ) = 0 := by
    simpa [htrace, hdet] using hroot
  have hp := twoByTwoReal_eigenpair_of_quadratic_root hroot'
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_matrix]
  simpa [fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector,
    fzzCigarParityDilatedSecondDiagonalPerturbedUpper, a, b, c, d,
    sub_eq_add_neg] using hp

/-- The explicit nonreal instability eigenvector is neutral for the literal source Krein form. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector_null
    {beta : ℝ} (hbeta : 0 < beta) {gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) = 0 := by
  have hself :=
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_formallySelfAdjoint
      hbeta gamma
      (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
      (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenpair hbeta hdisc]
    at hself
  rw [fzzCigarParityDilatedTwoScaleKreinPairing_smul_left,
    fzzCigarParityDilatedTwoScaleKreinPairing_smul_right] at hself
  have hfactor :
      (star
          (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
            beta gamma) -
          fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma) *
        fzzCigarParityDilatedTwoScaleKreinPairing beta
          (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
          (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) = 0 := by
    calc
      (star
            (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue
              beta gamma) -
            fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma) *
          fzzCigarParityDilatedTwoScaleKreinPairing beta
            (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
            (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) =
        star
            (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma) *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
              (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) -
          fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
              (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma) := by
                ring
      _ = 0 := sub_eq_zero.mpr hself
  exact (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr
      (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_not_real
        hdisc).symm)

/-- Negative discriminant is a genuine spectral-instability witness. -/
theorem not_fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_of_discriminant_neg
    {beta : ℝ} (hbeta : 0 < beta) {gamma : ℝ}
    (hdisc :
      fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0) :
    ¬ FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta gamma := by
  intro hreal
  exact
    fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue_not_real hdisc
      (hreal
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvalue beta gamma)
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector beta gamma)
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector_ne_zero
          hbeta hdisc)
        (fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenpair hbeta hdisc))

/-- Exact spectral classification of every real diagonal Riesz coupling. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_discriminant_nonneg
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta gamma ↔
      0 ≤ fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma := by
  constructor
  · intro hreal
    by_contra hnot
    have hneg :
        fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma < 0 :=
      lt_of_not_ge hnot
    exact (not_fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_of_discriminant_neg
      hbeta hneg) hreal
  · exact fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_of_discriminant_nonneg
      hbeta gamma

/-- **Full phase diagram.** Spectral reality is exactly the complement of one explicit bounded
open interval in the source-normalized diagonal coupling. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_outside_window
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta gamma ↔
      fzzCigarParityDilatedDiagonalStabilityRadius beta ≤
        |gamma / fzzCigarParityDilatedTwoScaleKreinGap beta -
          fzzCigarParityDilatedDiagonalStabilityCenter beta| := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_discriminant_nonneg
      hbeta gamma,
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_nonneg_iff
      hbeta gamma]

/-- Lower dimensional coupling boundary of the exact stability phase diagram. -/
def fzzCigarParityDilatedDiagonalStabilityLowerCoupling (beta : ℝ) : ℝ :=
  fzzCigarParityDilatedTwoScaleKreinGap beta *
    (fzzCigarParityDilatedDiagonalStabilityCenter beta -
      fzzCigarParityDilatedDiagonalStabilityRadius beta)

/-- Upper dimensional coupling boundary of the exact stability phase diagram. -/
def fzzCigarParityDilatedDiagonalStabilityUpperCoupling (beta : ℝ) : ℝ :=
  fzzCigarParityDilatedTwoScaleKreinGap beta *
    (fzzCigarParityDilatedDiagonalStabilityCenter beta +
      fzzCigarParityDilatedDiagonalStabilityRadius beta)

theorem fzzCigarParityDilatedDiagonalStabilityLowerCoupling_lt_upper
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedDiagonalStabilityLowerCoupling beta <
      fzzCigarParityDilatedDiagonalStabilityUpperCoupling beta := by
  rw [fzzCigarParityDilatedDiagonalStabilityLowerCoupling,
    fzzCigarParityDilatedDiagonalStabilityUpperCoupling]
  have hE := fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta
  have hr := fzzCigarParityDilatedDiagonalStabilityRadius_pos hbeta
  nlinarith

/-- Every coupling on the complete upper ray is spectrally real. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_upperRay
    {beta u : ℝ} (hbeta : 0 < beta) (hu : 0 ≤ u) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
      (fzzCigarParityDilatedDiagonalStabilityUpperCoupling beta +
        fzzCigarParityDilatedTwoScaleKreinGap beta * u) := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_outside_window
    hbeta]
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hr := fzzCigarParityDilatedDiagonalStabilityRadius_pos hbeta
  rw [fzzCigarParityDilatedDiagonalStabilityUpperCoupling]
  have hquot :
      (fzzCigarParityDilatedTwoScaleKreinGap beta *
            (fzzCigarParityDilatedDiagonalStabilityCenter beta +
              fzzCigarParityDilatedDiagonalStabilityRadius beta) +
          fzzCigarParityDilatedTwoScaleKreinGap beta * u) /
          fzzCigarParityDilatedTwoScaleKreinGap beta =
        fzzCigarParityDilatedDiagonalStabilityCenter beta +
          fzzCigarParityDilatedDiagonalStabilityRadius beta + u := by
    field_simp [hE]
  rw [hquot]
  rw [show
      fzzCigarParityDilatedDiagonalStabilityCenter beta +
            fzzCigarParityDilatedDiagonalStabilityRadius beta + u -
          fzzCigarParityDilatedDiagonalStabilityCenter beta =
        fzzCigarParityDilatedDiagonalStabilityRadius beta + u by ring,
    abs_of_nonneg (by linarith)]
  linarith

/-- Every coupling on the complete lower ray is spectrally real. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_lowerRay
    {beta u : ℝ} (hbeta : 0 < beta) (hu : 0 ≤ u) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
      (fzzCigarParityDilatedDiagonalStabilityLowerCoupling beta -
        fzzCigarParityDilatedTwoScaleKreinGap beta * u) := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_outside_window
    hbeta]
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hr := fzzCigarParityDilatedDiagonalStabilityRadius_pos hbeta
  rw [fzzCigarParityDilatedDiagonalStabilityLowerCoupling]
  have hquot :
      (fzzCigarParityDilatedTwoScaleKreinGap beta *
            (fzzCigarParityDilatedDiagonalStabilityCenter beta -
              fzzCigarParityDilatedDiagonalStabilityRadius beta) -
          fzzCigarParityDilatedTwoScaleKreinGap beta * u) /
          fzzCigarParityDilatedTwoScaleKreinGap beta =
        fzzCigarParityDilatedDiagonalStabilityCenter beta -
          fzzCigarParityDilatedDiagonalStabilityRadius beta - u := by
    field_simp [hE]
  rw [hquot]
  rw [show
      fzzCigarParityDilatedDiagonalStabilityCenter beta -
            fzzCigarParityDilatedDiagonalStabilityRadius beta - u -
          fzzCigarParityDilatedDiagonalStabilityCenter beta =
        -(fzzCigarParityDilatedDiagonalStabilityRadius beta + u) by ring,
    abs_neg,
    abs_of_nonneg (by linarith)]
  linarith

/-- **Diagonal-stability nonuniqueness.** Every positive source scale has two disjoint unbounded
spectrally-real coupling rays separated by a bounded nonreal-neutral window. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbed_twoStableRays
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedDiagonalStabilityLowerCoupling beta <
        fzzCigarParityDilatedDiagonalStabilityUpperCoupling beta ∧
      (∀ u : ℝ, 0 ≤ u →
        FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
          (fzzCigarParityDilatedDiagonalStabilityLowerCoupling beta -
            fzzCigarParityDilatedTwoScaleKreinGap beta * u)) ∧
      (∀ u : ℝ, 0 ≤ u →
        FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
          (fzzCigarParityDilatedDiagonalStabilityUpperCoupling beta +
            fzzCigarParityDilatedTwoScaleKreinGap beta * u)) := by
  exact ⟨fzzCigarParityDilatedDiagonalStabilityLowerCoupling_lt_upper hbeta,
    fun _ => fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_lowerRay hbeta,
    fun _ => fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_upperRay hbeta⟩

end

end RHTower
