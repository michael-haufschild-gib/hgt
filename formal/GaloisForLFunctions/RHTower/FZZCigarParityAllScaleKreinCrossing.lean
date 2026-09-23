import GaloisForLFunctions.RHTower.FZZCigarParityKreinGradeCrossingOrientation

/-!
# All-scale Krein crossing of the FZZ parity source

The parity-subtracted FZZ delay is the literal Fermi source `P(t)=1/(exp(t)+1)`.  Previous modules
found a negative multiplicative Hankel minor and an oriented neutral Krein eigenpair only at the
single scale `beta=1`.  Here the physical dilation is left free.

For every `beta>0`, the source values `P(beta), P(2 beta), P(4 beta)` have strictly negative
Hankel determinant.  The resulting canonical source-Krein-self-adjoint operator therefore has a
nonreal neutral conjugate eigenpair at every positive scale.  Its natural grade crossing is
strictly positive on the positive-imaginary eigenline and strictly negative on its conjugate.

This constructs a coherent, coefficient-faithful oriented carrier over the entire positive scale
ray before any Xi divisor specialization.  It does not prove RH: the remaining gate is to derive a
source-native landing of each parity-Mellin divisor mode into one of these physical eigenlines.
-/

open Complex

namespace RHTower

noncomputable section

/-- Two-scale FZZ parity Hankel determinant at physical dilation `beta`. -/
def fzzCigarParityDilatedTwoScaleHankelMinor (beta : ℝ) : ℝ :=
  fzzCigarParityDelay beta * fzzCigarParityDelay (4 * beta) -
    fzzCigarParityDelay (2 * beta) ^ (2 : ℕ)

/-- **All-scale strict indefiniteness.** Every positive dilation has negative Hankel determinant. -/
theorem fzzCigarParityDilatedTwoScaleHankelMinor_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleHankelMinor beta < 0 := by
  rw [fzzCigarParityDilatedTwoScaleHankelMinor,
    fzzCigarParityDelay_eq_fermi hbeta,
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta),
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta)]
  let a : ℝ := Real.exp beta
  have ha : 1 < a := by
    change 1 < Real.exp beta
    exact Real.one_lt_exp_iff.mpr hbeta
  have he2 : Real.exp (2 * beta) = a ^ (2 : ℕ) := by
    rw [show 2 * beta = beta + beta by ring, Real.exp_add]
    change a * a = a ^ (2 : ℕ)
    ring
  have he4 : Real.exp (4 * beta) = a ^ (4 : ℕ) := by
    rw [show 4 * beta = 2 * beta + 2 * beta by ring, Real.exp_add, he2]
    ring
  rw [show Real.exp beta = a by rfl, he2, he4]
  have hB : 0 < (a ^ (2 : ℕ) + 1) ^ (2 : ℕ) := sq_pos_of_pos (by positivity)
  have hBA : (a ^ (2 : ℕ) + 1) ^ (2 : ℕ) < (a + 1) * (a ^ (4 : ℕ) + 1) := by
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have ha2 : 1 < a ^ (2 : ℕ) := one_lt_pow₀ ha (by norm_num)
    have ha4 : a ^ (2 : ℕ) < a ^ (4 : ℕ) := by nlinarith [ha2]
    nlinarith [ha0]
  have hinv : ((a + 1) * (a ^ (4 : ℕ) + 1))⁻¹ < ((a ^ (2 : ℕ) + 1) ^ (2 : ℕ))⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hB hBA
  exact sub_neg.mpr (by simpa [mul_inv, inv_pow, mul_comm] using hinv)

/-- First diagonal coefficient of the dilated source block. -/
abbrev fzzKreinPAt (beta : ℝ) : ℝ := fzzCigarParityDelay beta
/-- Off-diagonal coefficient of the dilated source block. -/
abbrev fzzKreinQAt (beta : ℝ) : ℝ := fzzCigarParityDelay (2 * beta)
/-- Second diagonal coefficient of the dilated source block. -/
abbrev fzzKreinRAt (beta : ℝ) : ℝ := fzzCigarParityDelay (4 * beta)

/-- Source-exact Hermitian pairing at physical dilation `beta`. -/
def fzzCigarParityDilatedTwoScaleKreinPairing
    (beta : ℝ) (u v : ℂ × ℂ) : ℂ :=
  (fzzKreinPAt beta : ℂ) * star u.1 * v.1 +
    (fzzKreinQAt beta : ℂ) * star u.1 * v.2 +
    (fzzKreinQAt beta : ℂ) * star u.2 * v.1 +
    (fzzKreinRAt beta : ℂ) * star u.2 * v.2

/-- Canonical traceless operator adapted to the dilated source pairing. -/
def fzzCigarParityDilatedTwoScaleKreinOperator
    (beta : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  ((fzzKreinPAt beta : ℂ) * u.1 + (fzzKreinQAt beta : ℂ) * u.2,
    (-((fzzKreinPAt beta * fzzKreinQAt beta / fzzKreinRAt beta : ℝ) : ℂ)) * u.1 -
      (fzzKreinPAt beta : ℂ) * u.2)

theorem fzzKreinPAt_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzKreinPAt beta := by
  change 0 < fzzCigarParityDelay beta
  rw [fzzCigarParityDelay_eq_fermi hbeta]
  positivity

theorem fzzKreinQAt_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzKreinQAt beta := by
  change 0 < fzzCigarParityDelay (2 * beta)
  rw [fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta)]
  positivity

theorem fzzKreinRAt_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzKreinRAt beta := by
  change 0 < fzzCigarParityDelay (4 * beta)
  rw [fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta)]
  positivity

/-- Canonical operator is formally self-adjoint at every positive dilation. -/
theorem fzzCigarParityDilatedTwoScaleKreinOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ u v : ℂ × ℂ,
      fzzCigarParityDilatedTwoScaleKreinPairing beta
          (fzzCigarParityDilatedTwoScaleKreinOperator beta u) v =
        fzzCigarParityDilatedTwoScaleKreinPairing beta u
          (fzzCigarParityDilatedTwoScaleKreinOperator beta v) := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedTwoScaleKreinOperator]
  have hR : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  field_simp
  ring

/-- Positive discriminant complementary to the dilated negative Hankel determinant. -/
def fzzCigarParityDilatedTwoScaleKreinDiscriminant (beta : ℝ) : ℝ :=
  fzzKreinPAt beta *
      (fzzKreinQAt beta ^ (2 : ℕ) - fzzKreinPAt beta * fzzKreinRAt beta) /
    fzzKreinRAt beta

theorem fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityDilatedTwoScaleKreinDiscriminant beta := by
  have hminor := fzzCigarParityDilatedTwoScaleHankelMinor_neg hbeta
  change fzzKreinPAt beta * fzzKreinRAt beta - fzzKreinQAt beta ^ (2 : ℕ) < 0 at hminor
  rw [fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  exact div_pos (mul_pos (fzzKreinPAt_pos hbeta) (by linarith))
    (fzzKreinRAt_pos hbeta)

/-- Positive-imaginary member of the scale-dependent Krein pair. -/
def fzzCigarParityDilatedTwoScaleKreinEigenvalue (beta : ℝ) : ℂ :=
  Complex.I *
    (Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) : ℂ)

/-- Explicit source-coordinate eigenvector at dilation `beta`. -/
def fzzCigarParityDilatedTwoScaleKreinEigenvector (beta : ℝ) : ℂ × ℂ :=
  ((fzzKreinQAt beta : ℂ),
    fzzCigarParityDilatedTwoScaleKreinEigenvalue beta - (fzzKreinPAt beta : ℂ))

theorem fzzCigarParityDilatedTwoScaleKreinEigenvalue_sq
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinEigenvalue beta ^ (2 : ℕ) =
      -(fzzCigarParityDilatedTwoScaleKreinDiscriminant beta : ℂ) := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  have hsqrt :
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) ^ (2 : ℕ) =
        fzzCigarParityDilatedTwoScaleKreinDiscriminant beta :=
    Real.sq_sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta).le
  have hcast :
      ((Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) : ℝ) : ℂ) ^ (2 : ℕ) =
        (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta : ℂ) := by
    exact_mod_cast hsqrt
  rw [mul_pow, Complex.I_sq, hcast]
  ring

theorem fzzCigarParityDilatedTwoScaleKreinEigenvector_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinEigenvector beta ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp only [fzzCigarParityDilatedTwoScaleKreinEigenvector, Prod.fst_zero] at hfirst
  exact (Complex.ofReal_ne_zero.mpr (fzzKreinQAt_pos hbeta).ne') hfirst

/-- Explicit nonreal eigenpair throughout the positive scale ray. -/
theorem fzzCigarParityDilatedTwoScaleKreinEigenpair
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinOperator beta
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) =
      fzzCigarParityDilatedTwoScaleKreinEigenvalue beta •
        fzzCigarParityDilatedTwoScaleKreinEigenvector beta := by
  apply Prod.ext
  · simp only [fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParityDilatedTwoScaleKreinEigenvector, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParityDilatedTwoScaleKreinEigenvector, Prod.smul_snd, smul_eq_mul]
    have hR : (fzzKreinRAt beta : ℂ) ≠ 0 := by
      exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
    calc
      -((fzzKreinPAt beta * fzzKreinQAt beta / fzzKreinRAt beta : ℝ) : ℂ) *
            (fzzKreinQAt beta : ℂ) -
          (fzzKreinPAt beta : ℂ) *
            (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
              (fzzKreinPAt beta : ℂ)) =
          -(fzzCigarParityDilatedTwoScaleKreinDiscriminant beta : ℂ) -
            (fzzKreinPAt beta : ℂ) *
              fzzCigarParityDilatedTwoScaleKreinEigenvalue beta := by
              rw [fzzCigarParityDilatedTwoScaleKreinDiscriminant]
              push_cast
              field_simp
              ring
      _ = fzzCigarParityDilatedTwoScaleKreinEigenvalue beta ^ (2 : ℕ) -
            (fzzKreinPAt beta : ℂ) *
              fzzCigarParityDilatedTwoScaleKreinEigenvalue beta := by
              rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue_sq hbeta]
      _ = fzzCigarParityDilatedTwoScaleKreinEigenvalue beta *
            (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
              (fzzKreinPAt beta : ℂ)) := by ring

theorem fzzCigarParityDilatedTwoScaleKreinEigenvalue_im_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta).im := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp only [mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, zero_add]
  simpa using Real.sqrt_pos.2
    (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta)

theorem star_fzzCigarParityDilatedTwoScaleKreinEigenvalue_eq_neg
    (beta : ℝ) :
    star (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta) =
      -fzzCigarParityDilatedTwoScaleKreinEigenvalue beta := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp

theorem fzzCigarParityDilatedTwoScaleKreinEigenvalue_not_real
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinEigenvalue beta ≠
      star (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta) := by
  intro h
  have him := congrArg Complex.im h
  rw [star_fzzCigarParityDilatedTwoScaleKreinEigenvalue_eq_neg beta,
    neg_im] at him
  linarith [fzzCigarParityDilatedTwoScaleKreinEigenvalue_im_pos hbeta]

/-- Every positive-scale eigenvector is neutral for its source pairing. -/
theorem fzzCigarParityDilatedTwoScaleKreinEigenvector_null
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
      (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)
      (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) = 0 := by
  have hself := fzzCigarParityDilatedTwoScaleKreinOperator_formallySelfAdjoint hbeta
    (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)
    (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)
  rw [fzzCigarParityDilatedTwoScaleKreinEigenpair hbeta] at hself
  simp [fzzCigarParityDilatedTwoScaleKreinPairing] at hself
  have hfactor :
      (star (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta) -
          fzzCigarParityDilatedTwoScaleKreinEigenvalue beta) *
        fzzCigarParityDilatedTwoScaleKreinPairing beta
          (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)
          (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) = 0 := by
    rw [fzzCigarParityDilatedTwoScaleKreinPairing]
    linear_combination hself
  exact (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr
      (fzzCigarParityDilatedTwoScaleKreinEigenvalue_not_real hbeta).symm)

/-- Natural grade projection distinguishing the second dilated source scale. -/
def fzzCigarParityDilatedTwoScaleGrade (u : ℂ × ℂ) : ℂ × ℂ :=
  (0, u.2)

/-- Null-line crossing form of the dilated source grade. -/
def fzzCigarParityDilatedTwoScaleGradeCrossing
    (beta : ℝ) (u : ℂ × ℂ) : ℂ :=
  fzzCigarParityDilatedTwoScaleKreinPairing beta u
    (fzzCigarParityDilatedTwoScaleGrade u)

/-- Exact all-scale crossing identity `C_beta(v_beta)=q_beta^(2 : ℕ) lambda_beta`. -/
theorem fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleGradeCrossing beta
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) =
      (fzzKreinQAt beta : ℂ) ^ (2 : ℕ) *
        fzzCigarParityDilatedTwoScaleKreinEigenvalue beta := by
  rw [fzzCigarParityDilatedTwoScaleGradeCrossing,
    fzzCigarParityDilatedTwoScaleGrade,
    fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedTwoScaleKreinEigenvector]
  simp only [mul_zero, add_zero]
  have hstarSub :
      star (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
          (fzzKreinPAt beta : ℂ)) =
        -fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
          (fzzKreinPAt beta : ℂ) := by
    simp [star_fzzCigarParityDilatedTwoScaleKreinEigenvalue_eq_neg]
  rw [hstarSub]
  have hstarQ : star (fzzKreinQAt beta : ℂ) = (fzzKreinQAt beta : ℂ) := by simp
  rw [hstarQ]
  have hR : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  ring_nf
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue_sq hbeta]
  rw [fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  push_cast
  field_simp
  ring

theorem fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing_im_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < (fzzCigarParityDilatedTwoScaleGradeCrossing beta
      (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)).im := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing hbeta]
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp
  have hre : ((fzzKreinQAt beta : ℂ) ^ (2 : ℕ)).re = fzzKreinQAt beta ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre]
  exact mul_pos (sq_pos_of_pos (fzzKreinQAt_pos hbeta))
    (Real.sqrt_pos.2
      (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta))

/-- Eigenvector for the conjugate member of the scale-dependent pair. -/
def fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector
    (beta : ℝ) : ℂ × ℂ :=
  ((fzzKreinQAt beta : ℂ),
    star (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta) -
      (fzzKreinPAt beta : ℂ))

theorem fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_gradeCrossing
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleGradeCrossing beta
        (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta) =
      -fzzCigarParityDilatedTwoScaleGradeCrossing beta
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing hbeta]
  rw [fzzCigarParityDilatedTwoScaleGradeCrossing,
    fzzCigarParityDilatedTwoScaleGrade,
    fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector]
  simp only [mul_zero, add_zero]
  have hs := star_fzzCigarParityDilatedTwoScaleKreinEigenvalue_eq_neg beta
  have hstarSub :
      star (-fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
          (fzzKreinPAt beta : ℂ)) =
        fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
          (fzzKreinPAt beta : ℂ) := by simp [hs]
  rw [hs, hstarSub]
  have hstarQ : star (fzzKreinQAt beta : ℂ) = (fzzKreinQAt beta : ℂ) := by simp
  rw [hstarQ]
  have hR : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  ring_nf
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue_sq hbeta]
  rw [fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  push_cast
  field_simp
  ring

theorem fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_gradeCrossing_im_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    (fzzCigarParityDilatedTwoScaleGradeCrossing beta
      (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)).im < 0 := by
  rw [fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_gradeCrossing hbeta,
    neg_im]
  exact neg_lt_zero.mpr
    (fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing_im_pos hbeta)

/-- **All-scale oriented carrier.** Every positive source dilation separates its neutral
conjugate eigenlines by strict opposite grade-crossing signs. -/
theorem fzzCigarParity_allPositiveScales_conjugatePair_gradeCrossing_oriented :
    ∀ beta : ℝ, 0 < beta →
      0 < (fzzCigarParityDilatedTwoScaleGradeCrossing beta
          (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)).im ∧
        (fzzCigarParityDilatedTwoScaleGradeCrossing beta
          (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)).im < 0 := by
  intro beta hbeta
  exact ⟨fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing_im_pos hbeta,
    fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_gradeCrossing_im_neg hbeta⟩

end

end RHTower
