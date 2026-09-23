import GaloisForLFunctions.RHTower.FZZCigarParityTwoScaleKreinSelfAdjointNoGo

/-!
# Grade crossing orients the neutral FZZ Krein pair

The literal two-scale FZZ Krein operator has a conjugate pair of nonreal neutral eigenmodes, so
formal self-adjointness cannot force spectral reality. Neutrality does not erase all source
orientation, however. The natural scale grade, projecting onto the second source scale, crosses
the two null lines with opposite signs.

This file proves the exact crossing law

`B(v, Dv) = P(2)^(2 : ℕ) * lambda`

for the positive-imaginary source eigenmode. Its imaginary part is strictly positive; the conjugate
mode has exactly the negative crossing. This is a coefficient-faithful oriented survivor, obtained
before any Xi divisor specialization.

It is not an RH proof: the remaining dynamical gate is to construct the corresponding full
interacting FZZ/GFZZ crossing and prove that every parity-Mellin divisor mode lies in one fixed
physical crossing chamber.
-/

open Complex

namespace RHTower

noncomputable section

/-- Natural grade projection distinguishing the second multiplicative source scale. -/
def fzzCigarParityTwoScaleGrade (u : ℂ × ℂ) : ℂ × ℂ :=
  (0, u.2)

/-- Null-line crossing form of the natural source grade. -/
def fzzCigarParityTwoScaleGradeCrossing (u : ℂ × ℂ) : ℂ :=
  fzzCigarParityTwoScaleKreinPairing u
    (fzzCigarParityTwoScaleGrade u)

theorem star_fzzCigarParityTwoScaleKreinEigenvalue_eq_neg :
    star fzzCigarParityTwoScaleKreinEigenvalue =
      -fzzCigarParityTwoScaleKreinEigenvalue := by
  rw [fzzCigarParityTwoScaleKreinEigenvalue]
  simp

/-- **Exact FZZ null-crossing law.** The natural grade crossing is the square of the physical
off-diagonal source coefficient times the nonreal eigenvalue. -/
theorem fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing :
    fzzCigarParityTwoScaleGradeCrossing
        fzzCigarParityTwoScaleKreinEigenvector =
      (fzzKreinQ : ℂ) ^ (2 : ℕ) *
        fzzCigarParityTwoScaleKreinEigenvalue := by
  rw [fzzCigarParityTwoScaleGradeCrossing,
    fzzCigarParityTwoScaleGrade, fzzCigarParityTwoScaleKreinPairing,
    fzzCigarParityTwoScaleKreinEigenvector]
  simp only [mul_zero, add_zero]
  have hstarSub :
      star (fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ)) =
        -fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ) := by
    simp [star_fzzCigarParityTwoScaleKreinEigenvalue_eq_neg]
  rw [hstarSub]
  have hstarQ : star (fzzKreinQ : ℂ) = (fzzKreinQ : ℂ) := by simp
  rw [hstarQ]
  have hR : (fzzKreinR : ℂ) ≠ 0 := by exact_mod_cast fzzKreinR_pos.ne'
  ring_nf
  rw [fzzCigarParityTwoScaleKreinEigenvalue_sq]
  rw [fzzCigarParityTwoScaleKreinDiscriminant]
  push_cast
  field_simp
  ring

/-- The positive-imaginary source mode has strict positive crossing orientation. -/
theorem fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_im_pos :
    0 < (fzzCigarParityTwoScaleGradeCrossing
      fzzCigarParityTwoScaleKreinEigenvector).im := by
  rw [fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing,
    fzzCigarParityTwoScaleKreinEigenvalue]
  simp
  have hre : ((fzzKreinQ : ℂ) ^ (2 : ℕ)).re = fzzKreinQ ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre]
  have hQ : 0 < fzzKreinQ := by
    change 0 < fzzCigarParityDelay 2
    rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 2)]
    positivity
  exact mul_pos (sq_pos_of_pos hQ)
    (Real.sqrt_pos.2 fzzCigarParityTwoScaleKreinDiscriminant_pos)

theorem fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_ne_zero :
    fzzCigarParityTwoScaleGradeCrossing
      fzzCigarParityTwoScaleKreinEigenvector ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [zero_im] at him
  exact (ne_of_gt
    fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_im_pos) him

/-- Source eigenvector for the conjugate member of the complex Krein pair. -/
def fzzCigarParityTwoScaleConjugateKreinEigenvector : ℂ × ℂ :=
  ((fzzKreinQ : ℂ),
    star fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ))

/-- Conjugation reverses the natural grade crossing exactly. -/
theorem fzzCigarParityTwoScaleConjugateKreinEigenvector_gradeCrossing :
    fzzCigarParityTwoScaleGradeCrossing
        fzzCigarParityTwoScaleConjugateKreinEigenvector =
      -fzzCigarParityTwoScaleGradeCrossing
        fzzCigarParityTwoScaleKreinEigenvector := by
  rw [fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing]
  rw [fzzCigarParityTwoScaleGradeCrossing,
    fzzCigarParityTwoScaleGrade, fzzCigarParityTwoScaleKreinPairing,
    fzzCigarParityTwoScaleConjugateKreinEigenvector]
  simp only [mul_zero, add_zero]
  have hs : star fzzCigarParityTwoScaleKreinEigenvalue =
      -fzzCigarParityTwoScaleKreinEigenvalue :=
    star_fzzCigarParityTwoScaleKreinEigenvalue_eq_neg
  have hstarSub :
      star (-fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ)) =
        fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ) := by simp [hs]
  rw [hs, hstarSub]
  have hstarQ : star (fzzKreinQ : ℂ) = (fzzKreinQ : ℂ) := by simp
  rw [hstarQ]
  have hR : (fzzKreinR : ℂ) ≠ 0 := by exact_mod_cast fzzKreinR_pos.ne'
  ring_nf
  rw [fzzCigarParityTwoScaleKreinEigenvalue_sq]
  rw [fzzCigarParityTwoScaleKreinDiscriminant]
  push_cast
  field_simp
  ring

theorem fzzCigarParityTwoScaleConjugateKreinEigenvector_gradeCrossing_im_neg :
    (fzzCigarParityTwoScaleGradeCrossing
      fzzCigarParityTwoScaleConjugateKreinEigenvector).im < 0 := by
  rw [fzzCigarParityTwoScaleConjugateKreinEigenvector_gradeCrossing, neg_im]
  exact neg_lt_zero.mpr
    fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_im_pos

/-- **Oriented conjugate-pair survivor.** The literal source grade separates the two neutral modes
by strict opposite crossing signs. -/
theorem fzzCigarParityTwoScaleKrein_conjugatePair_gradeCrossing_oriented :
    0 < (fzzCigarParityTwoScaleGradeCrossing
        fzzCigarParityTwoScaleKreinEigenvector).im ∧
      (fzzCigarParityTwoScaleGradeCrossing
        fzzCigarParityTwoScaleConjugateKreinEigenvector).im < 0 :=
  ⟨fzzCigarParityTwoScaleKreinEigenvector_gradeCrossing_im_pos,
    fzzCigarParityTwoScaleConjugateKreinEigenvector_gradeCrossing_im_neg⟩

end

end RHTower
