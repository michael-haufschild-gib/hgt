import GaloisForLFunctions.RHTower.FZZCigarParityFermiHankelPositivityNoGo

/-!
# FZZ two-scale Krein self-adjointness does not force spectral reality

The literal multiplicative Fermi kernel has split signature already on scales `1` and `2`.
One might replace failed Hilbert positivity by formal self-adjointness in that source-derived Krein
form. This file proves a sharp no-go.

Using only the three literal source values `P(1), P(2), P(4)`, we construct a traceless operator
formally self-adjoint for the two-scale FZZ pairing. Its source discriminant is strictly positive,
yet it has an explicit nonzero neutral eigenvector with a strictly nonreal eigenvalue. Thus bare
Krein self-adjointness cannot orient the FZZ parity divisor.

The positive survivor is the exact complex-pair normal form forced by the source's negative
Hankel minor. A successful indefinite route must add a source-derived definite invariant subspace,
a signed crossing law, or a dynamical exclusion of neutral eigenmodes.
-/

open Complex

namespace RHTower

noncomputable section

/-- First diagonal value of the two-scale FZZ parity kernel. -/
abbrev fzzKreinP : ℝ := fzzCigarParityDelay 1

/-- Off-diagonal value of the two-scale FZZ parity kernel. -/
abbrev fzzKreinQ : ℝ := fzzCigarParityDelay 2

/-- Second diagonal value of the two-scale FZZ parity kernel. -/
abbrev fzzKreinR : ℝ := fzzCigarParityDelay 4

/-- Source-exact Hermitian pairing of the literal two-scale FZZ parity block. -/
def fzzCigarParityTwoScaleKreinPairing (u v : ℂ × ℂ) : ℂ :=
  (fzzKreinP : ℂ) * star u.1 * v.1 +
    (fzzKreinQ : ℂ) * star u.1 * v.2 +
    (fzzKreinQ : ℂ) * star u.2 * v.1 +
    (fzzKreinR : ℂ) * star u.2 * v.2

/-- Canonical traceless operator adapted algebraically to the source Krein form. -/
def fzzCigarParityTwoScaleKreinOperator (u : ℂ × ℂ) : ℂ × ℂ :=
  ((fzzKreinP : ℂ) * u.1 + (fzzKreinQ : ℂ) * u.2,
    (-((fzzKreinP * fzzKreinQ / fzzKreinR : ℝ) : ℂ)) * u.1 -
      (fzzKreinP : ℂ) * u.2)

theorem fzzKreinR_pos : 0 < fzzKreinR := by
  change 0 < fzzCigarParityDelay 4
  rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 4)]
  positivity

/-- The canonical source operator is formally self-adjoint for the literal FZZ Krein pairing. -/
theorem fzzCigarParityTwoScaleKreinOperator_formallySelfAdjoint :
    ∀ u v : ℂ × ℂ,
      fzzCigarParityTwoScaleKreinPairing
          (fzzCigarParityTwoScaleKreinOperator u) v =
        fzzCigarParityTwoScaleKreinPairing u
          (fzzCigarParityTwoScaleKreinOperator v) := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  simp [fzzCigarParityTwoScaleKreinPairing,
    fzzCigarParityTwoScaleKreinOperator]
  have hR : (fzzKreinR : ℂ) ≠ 0 := by exact_mod_cast fzzKreinR_pos.ne'
  field_simp
  ring

/-- Positive discriminant complementary to the strictly negative source Hankel determinant. -/
def fzzCigarParityTwoScaleKreinDiscriminant : ℝ :=
  fzzKreinP * (fzzKreinQ ^ 2 - fzzKreinP * fzzKreinR) / fzzKreinR

theorem fzzCigarParityTwoScaleKreinDiscriminant_pos :
    0 < fzzCigarParityTwoScaleKreinDiscriminant := by
  have hP : 0 < fzzKreinP := by
    change 0 < fzzCigarParityDelay 1
    rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 1)]
    positivity
  have hminor := fzzCigarParityTwoScaleHankelMinor_neg
  change fzzKreinP * fzzKreinR - fzzKreinQ ^ 2 < 0 at hminor
  rw [fzzCigarParityTwoScaleKreinDiscriminant]
  exact div_pos (mul_pos hP (by linarith)) fzzKreinR_pos

/-- Positive-imaginary member of the canonical conjugate eigenvalue pair. -/
def fzzCigarParityTwoScaleKreinEigenvalue : ℂ :=
  I * (Real.sqrt fzzCigarParityTwoScaleKreinDiscriminant : ℂ)

/-- Explicit source-coordinate eigenvector of the canonical Krein operator. -/
def fzzCigarParityTwoScaleKreinEigenvector : ℂ × ℂ :=
  ((fzzKreinQ : ℂ),
    fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ))

theorem fzzCigarParityTwoScaleKreinEigenvalue_sq :
    fzzCigarParityTwoScaleKreinEigenvalue ^ 2 =
      -(fzzCigarParityTwoScaleKreinDiscriminant : ℂ) := by
  rw [fzzCigarParityTwoScaleKreinEigenvalue]
  have hsqrt : Real.sqrt fzzCigarParityTwoScaleKreinDiscriminant ^ 2 =
      fzzCigarParityTwoScaleKreinDiscriminant :=
    Real.sq_sqrt fzzCigarParityTwoScaleKreinDiscriminant_pos.le
  have hcast : ((Real.sqrt fzzCigarParityTwoScaleKreinDiscriminant : ℝ) : ℂ) ^ 2 =
      (fzzCigarParityTwoScaleKreinDiscriminant : ℂ) := by exact_mod_cast hsqrt
  rw [mul_pow, I_sq, hcast]
  ring

theorem fzzCigarParityTwoScaleKreinEigenvector_ne_zero :
    fzzCigarParityTwoScaleKreinEigenvector ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp only [fzzCigarParityTwoScaleKreinEigenvector, Prod.fst_zero] at hfirst
  have hQ : 0 < fzzKreinQ := by
    change 0 < fzzCigarParityDelay 2
    rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 2)]
    positivity
  exact (ofReal_ne_zero.mpr hQ.ne') hfirst

/-- Explicit nonreal eigenpair of the formally source-Krein-self-adjoint operator. -/
theorem fzzCigarParityTwoScaleKreinEigenpair :
    fzzCigarParityTwoScaleKreinOperator
        fzzCigarParityTwoScaleKreinEigenvector =
      fzzCigarParityTwoScaleKreinEigenvalue •
        fzzCigarParityTwoScaleKreinEigenvector := by
  apply Prod.ext
  · simp only [fzzCigarParityTwoScaleKreinOperator,
      fzzCigarParityTwoScaleKreinEigenvector, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [fzzCigarParityTwoScaleKreinOperator,
      fzzCigarParityTwoScaleKreinEigenvector, Prod.smul_snd, smul_eq_mul]
    have hR : (fzzKreinR : ℂ) ≠ 0 := by exact_mod_cast fzzKreinR_pos.ne'
    calc
      -((fzzKreinP * fzzKreinQ / fzzKreinR : ℝ) : ℂ) * (fzzKreinQ : ℂ) -
          (fzzKreinP : ℂ) *
            (fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ)) =
          -(fzzCigarParityTwoScaleKreinDiscriminant : ℂ) -
            (fzzKreinP : ℂ) * fzzCigarParityTwoScaleKreinEigenvalue := by
              rw [fzzCigarParityTwoScaleKreinDiscriminant]
              push_cast
              field_simp
              ring
      _ = fzzCigarParityTwoScaleKreinEigenvalue ^ 2 -
            (fzzKreinP : ℂ) * fzzCigarParityTwoScaleKreinEigenvalue := by
              rw [fzzCigarParityTwoScaleKreinEigenvalue_sq]
      _ = fzzCigarParityTwoScaleKreinEigenvalue *
            (fzzCigarParityTwoScaleKreinEigenvalue - (fzzKreinP : ℂ)) := by ring

/-- The canonical eigenvalue is strictly nonreal. -/
theorem fzzCigarParityTwoScaleKreinEigenvalue_not_real :
    fzzCigarParityTwoScaleKreinEigenvalue ≠
      star fzzCigarParityTwoScaleKreinEigenvalue := by
  have himpos : 0 < fzzCigarParityTwoScaleKreinEigenvalue.im := by
    rw [fzzCigarParityTwoScaleKreinEigenvalue]
    simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, zero_add]
    simpa using Real.sqrt_pos.2 fzzCigarParityTwoScaleKreinDiscriminant_pos
  intro h
  have him := congrArg Complex.im h
  have hstar : (star fzzCigarParityTwoScaleKreinEigenvalue).im =
      -fzzCigarParityTwoScaleKreinEigenvalue.im := by
    change ((starRingEnd ℂ) fzzCigarParityTwoScaleKreinEigenvalue).im =
      -fzzCigarParityTwoScaleKreinEigenvalue.im
    exact Complex.conj_im fzzCigarParityTwoScaleKreinEigenvalue
  rw [hstar] at him
  linarith

/-- As Krein theory predicts, the explicit nonreal eigenvector is neutral for the source form. -/
theorem fzzCigarParityTwoScaleKreinEigenvector_null :
    fzzCigarParityTwoScaleKreinPairing
      fzzCigarParityTwoScaleKreinEigenvector
      fzzCigarParityTwoScaleKreinEigenvector = 0 := by
  have hself := fzzCigarParityTwoScaleKreinOperator_formallySelfAdjoint
    fzzCigarParityTwoScaleKreinEigenvector
    fzzCigarParityTwoScaleKreinEigenvector
  rw [fzzCigarParityTwoScaleKreinEigenpair] at hself
  simp [fzzCigarParityTwoScaleKreinPairing] at hself
  have hfactor :
      (star fzzCigarParityTwoScaleKreinEigenvalue -
          fzzCigarParityTwoScaleKreinEigenvalue) *
        fzzCigarParityTwoScaleKreinPairing
          fzzCigarParityTwoScaleKreinEigenvector
          fzzCigarParityTwoScaleKreinEigenvector = 0 := by
    rw [fzzCigarParityTwoScaleKreinPairing]
    linear_combination hself
  exact (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr fzzCigarParityTwoScaleKreinEigenvalue_not_real.symm)

/-- Proposed spectral-reality consequence of formal self-adjointness for the fixed source
operator. -/
def FZZCigarParityTwoScaleKreinSelfAdjointSpectrallyReal : Prop :=
  ∀ lambda : ℂ, ∀ v : ℂ × ℂ, v ≠ 0 →
    fzzCigarParityTwoScaleKreinOperator v = lambda • v →
      lambda = star lambda

/-- **Krein self-adjointness no-go.** The fixed, formally source-self-adjoint operator already has
a nonreal neutral eigenmode. -/
theorem not_fzzCigarParityTwoScaleKreinSelfAdjointSpectrallyReal :
    ¬ FZZCigarParityTwoScaleKreinSelfAdjointSpectrallyReal := by
  intro hreal
  exact fzzCigarParityTwoScaleKreinEigenvalue_not_real
    (hreal fzzCigarParityTwoScaleKreinEigenvalue
      fzzCigarParityTwoScaleKreinEigenvector
      fzzCigarParityTwoScaleKreinEigenvector_ne_zero
      fzzCigarParityTwoScaleKreinEigenpair)

end

end RHTower
