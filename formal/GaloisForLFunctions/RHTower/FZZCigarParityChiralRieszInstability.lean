import GaloisForLFunctions.RHTower.FZZCigarParityGradeHermitianization

/-!
# Chiral Riesz interaction is strictly anti-stabilizing for the FZZ parity block

The literal FZZ grade crossing is the unique imaginary off-diagonal Hermitian reporter.  This
module turns that reporter into a genuine source-metric interaction: it Riesz-represents the unit
chiral form through the indefinite two-scale FZZ metric and adds an arbitrary real multiple to the
canonical source-Krein generator.

The interaction preserves formal Krein self-adjointness, but cannot restore spectral reality.  If
`E=Q(beta)^2-P(beta)R(beta)>0`, its exact instability discriminant is

`Delta_gamma = Delta_0 + gamma^2/E`.

Thus every real coupling retains an explicit nonreal neutral eigenpair, and every nonzero coupling
strictly increases its positive imaginary eigenvalue.  This closes the most direct source-native
chiral stabilization attempt: any viable FZZ/GFZZ stability mechanism must contain additional
diagonal, nonlocal, nonlinear, or singular data.
-/

open Complex

namespace RHTower

noncomputable section

def fzzCigarParityDilatedTwoScaleKreinGap (beta : ℝ) : ℝ :=
  fzzKreinQAt beta ^ 2 - fzzKreinPAt beta * fzzKreinRAt beta

theorem fzzCigarParityDilatedTwoScaleKreinGap_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityDilatedTwoScaleKreinGap beta := by
  have hminor := fzzCigarParityDilatedTwoScaleHankelMinor_neg hbeta
  rw [fzzCigarParityDilatedTwoScaleHankelMinor] at hminor
  rw [fzzCigarParityDilatedTwoScaleKreinGap]
  linarith

def fzzCigarParityHermitianUnitChiralPairing
    (u v : ℂ × ℂ) : ℂ :=
  Complex.I * star u.1 * v.2 - Complex.I * star u.2 * v.1

theorem fzzCigarParityDilatedTwoScaleKreinPairing_smul_left
    (beta : ℝ) (z : ℂ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta (z • u) v =
      star z * fzzCigarParityDilatedTwoScaleKreinPairing beta u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  simp [fzzCigarParityDilatedTwoScaleKreinPairing, star_mul]
  ring

theorem fzzCigarParityDilatedTwoScaleKreinPairing_smul_right
    (beta : ℝ) (z : ℂ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta u (z • v) =
      z * fzzCigarParityDilatedTwoScaleKreinPairing beta u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  simp [fzzCigarParityDilatedTwoScaleKreinPairing]
  ring

theorem fzzCigarParityHermitianUnitChiralPairing_self
    (u : ℂ × ℂ) :
    fzzCigarParityHermitianUnitChiralPairing u u =
      fzzCigarParityHermitianQuadraticObservable 0 0 1 0 u := by
  simp [fzzCigarParityHermitianUnitChiralPairing,
    fzzCigarParityHermitianQuadraticObservable]
  ring

def fzzCigarParityDilatedChiralRieszOperator
    (beta : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let E := fzzCigarParityDilatedTwoScaleKreinGap beta
  ((-Complex.I * ((fzzKreinQAt beta / E : ℝ) : ℂ)) * u.1 +
      (-Complex.I * ((fzzKreinRAt beta / E : ℝ) : ℂ)) * u.2,
    (Complex.I * ((fzzKreinPAt beta / E : ℝ) : ℂ)) * u.1 +
      (Complex.I * ((fzzKreinQAt beta / E : ℝ) : ℂ)) * u.2)

theorem fzzCigarParityDilatedChiralRieszOperator_represents
    {beta : ℝ} (hbeta : 0 < beta) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedChiralRieszOperator beta v) =
      fzzCigarParityHermitianUnitChiralPairing u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hgapC :
      (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) =
        (fzzKreinQAt beta : ℂ) ^ 2 -
          (fzzKreinPAt beta : ℂ) * (fzzKreinRAt beta : ℂ) := by
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    push_cast
    ring
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedChiralRieszOperator,
    fzzCigarParityHermitianUnitChiralPairing]
  field_simp [hEC]
  rw [hgapC]
  ring

theorem fzzCigarParityDilatedChiralRieszOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedChiralRieszOperator beta u) v =
      fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedChiralRieszOperator beta v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedChiralRieszOperator,
    Complex.conj_ofReal]
  field_simp [hEC]
  ring

def fzzCigarParityDilatedChiralPerturbedKreinOperator
    (beta gamma : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let Au := fzzCigarParityDilatedTwoScaleKreinOperator beta u
  let Bu := fzzCigarParityDilatedChiralRieszOperator beta u
  (Au.1 + (gamma : ℂ) * Bu.1, Au.2 + (gamma : ℂ) * Bu.2)

/-- Zero chiral coupling recovers the canonical source-Krein generator exactly. -/
theorem fzzCigarParityDilatedChiralPerturbedKreinOperator_zero
    (beta : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedChiralPerturbedKreinOperator beta 0 u =
      fzzCigarParityDilatedTwoScaleKreinOperator beta u := by
  simp [fzzCigarParityDilatedChiralPerturbedKreinOperator]

theorem fzzCigarParityDilatedChiralPerturbedKreinOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedChiralPerturbedKreinOperator beta gamma u) v =
      fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedChiralPerturbedKreinOperator beta gamma v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hR : fzzKreinRAt beta ≠ 0 := (fzzKreinRAt_pos hbeta).ne'
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  have hgapC :
      (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) =
        (fzzKreinQAt beta : ℂ) ^ 2 -
          (fzzKreinPAt beta : ℂ) * (fzzKreinRAt beta : ℂ) := by
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    push_cast
    ring
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedChiralPerturbedKreinOperator,
    fzzCigarParityDilatedTwoScaleKreinOperator,
    fzzCigarParityDilatedChiralRieszOperator,
    Complex.conj_ofReal]
  field_simp [hEC, hRC]
  rw [hgapC]
  ring

def fzzCigarParityDilatedChiralPerturbedDiag
    (beta gamma : ℝ) : ℂ :=
  (fzzKreinPAt beta : ℂ) -
    Complex.I * ((gamma * fzzKreinQAt beta /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

def fzzCigarParityDilatedChiralPerturbedUpper
    (beta gamma : ℝ) : ℂ :=
  (fzzKreinQAt beta : ℂ) -
    Complex.I * ((gamma * fzzKreinRAt beta /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

def fzzCigarParityDilatedChiralPerturbedLower
    (beta gamma : ℝ) : ℂ :=
  -((fzzKreinPAt beta * fzzKreinQAt beta /
      fzzKreinRAt beta : ℝ) : ℂ) +
    Complex.I * ((gamma * fzzKreinPAt beta /
      fzzCigarParityDilatedTwoScaleKreinGap beta : ℝ) : ℂ)

theorem fzzCigarParityDilatedChiralPerturbedKreinOperator_matrix
    (beta gamma : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedChiralPerturbedKreinOperator beta gamma u =
      (fzzCigarParityDilatedChiralPerturbedDiag beta gamma * u.1 +
          fzzCigarParityDilatedChiralPerturbedUpper beta gamma * u.2,
        fzzCigarParityDilatedChiralPerturbedLower beta gamma * u.1 -
          fzzCigarParityDilatedChiralPerturbedDiag beta gamma * u.2) := by
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext <;>
    simp [fzzCigarParityDilatedChiralPerturbedKreinOperator,
      fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParityDilatedChiralRieszOperator,
      fzzCigarParityDilatedChiralPerturbedDiag,
      fzzCigarParityDilatedChiralPerturbedUpper,
      fzzCigarParityDilatedChiralPerturbedLower] <;>
    ring

def fzzCigarParityDilatedChiralPerturbedDiscriminant
    (beta gamma : ℝ) : ℝ :=
  fzzCigarParityDilatedTwoScaleKreinDiscriminant beta +
    gamma ^ 2 / fzzCigarParityDilatedTwoScaleKreinGap beta

/-- Zero coupling recovers the original positive instability discriminant. -/
theorem fzzCigarParityDilatedChiralPerturbedDiscriminant_zero (beta : ℝ) :
    fzzCigarParityDilatedChiralPerturbedDiscriminant beta 0 =
      fzzCigarParityDilatedTwoScaleKreinDiscriminant beta := by
  simp [fzzCigarParityDilatedChiralPerturbedDiscriminant]

theorem fzzCigarParityDilatedChiralPerturbedDiscriminant_pos
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    0 < fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma := by
  rw [fzzCigarParityDilatedChiralPerturbedDiscriminant]
  have hD := fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta
  have hE := fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta
  have hnonneg : 0 ≤ gamma ^ 2 / fzzCigarParityDilatedTwoScaleKreinGap beta :=
    div_nonneg (sq_nonneg gamma) hE.le
  linarith

theorem fzzCigarParityDilatedChiralPerturbed_characteristic
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedChiralPerturbedDiag beta gamma ^ 2 +
        fzzCigarParityDilatedChiralPerturbedUpper beta gamma *
          fzzCigarParityDilatedChiralPerturbedLower beta gamma =
      -(fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma : ℂ) := by
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR : fzzKreinRAt beta ≠ 0 := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  have hgapC :
      (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) =
        (fzzKreinQAt beta : ℂ) ^ 2 -
          (fzzKreinPAt beta : ℂ) * (fzzKreinRAt beta : ℂ) := by
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    push_cast
    ring
  simp [fzzCigarParityDilatedChiralPerturbedDiag,
    fzzCigarParityDilatedChiralPerturbedUpper,
    fzzCigarParityDilatedChiralPerturbedLower,
    fzzCigarParityDilatedChiralPerturbedDiscriminant,
    fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  field_simp [hEC, hRC]
  rw [hgapC]
  ring_nf
  rw [Complex.I_sq]
  ring

def fzzCigarParityDilatedChiralPerturbedEigenvalue
    (beta gamma : ℝ) : ℂ :=
  Complex.I *
    (Real.sqrt (fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma) : ℂ)

/-- The positive-imaginary perturbed eigenvalue specializes to the canonical one at zero
coupling. -/
theorem fzzCigarParityDilatedChiralPerturbedEigenvalue_zero (beta : ℝ) :
    fzzCigarParityDilatedChiralPerturbedEigenvalue beta 0 =
      fzzCigarParityDilatedTwoScaleKreinEigenvalue beta := by
  rw [fzzCigarParityDilatedChiralPerturbedEigenvalue,
    fzzCigarParityDilatedChiralPerturbedDiscriminant_zero,
    fzzCigarParityDilatedTwoScaleKreinEigenvalue]

def fzzCigarParityDilatedChiralPerturbedEigenvector
    (beta gamma : ℝ) : ℂ × ℂ :=
  (fzzCigarParityDilatedChiralPerturbedUpper beta gamma,
    fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma -
      fzzCigarParityDilatedChiralPerturbedDiag beta gamma)

theorem fzzCigarParityDilatedChiralPerturbedEigenvalue_sq
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma ^ 2 =
      -(fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma : ℂ) := by
  rw [fzzCigarParityDilatedChiralPerturbedEigenvalue]
  have hsqrt :
      Real.sqrt (fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma) ^ 2 =
        fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma :=
    Real.sq_sqrt
      (fzzCigarParityDilatedChiralPerturbedDiscriminant_pos hbeta gamma).le
  have hcast :
      ((Real.sqrt (fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma) : ℝ) : ℂ) ^ 2 =
        (fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma : ℂ) := by
    exact_mod_cast hsqrt
  rw [mul_pow, Complex.I_sq, hcast]
  ring

theorem fzzCigarParityDilatedChiralPerturbedUpper_re
    (beta gamma : ℝ) :
    (fzzCigarParityDilatedChiralPerturbedUpper beta gamma).re =
      fzzKreinQAt beta := by
  simp [fzzCigarParityDilatedChiralPerturbedUpper]

theorem fzzCigarParityDilatedChiralPerturbedEigenvector_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp only [fzzCigarParityDilatedChiralPerturbedEigenvector, Prod.fst_zero] at hfirst
  have hre := congrArg Complex.re hfirst
  rw [fzzCigarParityDilatedChiralPerturbedUpper_re] at hre
  exact (fzzKreinQAt_pos hbeta).ne' hre

theorem fzzCigarParityDilatedChiralPerturbedEigenpair
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedChiralPerturbedKreinOperator beta gamma
        (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) =
      fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma •
        fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma := by
  rw [fzzCigarParityDilatedChiralPerturbedKreinOperator_matrix]
  apply Prod.ext
  · simp [fzzCigarParityDilatedChiralPerturbedEigenvector]
    ring
  · simp only [fzzCigarParityDilatedChiralPerturbedEigenvector,
      Prod.smul_snd, smul_eq_mul]
    have hsq :=
      fzzCigarParityDilatedChiralPerturbedEigenvalue_sq hbeta gamma
    have hchar :=
      fzzCigarParityDilatedChiralPerturbed_characteristic hbeta gamma
    calc
      fzzCigarParityDilatedChiralPerturbedLower beta gamma *
            fzzCigarParityDilatedChiralPerturbedUpper beta gamma -
          fzzCigarParityDilatedChiralPerturbedDiag beta gamma *
            (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma -
              fzzCigarParityDilatedChiralPerturbedDiag beta gamma) =
          (fzzCigarParityDilatedChiralPerturbedDiag beta gamma ^ 2 +
              fzzCigarParityDilatedChiralPerturbedUpper beta gamma *
                fzzCigarParityDilatedChiralPerturbedLower beta gamma) -
            fzzCigarParityDilatedChiralPerturbedDiag beta gamma *
              fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma := by ring
      _ = -(fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma : ℂ) -
            fzzCigarParityDilatedChiralPerturbedDiag beta gamma *
              fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma := by rw [hchar]
      _ = fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma ^ 2 -
            fzzCigarParityDilatedChiralPerturbedDiag beta gamma *
              fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma := by rw [hsq]
      _ = fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma *
            (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma -
              fzzCigarParityDilatedChiralPerturbedDiag beta gamma) := by ring

theorem fzzCigarParityDilatedChiralPerturbedEigenvalue_im_pos
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    0 < (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma).im := by
  rw [fzzCigarParityDilatedChiralPerturbedEigenvalue]
  simp only [mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, zero_add]
  simpa using Real.sqrt_pos.2
    (fzzCigarParityDilatedChiralPerturbedDiscriminant_pos hbeta gamma)

theorem fzzCigarParityDilatedChiralPerturbedEigenvalue_not_real
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma ≠
      star (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) := by
  intro h
  have him := congrArg Complex.im h
  have hstar :
      (star (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma)).im =
        -(fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma).im := by
    change ((starRingEnd ℂ)
      (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma)).im = _
    exact Complex.conj_im _
  rw [hstar] at him
  have hpos := fzzCigarParityDilatedChiralPerturbedEigenvalue_im_pos hbeta gamma
  linarith

theorem fzzCigarParityDilatedChiralPerturbedEigenvector_null
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
        (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) = 0 := by
  have hself :=
    fzzCigarParityDilatedChiralPerturbedKreinOperator_formallySelfAdjoint
      hbeta gamma
      (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
      (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
  rw [fzzCigarParityDilatedChiralPerturbedEigenpair hbeta gamma] at hself
  rw [fzzCigarParityDilatedTwoScaleKreinPairing_smul_left,
    fzzCigarParityDilatedTwoScaleKreinPairing_smul_right] at hself
  have hfactor :
      (star (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) -
          fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) *
        fzzCigarParityDilatedTwoScaleKreinPairing beta
          (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
          (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) = 0 := by
    calc
      (star (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) -
            fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) *
          fzzCigarParityDilatedTwoScaleKreinPairing beta
            (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
            (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) =
        star (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma) *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
              (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) -
          fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma *
            fzzCigarParityDilatedTwoScaleKreinPairing beta
              (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
              (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma) := by ring
      _ = 0 := sub_eq_zero.mpr hself
  exact (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr
      (fzzCigarParityDilatedChiralPerturbedEigenvalue_not_real hbeta gamma).symm)

/-- Proposed spectral-reality conclusion for a fixed real chiral coupling at one source scale. -/
def FZZCigarParityDilatedChiralPerturbedSpectrallyReal
    (beta gamma : ℝ) : Prop :=
  ∀ lambda : ℂ, ∀ v : ℂ × ℂ,
    v ≠ 0 →
    fzzCigarParityDilatedChiralPerturbedKreinOperator beta gamma v = lambda • v →
    lambda = star lambda

/-- **Chiral Riesz stability no-go.** No real coupling of the source-native chiral interaction
restores spectral reality at any positive physical scale. -/
theorem not_fzzCigarParityDilatedChiralPerturbedSpectrallyReal
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    ¬ FZZCigarParityDilatedChiralPerturbedSpectrallyReal beta gamma := by
  intro hreal
  exact fzzCigarParityDilatedChiralPerturbedEigenvalue_not_real hbeta gamma
    (hreal (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma)
      (fzzCigarParityDilatedChiralPerturbedEigenvector beta gamma)
      (fzzCigarParityDilatedChiralPerturbedEigenvector_ne_zero hbeta gamma)
      (fzzCigarParityDilatedChiralPerturbedEigenpair hbeta gamma))

theorem fzzCigarParityDilatedChiralPerturbedDiscriminant_gt
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : gamma ≠ 0) :
    fzzCigarParityDilatedTwoScaleKreinDiscriminant beta <
      fzzCigarParityDilatedChiralPerturbedDiscriminant beta gamma := by
  rw [fzzCigarParityDilatedChiralPerturbedDiscriminant]
  have hsq : 0 < gamma ^ 2 := sq_pos_of_ne_zero hgamma
  have hE := fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta
  have hquot : 0 < gamma ^ 2 / fzzCigarParityDilatedTwoScaleKreinGap beta :=
    div_pos hsq hE
  linarith

theorem fzzCigarParityDilatedChiralPerturbedEigenvalue_im_gt
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : gamma ≠ 0) :
    (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta).im <
      (fzzCigarParityDilatedChiralPerturbedEigenvalue beta gamma).im := by
  rw [fzzCigarParityDilatedTwoScaleKreinEigenvalue,
    fzzCigarParityDilatedChiralPerturbedEigenvalue]
  simp only [mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, zero_add]
  simpa using Real.sqrt_lt_sqrt
    (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta).le
    (fzzCigarParityDilatedChiralPerturbedDiscriminant_gt hbeta hgamma)

end

end RHTower
