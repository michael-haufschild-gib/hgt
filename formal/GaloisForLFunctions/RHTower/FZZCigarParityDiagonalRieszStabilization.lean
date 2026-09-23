import GaloisForLFunctions.RHTower.FZZCigarParityChiralRieszInstability
import GaloisForLFunctions.RHTower.FZZCigarParityHermitianReflectionDetectorCone

/-!
# Source-gap diagonal Riesz stabilization of the FZZ parity block

The unit second-coordinate Hermitian reporter lies inside the sharp FZZ reflection-detector cone.
This module Riesz-represents that reporter through the literal indefinite source metric and adds it
to the canonical source-Krein generator.

At the canonical negative coupling given by the source gap `-(Q^(2 : ℕ)-PR)`, the perturbed generator
collapses to a rank-one triangular operator satisfying `A^(2 : ℕ)=P A`.  Its entire spectrum is real at
every positive physical scale.  Yet equality of the same diagonal reporter on a Mellin carrier and
its functional reflection remains exactly the critical-line equation.  Thus local source spectral
stability is unconditional and cannot replace the missing reflected-energy matching law.
-/

open Complex

namespace RHTower

noncomputable section

/-- Sesquilinear form of the unit second-coordinate diagonal reporter. -/
def fzzCigarParityHermitianUnitSecondDiagonalPairing
    (u v : ℂ × ℂ) : ℂ :=
  star u.2 * v.2

theorem fzzCigarParityHermitianUnitSecondDiagonalPairing_self
    (u : ℂ × ℂ) :
    fzzCigarParityHermitianUnitSecondDiagonalPairing u u =
      fzzCigarParityHermitianQuadraticObservable 0 0 0 1 u := by
  simp [fzzCigarParityHermitianUnitSecondDiagonalPairing,
    fzzCigarParityHermitianQuadraticObservable]

/-- Source-metric Riesz representative of the unit second-coordinate diagonal reporter. -/
def fzzCigarParityDilatedSecondDiagonalRieszOperator
    (beta : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let E := fzzCigarParityDilatedTwoScaleKreinGap beta
  (((fzzKreinQAt beta / E : ℝ) : ℂ) * u.2,
    (-((fzzKreinPAt beta / E : ℝ) : ℂ)) * u.2)

theorem fzzCigarParityDilatedSecondDiagonalRieszOperator_represents
    {beta : ℝ} (hbeta : 0 < beta) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedSecondDiagonalRieszOperator beta v) =
      fzzCigarParityHermitianUnitSecondDiagonalPairing u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hgapC :
      (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) =
        (fzzKreinQAt beta : ℂ) ^ (2 : ℕ) -
          (fzzKreinPAt beta : ℂ) * (fzzKreinRAt beta : ℂ) := by
    rw [fzzCigarParityDilatedTwoScaleKreinGap]
    push_cast
    ring
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedSecondDiagonalRieszOperator,
    fzzCigarParityHermitianUnitSecondDiagonalPairing]
  field_simp [hEC]
  rw [hgapC]
  ring

theorem fzzCigarParityDilatedSecondDiagonalRieszOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedSecondDiagonalRieszOperator beta u) v =
      fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedSecondDiagonalRieszOperator beta v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedSecondDiagonalRieszOperator,
    Complex.conj_ofReal]
  field_simp [hEC]
  ring

/-- Canonical source generator perturbed by a real multiple of diagonal detector energy. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator
    (beta gamma : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let Au := fzzCigarParityDilatedTwoScaleKreinOperator beta u
  let Bu := fzzCigarParityDilatedSecondDiagonalRieszOperator beta u
  (Au.1 + (gamma : ℂ) * Bu.1, Au.2 + (gamma : ℂ) * Bu.2)

theorem fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_zero
    (beta : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta 0 u =
      fzzCigarParityDilatedTwoScaleKreinOperator beta u := by
  simp [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator]

theorem fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_formallySelfAdjoint
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma u) v =
      fzzCigarParityDilatedTwoScaleKreinPairing beta u
        (fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR : fzzKreinRAt beta ≠ 0 := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator,
    fzzCigarParityDilatedTwoScaleKreinOperator,
    fzzCigarParityDilatedSecondDiagonalRieszOperator,
    Complex.conj_ofReal]
  field_simp [hEC, hRC]
  ring

theorem fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_matrix
    (beta gamma : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma u =
      ((fzzKreinPAt beta : ℂ) * u.1 +
          ((fzzKreinQAt beta *
            (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) : ℝ) : ℂ) * u.2,
        (-((fzzKreinPAt beta * fzzKreinQAt beta /
            fzzKreinRAt beta : ℝ) : ℂ)) * u.1 -
          ((fzzKreinPAt beta *
            (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) : ℝ) : ℂ) * u.2) := by
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext <;>
    simp [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator,
      fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParityDilatedSecondDiagonalRieszOperator] <;>
    ring

/-- Real trace coefficient of the diagonal Riesz perturbation. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedTrace
    (beta gamma : ℝ) : ℝ :=
  -(gamma * fzzKreinPAt beta /
    fzzCigarParityDilatedTwoScaleKreinGap beta)

/-- Real determinant coefficient of the diagonal Riesz perturbation. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant
    (beta gamma : ℝ) : ℝ :=
  fzzCigarParityDilatedTwoScaleKreinDiscriminant beta *
    (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta)

/-- Characteristic discriminant of the diagonal Riesz perturbation. -/
def fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant
    (beta gamma : ℝ) : ℝ :=
  fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma ^ (2 : ℕ) -
    4 * fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma

theorem fzzCigarParityDilatedSecondDiagonalPerturbed_trace_eq
    (beta gamma : ℝ) :
    (fzzKreinPAt beta : ℂ) -
        ((fzzKreinPAt beta *
          (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) : ℝ) : ℂ) =
      (fzzCigarParityDilatedSecondDiagonalPerturbedTrace beta gamma : ℂ) := by
  simp [fzzCigarParityDilatedSecondDiagonalPerturbedTrace]
  ring

theorem fzzCigarParityDilatedSecondDiagonalPerturbed_determinant_eq
    {beta : ℝ} (hbeta : 0 < beta) (gamma : ℝ) :
    (fzzKreinPAt beta : ℂ) *
          (-((fzzKreinPAt beta *
            (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) : ℝ) : ℂ)) -
        ((fzzKreinQAt beta *
          (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) : ℝ) : ℂ) *
          (-((fzzKreinPAt beta * fzzKreinQAt beta /
            fzzKreinRAt beta : ℝ) : ℂ)) =
      (fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta gamma : ℂ) := by
  have hE : fzzCigarParityDilatedTwoScaleKreinGap beta ≠ 0 :=
    (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  have hR : fzzKreinRAt beta ≠ 0 := (fzzKreinRAt_pos hbeta).ne'
  have hEC : (fzzCigarParityDilatedTwoScaleKreinGap beta : ℂ) ≠ 0 := by
    exact_mod_cast hE
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hR
  simp [fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant,
    fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  field_simp [hEC, hRC]
  ring

theorem fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq
    (beta gamma : ℝ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta gamma =
      gamma ^ (2 : ℕ) * fzzKreinPAt beta ^ (2 : ℕ) /
          fzzCigarParityDilatedTwoScaleKreinGap beta ^ (2 : ℕ) -
        4 * fzzCigarParityDilatedTwoScaleKreinDiscriminant beta *
          (1 + gamma / fzzCigarParityDilatedTwoScaleKreinGap beta) := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant,
    fzzCigarParityDilatedSecondDiagonalPerturbedTrace,
    fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant]
  ring

/-- Canonical negative coupling selected only by the source gap. -/
def fzzCigarParityDilatedSecondDiagonalStabilizingCoupling
    (beta : ℝ) : ℝ :=
  -fzzCigarParityDilatedTwoScaleKreinGap beta

theorem fzzCigarParityDilatedSecondDiagonalStabilizingCoupling_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta < 0 := by
  exact neg_neg_of_pos (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta)

/-- At source-gap coupling the second column vanishes and the generator becomes triangular. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
        (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) u =
      ((fzzKreinPAt beta : ℂ) * u.1,
        (-((fzzKreinPAt beta * fzzKreinQAt beta /
          fzzKreinRAt beta : ℝ) : ℂ)) * u.1) := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_matrix]
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  simp [fzzCigarParityDilatedSecondDiagonalStabilizingCoupling, hE]

/-- Rank-one polynomial law at the canonical stabilizing coupling. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_sq
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
        (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta)
        (fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
          (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) u) =
      (fzzKreinPAt beta : ℂ) •
        fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
          (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) u := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta,
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta]
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext
  · simp [smul_eq_mul]
  · simp [smul_eq_mul]
    ring

theorem fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant_stabilizingCoupling
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant beta
      (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) = 0 := by
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  simp [fzzCigarParityDilatedSecondDiagonalPerturbedDeterminant,
    fzzCigarParityDilatedSecondDiagonalStabilizingCoupling, hE]

theorem fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_stabilizingCoupling
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant beta
        (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) =
      fzzKreinPAt beta ^ (2 : ℕ) := by
  have hE := (fzzCigarParityDilatedTwoScaleKreinGap_pos hbeta).ne'
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq]
  simp [fzzCigarParityDilatedSecondDiagonalStabilizingCoupling, hE]

/-- Spectral-reality property for one diagonal Riesz coupling. -/
def FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal
    (beta gamma : ℝ) : Prop :=
  ∀ lambda : ℂ, ∀ v : ℂ × ℂ,
    v ≠ 0 →
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta gamma v =
      lambda • v →
    lambda = star lambda

/-- The canonical source-gap coupling has real spectrum at every positive scale. -/
theorem fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_stabilizingCoupling
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
      (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) := by
  intro lambda v hv heigen
  rcases v with ⟨u₁, u₂⟩
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta]
    at heigen
  have hfirst := congrArg Prod.fst heigen
  have hsecond := congrArg Prod.snd heigen
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfirst hsecond
  by_cases hu₁ : u₁ = 0
  · have hu₂ : u₂ ≠ 0 := by
      intro hu₂
      apply hv
      simp [hu₁, hu₂]
    rw [hu₁] at hsecond
    simp only [mul_zero] at hsecond
    have hlambda : lambda = 0 :=
      (mul_eq_zero.mp hsecond.symm).resolve_right hu₂
    simp [hlambda]
  · have hcoeff : (fzzKreinPAt beta : ℂ) = lambda :=
      mul_right_cancel₀ hu₁ hfirst
    rw [← hcoeff]
    simp

/-- Two explicit nonzero eigenpairs of the rank-one stabilized generator. -/
theorem fzzCigarParityDilatedSecondDiagonalStabilized_eigenpairs
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
        (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta)
        (0, 1) = 0 • (0, 1) ∧
      fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
        (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta)
        ((fzzKreinRAt beta : ℂ), -(fzzKreinQAt beta : ℂ)) =
          (fzzKreinPAt beta : ℂ) •
            ((fzzKreinRAt beta : ℂ), -(fzzKreinQAt beta : ℂ)) := by
  have hRC : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  constructor
  · rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta]
    apply Prod.ext <;> simp
  · rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta]
    apply Prod.ext
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]
      field_simp [hRC]

/-- The unit diagonal energy remains an exact pointwise critical-line detector under functional
reflection, independently of unconditional source-block stabilization. -/
theorem fzzCigarParityMellinCharacterUnitSecondDiagonalReading_eq_reflection_iff
    (rho : ℂ) :
    fzzCigarParityMellinCharacterHermitianReading 0 0 0 1 rho =
        fzzCigarParityMellinCharacterHermitianReading 0 0 0 1
          (criticalLineReflectionPoint rho) ↔
      rho.re = 1 / 2 := by
  exact fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
    0 0 0 1 (by simp) (by simp) rho

/-- Every positive scale admits a negative coupling, determined entirely by source coefficients,
whose local perturbed spectrum is real. -/
theorem fzzCigarParity_allPositiveScales_exists_negative_diagonalStabilizingCoupling :
    ∀ beta : ℝ, 0 < beta →
      ∃ gamma : ℝ, gamma < 0 ∧
        FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta gamma := by
  intro beta hbeta
  exact
    ⟨fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta,
      fzzCigarParityDilatedSecondDiagonalStabilizingCoupling_neg hbeta,
      fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_stabilizingCoupling hbeta⟩

/-- **Stability-selection separation.** Every positive source scale has a canonical negative
diagonal coupling with globally real local spectrum, while reflected equality of its generating
energy still cuts out exactly the critical line on every Mellin carrier. -/
theorem fzzCigarParity_allPositiveScales_diagonalStability_and_reflectionDetector :
    ∀ beta : ℝ, 0 < beta →
      FZZCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal beta
          (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) ∧
        ∀ rho : ℂ,
          (fzzCigarParityMellinCharacterHermitianReading 0 0 0 1 rho =
              fzzCigarParityMellinCharacterHermitianReading 0 0 0 1
                (criticalLineReflectionPoint rho) ↔
            rho.re = 1 / 2) := by
  intro beta hbeta
  exact
    ⟨fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_stabilizingCoupling hbeta,
      fun rho =>
        fzzCigarParityMellinCharacterUnitSecondDiagonalReading_eq_reflection_iff rho⟩

end

end RHTower
