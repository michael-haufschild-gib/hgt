import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticSkewAdjointDefect
import GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticSpectralDecayEquivalence

/-!
# Theta-source skew-adjoint defect criterion

For an actual corrected finite theta stage `Mₖ`, define the coefficient-only energy

`Aₖ = ‖Mₖ - Mₖᴴ‖²_HS`.

The finite skew-adjoint majorant and the uniform theta Hilbert--Schmidt ceiling give, for every
Schur realization,

`Q₄(Mₖ) ≤ 575 * thetaSourceSignedHSCeiling² * Aₖ`.

Consequently, arbitrarily late stages with arbitrarily small `Aₖ` force cofinally small positive
quartic charge and hence the Riemann hypothesis.  The premise contains no root, eigenvalue,
determinant zero, or Schur packet.
-/

open Complex Filter Matrix
open scoped BigOperators Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- Entrywise skew-adjoint Hilbert--Schmidt energy of one actual finite theta stage. -/
def thetaSourceSignedStageSkewAdjointEnergy (k : ℕ) : ℝ :=
  finiteMatrixSkewAdjointEnergy (thetaSourceSignedStageFinMatrix k)

/-- Explicit coefficient formula; no spectral data occur. -/
theorem thetaSourceSignedStageSkewAdjointEnergy_eq_sum (k : ℕ) :
    thetaSourceSignedStageSkewAdjointEnergy k =
      ∑ i, ∑ j,
        ‖thetaSourceSignedStageFinMatrix k i j -
          (starRingEnd ℂ) (thetaSourceSignedStageFinMatrix k j i)‖ ^ 2 := by
  rfl

/-- The quadratic trace-energy defect of an actual stage is half its skew-adjoint energy. -/
theorem thetaSourceSignedStageQuadraticTraceEnergyDefect_eq_half_skewAdjointEnergy
    (k : ℕ) :
    finiteMatrixQuadraticTraceEnergyDefect (thetaSourceSignedStageFinMatrix k) =
      (1 / 2 : ℝ) * thetaSourceSignedStageSkewAdjointEnergy k := by
  exact finiteMatrixQuadraticTraceEnergyDefect_eq_half_skewAdjointEnergy _

theorem thetaSourceSignedStageSkewAdjointEnergy_nonneg (k : ℕ) :
    0 ≤ thetaSourceSignedStageSkewAdjointEnergy k :=
  finiteMatrixSkewAdjointEnergy_nonneg _

/-- Actual-stage quartic charge is bounded by the stage's root-free skew-adjoint energy. -/
theorem thetaSourceStageSchurPositiveQuarticCharge_le_skewAdjointEnergy
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    thetaSourceStageSchurPositiveQuarticCharge S ≤
      575 * matHSNormSq (thetaSourceSignedStageFinMatrix k) *
        thetaSourceSignedStageSkewAdjointEnergy k := by
  exact finiteMatrixSchurPositiveQuarticCharge_le_skewAdjointEnergy
    S.toFiniteMatrixSchurPacket

/-- Uniform source-only majorant, independent of the stage dimension and Schur realization. -/
theorem thetaSourceStageSchurPositiveQuarticCharge_le_ceiling_mul_skewAdjointEnergy
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    thetaSourceStageSchurPositiveQuarticCharge S ≤
      575 * thetaSourceSignedHSCeiling ^ 2 *
        thetaSourceSignedStageSkewAdjointEnergy k := by
  have henergy := thetaSourceSignedStageSkewAdjointEnergy_nonneg k
  exact (thetaSourceStageSchurPositiveQuarticCharge_le_skewAdjointEnergy S).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k) (by norm_num))
      henergy)

/-- Cofinal smallness of one coefficient-only scalar on actual theta stages. -/
def ThetaSourceSignedStageSkewAdjointEnergyCofinallySmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
    thetaSourceSignedStageSkewAdjointEnergy k < ε

/-- Cofinal skew-adjoint source decay forces cofinally small GTA quartic charge. -/
theorem thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_skewAdjointEnergy
    (hskew : ThetaSourceSignedStageSkewAdjointEnergyCofinallySmall) :
    ThetaSourceSchurPositiveQuarticChargeCofinallySmall := by
  intro ε hε N
  let A : ℝ := 575 * thetaSourceSignedHSCeiling ^ 2
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (by norm_num) (sq_pos_of_pos thetaSourceSignedHSCeiling_pos)
  let δ : ℝ := ε / A
  have hδ : 0 < δ := div_pos hε hA
  obtain ⟨k, hkN, hk⟩ := hskew δ hδ N
  let S : ThetaSourceStageSchurPacket k :=
    Classical.choice (nonempty_thetaSourceStageSchurPacket k)
  refine ⟨k, hkN, S, ?_⟩
  have hcharge :=
    thetaSourceStageSchurPositiveQuarticCharge_le_ceiling_mul_skewAdjointEnergy S
  have hstrict :
      A * thetaSourceSignedStageSkewAdjointEnergy k < A * δ :=
    mul_lt_mul_of_pos_left hk hA
  have hδeq : A * δ = ε := by
    dsimp [δ]
    field_simp [hA.ne']
  exact hcharge.trans_lt (hstrict.trans_eq hδeq)

/-- **Source-only GTA endpoint.** Arbitrarily late asymptotic Hermiticity of actual corrected
theta matrices implies RH. -/
theorem riemannHypothesis_of_thetaSourceSignedStageSkewAdjointEnergyCofinallySmall
    (hskew : ThetaSourceSignedStageSkewAdjointEnergyCofinallySmall) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaSourceSchurPositiveQuarticChargeCofinallySmall
    (thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_skewAdjointEnergy hskew)

end

end RHTower.HedenmalmThetaSource
