import GaloisForLFunctions.RHTower.PrimeUHFOperatorKOneContinuity
import GaloisForLFunctions.HTGeometry.CFCSqrtPerturbation
import GaloisForLFunctions.HTGeometry.OperatorNormLoewner
import GaloisForLFunctions.RHTower.FiniteIsometryBoundaryNoGo

/-!
# Finite-stage unitary density in the prime UHF algebra

The algebraic matrix union is dense in its norm completion, but a nearby algebraic element need
not be unitary.  This module performs the missing exact polar correction inside its finite matrix
stage.  A quantitative Gram estimate keeps the correction close, proving that literal finite-stage
unitaries are norm-dense in the unitary group of the completed UHF algebra.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder Ring
open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

theorem norm_unitary_coe_eq_one
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (u : unitary A) : ‖(u : A)‖ = 1 := by
  have hsq : ‖(u : A)‖ * ‖(u : A)‖ = 1 := by
    have h := CStarRing.norm_star_mul_self (x := (u : A))
    rw [u.property.1, norm_one] at h
    exact h.symm
  nlinarith [norm_nonneg (u : A), hsq]

/-- The Gram defect of an element close to a unitary is quadratically controlled. -/
theorem norm_star_mul_self_sub_one_le_of_unitary
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (a : A) (u : unitary A) :
    ‖star a * a - 1‖ ≤ ‖a - (u : A)‖ * (2 + ‖a - (u : A)‖) := by
  have huNorm : ‖(u : A)‖ = 1 := norm_unitary_coe_eq_one u
  have haNorm : ‖a‖ ≤ 1 + ‖a - (u : A)‖ := by
    have h := norm_add_le (a - (u : A)) (u : A)
    rw [sub_add_cancel, huNorm] at h
    simpa [add_comm] using h
  have hsplit : star a * a - 1 =
      star a * (a - (u : A)) + star (a - (u : A)) * (u : A) := by
    rw [mul_sub, star_sub, sub_mul, u.property.1]
    noncomm_ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖star a * (a - (u : A))‖ ≤ ‖a‖ * ‖a - (u : A)‖ := by
    calc
      ‖star a * (a - (u : A))‖ ≤ ‖star a‖ * ‖a - (u : A)‖ := norm_mul_le _ _
      _ = ‖a‖ * ‖a - (u : A)‖ := by rw [norm_star]
  have h2 : ‖star (a - (u : A)) * (u : A)‖ ≤ ‖a - (u : A)‖ := by
    calc
      ‖star (a - (u : A)) * (u : A)‖ ≤
          ‖star (a - (u : A))‖ * ‖(u : A)‖ := norm_mul_le _ _
      _ = ‖a - (u : A)‖ := by rw [norm_star, huNorm, mul_one]
  nlinarith [h1, h2, haNorm, norm_nonneg (a - (u : A))]

/-- Right polar correction of a finite complex matrix. -/
def finiteMatrixPolarFactor {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  A * (CFC.sqrt (star A * A))⁻¹ʳ

/-- A finite matrix with Gram operator in the open unit ball about one has isometric polar
factor. -/
theorem finiteMatrixPolarFactor_isometry {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) {η : ℝ} (hη : η < 1)
    (hgram : ‖star A * A - 1‖ ≤ η) :
    star (finiteMatrixPolarFactor A) * finiteMatrixPolarFactor A = 1 := by
  let b : Matrix (Fin d) (Fin d) ℂ := star A * A
  have hbsa : IsSelfAdjoint b := by
    unfold b IsSelfAdjoint
    rw [star_mul, star_star]
  have hbpos : 0 ≤ b := star_mul_self_nonneg A
  have hbstrict : IsStrictlyPositive b :=
    isStrictlyPositive_of_norm_sub_one_le hbsa hη hgram
  let r : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt b
  have hrstrict : IsStrictlyPositive r := hbstrict.sqrt b
  have hsstrict : IsStrictlyPositive (r⁻¹ʳ) := hrstrict.ringInverse
  have hssa : IsSelfAdjoint (r⁻¹ʳ) := hsstrict.isSelfAdjoint
  have hrr : r * r = b := CFC.sqrt_mul_sqrt_self b hbpos
  change star (A * r⁻¹ʳ) * (A * r⁻¹ʳ) = 1
  rw [star_mul, hssa.star_eq]
  calc
    r⁻¹ʳ * star A * (A * r⁻¹ʳ) = r⁻¹ʳ * b * r⁻¹ʳ := by
      change r⁻¹ʳ * star A * (A * r⁻¹ʳ) = r⁻¹ʳ * (star A * A) * r⁻¹ʳ
      noncomm_ring
    _ = r⁻¹ʳ * (r * r) * r⁻¹ʳ := by rw [hrr]
    _ = (r⁻¹ʳ * r) * (r * r⁻¹ʳ) := by noncomm_ring
    _ = 1 := by rw [Ring.inverse_mul_cancel r hrstrict.isUnit,
      Ring.mul_inverse_cancel r hrstrict.isUnit, one_mul]

/-- The exact finite-stage unitary obtained by polar correction. -/
def finiteMatrixPolarUnitary {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) {η : ℝ} (hη : η < 1)
    (hgram : ‖star A * A - 1‖ ≤ η) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨finiteMatrixPolarFactor A, by
    have hiso := finiteMatrixPolarFactor_isometry A hη hgram
    exact ⟨hiso, RHTower.finiteMatrix_isometry_is_unitary _ hiso⟩⟩

/-- Quantitative polar correction bound in a finite matrix stage. -/
theorem norm_finiteMatrixPolarFactor_sub_self_le {d : ℕ}
    [Nonempty (Fin d)] (A : Matrix (Fin d) (Fin d) ℂ)
    (hgramHalf : ‖star A * A - 1‖ ≤ 1 / 2) :
    ‖finiteMatrixPolarFactor A - A‖ ≤
      2 * ‖A‖ * ‖star A * A - 1‖ := by
  let b : Matrix (Fin d) (Fin d) ℂ := star A * A
  let r : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt b
  let S : Matrix (Fin d) (Fin d) ℂ := r⁻¹ʳ
  have hbsa : IsSelfAdjoint b := by
    unfold b IsSelfAdjoint
    rw [star_mul, star_star]
  have hbpos : 0 ≤ b := star_mul_self_nonneg A
  have hbstrict : IsStrictlyPositive b :=
    isStrictlyPositive_of_norm_sub_one_le hbsa (by norm_num : (1 / 2 : ℝ) < 1) hgramHalf
  have hrstrict : IsStrictlyPositive r := hbstrict.sqrt b
  have hrsa : IsSelfAdjoint r := hrstrict.isSelfAdjoint
  have hrclose : ‖r - 1‖ ≤ ‖b - 1‖ := norm_cfcSqrt_sub_one_le hbpos
  have hrcloseHalf : ‖r - 1‖ ≤ 1 / 2 := hrclose.trans hgramHalf
  have hrlower : (1 / 2 : ℝ) •
      (1 : Matrix (Fin d) (Fin d) ℂ) ≤ r := by
    have h := smul_one_le_of_norm_sub_one_le hrsa hrcloseHalf
    norm_num at h ⊢
    exact h
  have hSnorm : ‖S‖ ≤ 2 := by
    have h := norm_ringInverse_le_of_smul_one_le hrstrict
      (by norm_num : (0 : ℝ) < 1 / 2) hrlower
    norm_num at h
    exact h
  have hSclose : ‖S - 1‖ ≤ 2 * ‖b - 1‖ := by
    have h := norm_ringInverse_sub_one_le hrstrict
    change ‖S - 1‖ ≤ ‖S‖ * ‖r - 1‖ at h
    calc
      ‖S - 1‖ ≤ ‖S‖ * ‖r - 1‖ := h
      _ ≤ 2 * ‖r - 1‖ :=
        mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _)
      _ ≤ 2 * ‖b - 1‖ := by linarith
  have hsplit : finiteMatrixPolarFactor A - A = A * (S - 1) := by
    unfold finiteMatrixPolarFactor S r b
    noncomm_ring
  rw [hsplit]
  calc
    ‖A * (S - 1)‖ ≤ ‖A‖ * ‖S - 1‖ := norm_mul_le _ _
    _ ≤ ‖A‖ * (2 * ‖b - 1‖) :=
      mul_le_mul_of_nonneg_left hSclose (norm_nonneg _)
    _ = 2 * ‖A‖ * ‖star A * A - 1‖ := by
      change ‖A‖ * (2 * ‖star A * A - 1‖) = _
      ring

/-- Literal finite-stage unitaries are norm-dense in the unitary group of the completed UHF
algebra. -/
theorem exists_matrixAFStageUnitary_norm_sub_lt
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (U : unitary (PrimeUHFAlgebra localDim)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (i : ℕ)
      (V : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ),
      ‖(matrixAFStageUnitaryToUHF i V : PrimeUHFAlgebra localDim) -
          (U : PrimeUHFAlgebra localDim)‖ < ε := by
  let ρ : ℝ := min (1 / 16 : ℝ) (ε / 8)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  obtain ⟨q, hq⟩ :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt
      (U : PrimeUHFAlgebra localDim) hρ
  have hq' : ‖(q : PrimeUHFAlgebra localDim) -
      (U : PrimeUHFAlgebra localDim)‖ < ρ := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using hq
  induction q using DirectLimit.induction with
  | ih i A =>
      let a : PrimeUHFAlgebra localDim := matrixAFStageToUHF i A
      let δ : ℝ := ‖a - (U : PrimeUHFAlgebra localDim)‖
      have ha : a = (↑(⟦⟨i, A⟩⟧ : PrimeAFAlgebraicLimit localDim) :
          PrimeUHFAlgebra localDim) := rfl
      have hδρ : δ < ρ := by simpa [δ, a, ha] using hq'
      have hδ0 : 0 ≤ δ := norm_nonneg _
      have hρSixteen : ρ ≤ 1 / 16 := min_le_left _ _
      have hρEps : ρ ≤ ε / 8 := min_le_right _ _
      have hδSixteen : δ ≤ 1 / 16 := le_trans hδρ.le hρSixteen
      have hδEps : δ < ε / 8 := lt_of_lt_of_le hδρ hρEps
      have hgram : ‖star A * A - 1‖ ≤ δ * (2 + δ) := by
        calc
          ‖star A * A - 1‖ =
              ‖matrixAFStageToUHF i (star A * A - 1)‖ :=
                (norm_matrixAFStageToUHF i _).symm
          _ = ‖star a * a - 1‖ := by
            simp only [map_sub, map_mul, map_star, map_one, a]
          _ ≤ δ * (2 + δ) :=
            norm_star_mul_self_sub_one_le_of_unitary a U
      have hgramHalf : ‖star A * A - 1‖ ≤ 1 / 2 := by
        have hgramNonneg : 0 ≤ ‖star A * A - 1‖ := norm_nonneg _
        nlinarith
      letI : Nonempty (Fin (matrixAFStageDimension localDim i)) :=
        Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out i)
      let V : Matrix.unitaryGroup
          (Fin (matrixAFStageDimension localDim i)) ℂ :=
        finiteMatrixPolarUnitary A (η := (1 / 2 : ℝ)) (by norm_num) hgramHalf
      refine ⟨i, V, ?_⟩
      have hcorrStage : ‖finiteMatrixPolarFactor A - A‖ ≤
          2 * ‖A‖ * ‖star A * A - 1‖ :=
        norm_finiteMatrixPolarFactor_sub_self_le A hgramHalf
      have hcorr : ‖matrixAFStageToUHF i (finiteMatrixPolarFactor A) - a‖ ≤
          2 * ‖A‖ * ‖star A * A - 1‖ := by
        change ‖matrixAFStageToUHF i (finiteMatrixPolarFactor A) -
            matrixAFStageToUHF i A‖ ≤ _
        rw [← map_sub, norm_matrixAFStageToUHF]
        exact hcorrStage
      have hUnorm : ‖(U : PrimeUHFAlgebra localDim)‖ = 1 :=
        norm_unitary_coe_eq_one U
      have haNorm : ‖A‖ ≤ 1 + δ := by
        rw [← norm_matrixAFStageToUHF i A]
        change ‖a‖ ≤ 1 + δ
        calc
          ‖a‖ = ‖(a - (U : PrimeUHFAlgebra localDim)) +
              (U : PrimeUHFAlgebra localDim)‖ := by rw [sub_add_cancel]
          _ ≤ ‖a - (U : PrimeUHFAlgebra localDim)‖ +
              ‖(U : PrimeUHFAlgebra localDim)‖ := norm_add_le _ _
          _ = δ + 1 := by rw [hUnorm]
          _ = 1 + δ := add_comm _ _
      have htarget : ‖matrixAFStageToUHF i (finiteMatrixPolarFactor A) -
          (U : PrimeUHFAlgebra localDim)‖ ≤
          2 * ‖A‖ * ‖star A * A - 1‖ + δ := by
        have htri := norm_add_le
          (matrixAFStageToUHF i (finiteMatrixPolarFactor A) - a)
          (a - (U : PrimeUHFAlgebra localDim))
        have hsplit : matrixAFStageToUHF i (finiteMatrixPolarFactor A) -
            (U : PrimeUHFAlgebra localDim) =
            (matrixAFStageToUHF i (finiteMatrixPolarFactor A) - a) +
              (a - (U : PrimeUHFAlgebra localDim)) := by abel
        rw [← hsplit] at htri
        exact htri.trans (add_le_add hcorr le_rfl)
      have hbound : 2 * ‖A‖ * ‖star A * A - 1‖ + δ ≤ 8 * δ := by
        have hg0 : 0 ≤ ‖star A * A - 1‖ := norm_nonneg _
        have hfirst : 2 * ‖A‖ * ‖star A * A - 1‖ ≤
            2 * (1 + δ) * ‖star A * A - 1‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left haNorm (by norm_num)) hg0
        have hsecond : 2 * (1 + δ) * ‖star A * A - 1‖ ≤
            2 * (1 + δ) * (δ * (2 + δ)) := by
          exact mul_le_mul_of_nonneg_left hgram (by positivity)
        calc
          2 * ‖A‖ * ‖star A * A - 1‖ + δ ≤
              2 * (1 + δ) * ‖star A * A - 1‖ + δ :=
            add_le_add hfirst le_rfl
          _ ≤ 2 * (1 + δ) * (δ * (2 + δ)) + δ :=
            add_le_add hsecond le_rfl
          _ ≤ 8 * δ := by nlinarith
      change ‖matrixAFStageToUHF i (finiteMatrixPolarFactor A) -
          (U : PrimeUHFAlgebra localDim)‖ < ε
      exact lt_of_le_of_lt (htarget.trans hbound) (by linarith)

end

end PrimeQuasiLocalCharge
