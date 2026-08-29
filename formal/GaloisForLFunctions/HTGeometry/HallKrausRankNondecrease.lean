import GaloisForLFunctions.HTGeometry.HallKrausDeterminantCapacity
import GaloisForLFunctions.HTGeometry.MatrixLoewnerRankMonotone

/-!
# Hall rank nondecrease for positive Kraus inputs

The finite Rado selector can be applied to an eigenbasis of a singular positive-semidefinite
matrix.  Its selected congruence has the same rank as the input and is Loewner-dominated by the
full Kraus sum.  Rank monotonicity therefore extends the Hall condition from subspaces to every
positive-semidefinite matrix input.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d κ : Type*} [Fintype d] [DecidableEq d]
  [Fintype κ] [DecidableEq κ]

/-- A Hall Kraus family cannot decrease rank on the positive cone. -/
theorem rank_le_rank_krausSum_of_hall
    (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k => (A k).mulVecLin)
    {M : Matrix d d ℂ} (hM : M.PosSemidef) :
    M.rank ≤ (∑ q, A q * M * (A q)ᴴ).rank := by
  let U : Matrix d d ℂ := hM.isHermitian.eigenvectorUnitary
  let lam : d → ℝ := hM.isHermitian.eigenvalues
  let D : Matrix d d ℂ := diagonal fun j => (lam j : ℂ)
  have hUmem : U ∈ Matrix.unitaryGroup d ℂ := by
    simp [U]
  obtain ⟨k, hk⟩ := exists_hallSelectedColumnMatrix_det_ne_zero A hHall ⟨U, hUmem⟩
  let C : Matrix d d ℂ := hallSelectedColumnMatrix A U k
  have hCunit : IsUnit C := by
    apply C.isUnit_iff_isUnit_det.mpr
    exact isUnit_iff_ne_zero.mpr (by simpa [C] using hk)
  have hUunit : IsUnit U := by
    refine ⟨⟨U, Uᴴ, ?_, ?_⟩, rfl⟩
    · exact (Unitary.mem_iff.mp hUmem).2
    · exact (Unitary.mem_iff.mp hUmem).1
  have hlam : ∀ j, 0 ≤ lam j := fun j => hM.eigenvalues_nonneg j
  have hspec : M = U * D * Uᴴ := by
    simpa [U, D, lam, Matrix.star_eq_conjTranspose] using
      isHermitian_eq_conj_diagonal hM.isHermitian
  have htotal :
      (∑ q, A q * M * (A q)ᴴ) =
        ∑ q, (A q * U) * D * (A q * U)ᴴ := by
    rw [hspec]
    apply Finset.sum_congr rfl
    intro q _hq
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hselected : (C * D * Cᴴ).PosSemidef := by
    simpa [C, D] using
      hallSelected_diagonal_congruence_posSemidef A U lam hlam k
  have hdiff :
      ((∑ q, A q * M * (A q)ᴴ) - C * D * Cᴴ).PosSemidef := by
    rw [htotal]
    simpa [C, D] using
      kraus_diagonal_sum_sub_hallSelected_posSemidef A U lam hlam k
  have hrank := rank_le_rank_of_posSemidef_sub hselected hdiff
  calc
    M.rank = (U * D * Uᴴ).rank := congrArg Matrix.rank hspec
    _ = D.rank := rank_mul_mul_conjTranspose_eq_of_isUnit U D hUunit
    _ = (C * D * Cᴴ).rank :=
      (rank_mul_mul_conjTranspose_eq_of_isUnit C D hCunit).symm
    _ ≤ (∑ q, A q * M * (A q)ᴴ).rank := hrank

end

end GaloisForLFunctions.HTGeometry
