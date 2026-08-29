import GaloisForLFunctions.HTGeometry.LinearHallTransversal
import GaloisForLFunctions.HTGeometry.CompactDetectorNearRadicalAlternative
import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone

/-!
# Hall determinant certificates for finite Kraus families

Linear Hall expansion permits one independent image from every column of every unitary frame.
Summing the squared determinants of all such colored column selections gives a continuous,
strictly positive certificate on the compact unitary group, hence a uniform positive margin.
This is the finite-dimensional determinant-capacity input for matrix Dyson boundary analysis.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d κ : Type*} [Fintype d] [DecidableEq d] [Fintype κ] [DecidableEq κ]

/-- The columns of a unitary matrix, packaged as a basis of coordinate space. -/
def unitaryColumnBasis (U : Matrix.unitaryGroup d ℂ) : Module.Basis d ℂ (d → ℂ) := by
  have hleft : (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 :=
    (Unitary.mem_iff.mp U.property).1
  have hdet : (U : Matrix d d ℂ).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse hleft
  have hunit : IsUnit (U : Matrix d d ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).2 ((isUnit_iff_ne_zero).2 hdet)
  have hli : LinearIndependent ℂ (U : Matrix d d ℂ).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  apply Module.Basis.mk hli
  let S : Submodule ℂ (d → ℂ) :=
    Submodule.span ℂ (Set.range (U : Matrix d d ℂ).col)
  have hfin : Module.finrank ℂ S = Fintype.card d := by
    simpa [S] using finrank_span_eq_card hli
  have htop : S = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hfin)
  simpa [S] using le_of_eq htop.symm

theorem unitaryColumnBasis_apply (U : Matrix.unitaryGroup d ℂ) (j : d) :
    unitaryColumnBasis U j = fun i ↦ (U : Matrix d d ℂ) i j := by
  simp only [unitaryColumnBasis]
  change (U : Matrix d d ℂ).col j = _
  rfl

/-- Matrix whose `j`th column applies the color `k j` to the `j`th column of `U`. -/
def hallSelectedColumnMatrix (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ)
    (k : d → κ) : Matrix d d ℂ :=
  fun i j ↦ (A (k j) * U) i j

theorem hallSelectedColumnMatrix_col (A : κ → Matrix d d ℂ)
    (U : Matrix d d ℂ) (k : d → κ) (j : d) :
    (hallSelectedColumnMatrix A U k).col j =
      (A (k j)).mulVec (fun i ↦ U i j) := by
  ext i
  simp only [hallSelectedColumnMatrix, Matrix.col_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]

/-- Every unitary frame has a colored Hall selection with nonzero determinant. -/
theorem exists_hallSelectedColumnMatrix_det_ne_zero
    (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin)
    (U : Matrix.unitaryGroup d ℂ) :
    ∃ k : d → κ, (hallSelectedColumnMatrix A U k).det ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_linearIndependent_image_choice_of_hall
    (fun k ↦ (A k).mulVecLin) hHall (unitaryColumnBasis U)
  refine ⟨k, ?_⟩
  have hcols : LinearIndependent ℂ (hallSelectedColumnMatrix A U k).col := by
    have hk' : LinearIndependent ℂ
        (fun j ↦ (A (k j)).mulVec (fun i ↦ (U : Matrix d d ℂ) i j)) := by
      simpa only [unitaryColumnBasis_apply, Matrix.mulVecLin_apply] using hk
    simpa only [hallSelectedColumnMatrix_col] using hk'
  have hunit : IsUnit (hallSelectedColumnMatrix A U k) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit))

/-- Sum of squared determinant certificates over every colored column selection. -/
def hallDeterminantCertificate (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ) : ℝ :=
  ∑ k : d → κ, Complex.normSq (hallSelectedColumnMatrix A U k).det

theorem hallDeterminantCertificate_nonneg (A : κ → Matrix d d ℂ)
    (U : Matrix d d ℂ) :
    0 ≤ hallDeterminantCertificate A U :=
  Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem hallDeterminantCertificate_pos_of_unitary
    (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin)
    (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    0 < hallDeterminantCertificate A U := by
  obtain ⟨k, hk⟩ := exists_hallSelectedColumnMatrix_det_ne_zero A hHall ⟨U, hU⟩
  exact Finset.sum_pos'
    (fun q _ ↦ Complex.normSq_nonneg (hallSelectedColumnMatrix A U q).det)
    ⟨k, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

theorem continuous_hallDeterminantCertificate (A : κ → Matrix d d ℂ) :
    Continuous (hallDeterminantCertificate A) := by
  unfold hallDeterminantCertificate hallSelectedColumnMatrix
  fun_prop

/-- Compactness upgrades pointwise Hall selections to one uniform positive determinant margin. -/
theorem exists_pos_le_hallDeterminantCertificate
    [Nonempty d] (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin) :
    ∃ c : ℝ, 0 < c ∧ ∀ U : Matrix d d ℂ,
      U ∈ Matrix.unitaryGroup d ℂ → c ≤ hallDeterminantCertificate A U := by
  have hcompact : IsCompact (Matrix.unitaryGroup d ℂ : Set (Matrix d d ℂ)) := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun U hU ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (CStarRing.norm_of_mem_unitary hU).le
  apply exists_pos_compactMargin hcompact
  · exact ⟨1, by simp⟩
  · exact (continuous_hallDeterminantCertificate A).continuousOn
  · exact hallDeterminantCertificate_pos_of_unitary A hHall

end

end GaloisForLFunctions.HTGeometry
