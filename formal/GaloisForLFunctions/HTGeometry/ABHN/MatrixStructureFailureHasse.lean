import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSymmetry
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixDiagonal
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixAdjoints
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixTriangular
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixIsometries
import GaloisForLFunctions.HTGeometry.ABHN.HasseClassicalMatrixGroups
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixCharpolySeparable

/-!
# Matrix-structure defects at every completion

Faithful scalar extension reflects matrix symmetry, diagonal and orthogonality conditions,
adjoint relations, block flags, bilinear-form preservation, classical-group membership,
invertibility, and characteristic-polynomial separability.  Their failures are therefore visible
at every global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w x

/-- Nonsymmetry of a number-field matrix persists at every completion. -/
theorem numberFieldMatrix_not_isSymm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    ¬ M.IsSymm ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).IsSymm :=
  not_iff_forall_not_of_iff_exists (numberFieldMatrix_isSymm_iff_exists_place K n M)

/-- Nonsymmetry of a function-field matrix persists at every completion. -/
theorem rationalFunctionMatrix_not_isSymm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    ¬ M.IsSymm ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsSymm :=
  not_iff_forall_not_of_iff_exists (rationalFunctionMatrix_isSymm_iff_exists_place F n M)

/-- Nondiagonality of a number-field matrix persists at every completion. -/
theorem numberFieldMatrix_not_isDiag_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) (M : Matrix n n K) :
    ¬ M.IsDiag ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).IsDiag :=
  not_iff_forall_not_of_iff_exists (numberFieldMatrix_isDiag_iff_exists_place K n M)

/-- Nondiagonality of a function-field matrix persists at every completion. -/
theorem rationalFunctionMatrix_not_isDiag_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) (M : Matrix n n (RatFunc F)) :
    ¬ M.IsDiag ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsDiag :=
  not_iff_forall_not_of_iff_exists (rationalFunctionMatrix_isDiag_iff_exists_place F n M)

/-- Failure of row orthogonality over a number field persists at every completion. -/
theorem numberFieldMatrix_not_hasOrthogonalRows_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n K) :
    ¬ M.HasOrthogonalRows ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).HasOrthogonalRows :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_hasOrthogonalRows_iff_exists_place K M)

/-- Failure of row orthogonality over `F(t)` persists at every completion. -/
theorem rationalFunctionMatrix_not_hasOrthogonalRows_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype n]
    (M : Matrix m n (RatFunc F)) :
    ¬ M.HasOrthogonalRows ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalRows :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_hasOrthogonalRows_iff_exists_place F M)

/-- Failure of column orthogonality over a number field persists at every completion. -/
theorem numberFieldMatrix_not_hasOrthogonalCols_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n K) :
    ¬ M.HasOrthogonalCols ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).HasOrthogonalCols :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_hasOrthogonalCols_iff_exists_place K M)

/-- Failure of column orthogonality over `F(t)` persists at every completion. -/
theorem rationalFunctionMatrix_not_hasOrthogonalCols_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x} [Fintype m]
    (M : Matrix m n (RatFunc F)) :
    ¬ M.HasOrthogonalCols ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).HasOrthogonalCols :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_hasOrthogonalCols_iff_exists_place F M)

/-- Failure of a number-field adjoint-pair relation persists at every completion. -/
theorem numberFieldMatrix_not_isAdjointPair_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {m : Type w} {n : Type x}
    [Fintype m] [Fintype n]
    (J : Matrix n n K) (J' : Matrix m m K) (A : Matrix m n K) (A' : Matrix n m K) :
    ¬ Matrix.IsAdjointPair J J' A A' ↔ ∀ p : NumberFieldPlace K,
      ¬ Matrix.IsAdjointPair (J.map (algebraMap K (completion K p)))
        (J'.map (algebraMap K (completion K p))) (A.map (algebraMap K (completion K p)))
        (A'.map (algebraMap K (completion K p))) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_isAdjointPair_iff_exists_place K J J' A A')

/-- Failure of a function-field adjoint-pair relation persists at every completion. -/
theorem rationalFunctionMatrix_not_isAdjointPair_iff_forall_place
    (F : Type u) [Field F] [Finite F] {m : Type w} {n : Type x}
    [Fintype m] [Fintype n]
    (J : Matrix n n (RatFunc F)) (J' : Matrix m m (RatFunc F))
    (A : Matrix m n (RatFunc F)) (A' : Matrix n m (RatFunc F)) :
    ¬ Matrix.IsAdjointPair J J' A A' ↔ ∀ p : RationalFunctionPlace F,
      ¬ Matrix.IsAdjointPair
        (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (J'.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (A'.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_isAdjointPair_iff_exists_place F J J' A A')

/-- Failure of relative self-adjointness over a number field persists at every completion. -/
theorem numberFieldMatrix_not_isSelfAdjoint_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n]
    (J A : Matrix n n K) :
    ¬ J.IsSelfAdjoint A ↔ ∀ p : NumberFieldPlace K,
      ¬ (J.map (algebraMap K (completion K p))).IsSelfAdjoint
        (A.map (algebraMap K (completion K p))) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_isSelfAdjoint_iff_exists_place K n J A)

/-- Failure of relative self-adjointness over `F(t)` persists at every completion. -/
theorem rationalFunctionMatrix_not_isSelfAdjoint_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n]
    (J A : Matrix n n (RatFunc F)) :
    ¬ J.IsSelfAdjoint A ↔ ∀ p : RationalFunctionPlace F,
      ¬ (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).IsSelfAdjoint
        (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_isSelfAdjoint_iff_exists_place F n J A)

/-- Failure to preserve a number-field block flag persists at every completion. -/
theorem numberFieldMatrix_not_blockTriangular_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    {ι : Type x} [LT ι] (M : Matrix n n K) (b : n → ι) :
    ¬ M.BlockTriangular b ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).BlockTriangular b :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_blockTriangular_iff_exists_place K n M b)

/-- Failure to preserve a function-field block flag persists at every completion. -/
theorem rationalFunctionMatrix_not_blockTriangular_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    {ι : Type x} [LT ι] (M : Matrix n n (RatFunc F)) (b : n → ι) :
    ¬ M.BlockTriangular b ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).BlockTriangular b :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_blockTriangular_iff_exists_place F n M b)

/-- Failure to preserve a number-field form persists at every completion. -/
theorem numberFieldMatrix_not_preservesForm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J * M ≠ J ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) *
          M.map (algebraMap K (completion K p)) ≠ J.map (algebraMap K (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_preservesForm_iff_exists_place K n J M)

/-- Failure to preserve a function-field form persists at every completion. -/
theorem rationalFunctionMatrix_not_preservesForm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J * M ≠ J ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
          M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ≠
            J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_preservesForm_iff_exists_place F n J M)

/-- Failure of infinitesimal form preservation over a number field persists everywhere. -/
theorem numberFieldMatrix_not_infinitesimallyPreservesForm_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n K) :
    M.transpose * J + J * M ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).transpose *
          (J.map (algebraMap K (completion K p))) +
          (J.map (algebraMap K (completion K p))) *
            M.map (algebraMap K (completion K p)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_infinitesimallyPreservesForm_iff_exists_place K n J M)

/-- Failure of infinitesimal form preservation over `F(t)` persists everywhere. -/
theorem rationalFunctionMatrix_not_infinitesimallyPreservesForm_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (J M : Matrix n n (RatFunc F)) :
    M.transpose * J + J * M ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).transpose *
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) +
          (J.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) *
            M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_infinitesimallyPreservesForm_iff_exists_place F n J M)

/-- Failure of number-field orthogonal-group membership persists at every completion. -/
theorem numberFieldMatrix_not_mem_orthogonalGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∉ Matrix.orthogonalGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∉ Matrix.orthogonalGroup n (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_mem_orthogonalGroup_iff_exists_place K n M)

/-- Failure of function-field orthogonal-group membership persists at every completion. -/
theorem rationalFunctionMatrix_not_mem_orthogonalGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M ∉ Matrix.orthogonalGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∉
        Matrix.orthogonalGroup n (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_mem_orthogonalGroup_iff_exists_place F n M)

/-- Failure of number-field special-orthogonal membership persists at every completion. -/
theorem numberFieldMatrix_not_mem_specialOrthogonalGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M ∉ Matrix.specialOrthogonalGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∉ Matrix.specialOrthogonalGroup n (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_mem_specialOrthogonalGroup_iff_exists_place K n M)

/-- Failure of function-field special-orthogonal membership persists at every completion. -/
theorem rationalFunctionMatrix_not_mem_specialOrthogonalGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M ∉ Matrix.specialOrthogonalGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∉
        Matrix.specialOrthogonalGroup n (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_mem_specialOrthogonalGroup_iff_exists_place F n M)

/-- Failure of number-field symplectic-group membership persists at every completion. -/
theorem numberFieldMatrix_not_mem_symplecticGroup_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ n) (n ⊕ n) K) :
    M ∉ Matrix.symplecticGroup n K ↔ ∀ p : NumberFieldPlace K,
      M.map (algebraMap K (completion K p)) ∉ Matrix.symplecticGroup n (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_mem_symplecticGroup_iff_exists_place K n M)

/-- Failure of function-field symplectic-group membership persists at every completion. -/
theorem rationalFunctionMatrix_not_mem_symplecticGroup_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ n) (n ⊕ n) (RatFunc F)) :
    M ∉ Matrix.symplecticGroup n (RatFunc F) ↔ ∀ p : RationalFunctionPlace F,
      M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) ∉
        Matrix.symplecticGroup n (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_mem_symplecticGroup_iff_exists_place F n M)

/-- Noninvertibility of a number-field matrix persists at every completion. -/
theorem numberFieldMatrix_not_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    ¬ IsUnit M ↔ ∀ v : NumberFieldPlace K, ¬ IsUnit (M.map (placeEmbedding K v)) :=
  not_iff_forall_not_of_iff_exists (numberFieldMatrix_isUnit_iff_exists_place K n M)

/-- Noninvertibility of a function-field matrix persists at every completion. -/
theorem rationalFunctionMatrix_not_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    ¬ IsUnit M ↔ ∀ v : RationalFunctionPlace F,
      ¬ IsUnit (M.map (rationalFunctionPlaceEmbedding F v)) :=
  not_iff_forall_not_of_iff_exists (rationalFunctionMatrix_isUnit_iff_exists_place F n M)

/-- Inseparability of a number-field matrix characteristic polynomial persists everywhere. -/
theorem numberFieldMatrix_charpoly_not_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    ¬ M.charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      ¬ (M.map (algebraMap K (completion K p))).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_charpoly_separable_iff_exists_place K n M)

/-- Inseparability of a function-field matrix characteristic polynomial persists everywhere. -/
theorem rationalFunctionMatrix_charpoly_not_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    ¬ M.charpoly.Separable ↔ ∀ p : RationalFunctionPlace F,
      ¬ (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).charpoly.Separable :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_charpoly_separable_iff_exists_place F n M)

end GaloisForLFunctions.HTGeometry.ABHN
