import GaloisForLFunctions.HTGeometry.PaperCofaceExponentEmbedding
import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalFamily
import GaloisForLFunctions.HTGeometry.PaperNormalCrossingNormalLine

/-!
# A full polynomial normal space for native normal crossings

All gradient components of the coordinate product retain simultaneous
polynomial independence in the associated graded ring of its Jacobian ideal.
The result holds over every field, including characteristics dividing the
common degree. The same generators give a polynomial normal space for the
native coface boundary minor ideal and its squarefree Veronese presentation.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

variable (K : Type*) [Field K]

/-- Every prerequisite for the full coface normal family is proved for the native Jacobian ideal. -/
def paperNormalCrossingNormalFamilyData (r : ℕ) :
    PaperHomogeneousNormalFamilyData K (Fin (r + 1 + 1)) (Fin (r + 1 + 1))
      (normalCrossingJacobianIdeal (F := K) (r + 1)) where
  generator := cofaceMonomial (r + 1)
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem i := by
    rw [← pderiv_normalCrossingPolynomial]
    exact Ideal.subset_span ⟨i, rfl⟩
  homogeneous := paperCofaceMonomial_homogeneous K r
  independent := paperCofaceSubstitution_injective K r
  order_bound := by
    rw [normalCrossingJacobianIdeal_eq_veroneseIdeal]
    exact paperVeroneseIdeal_weightOrder K _ _

/-- Simultaneous substitution into every gradient initial class. -/
def paperNormalCrossingNormalSpaceMap (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →+*
      PaperIdealAssociatedGraded (normalCrossingJacobianIdeal (F := K) (r + 1)) :=
  (paperNormalCrossingNormalFamilyData K r).polynomialMap

/-- No scalar polynomial relation between the actual gradient initial classes survives. -/
theorem paperNormalCrossingNormalSpaceMap_eq_zero_iff (r : ℕ)
    (p : MvPolynomial (Fin (r + 1 + 1)) K) :
    paperNormalCrossingNormalSpaceMap K r p = 0 ↔ p = 0 :=
  (paperNormalCrossingNormalFamilyData K r).polynomialMap_eq_zero_iff p

/-- The actual normal-crossing associated graded ring contains a polynomial ring in all variables. -/
theorem paperNormalCrossingNormalSpaceMap_injective (r : ℕ) :
    Function.Injective (paperNormalCrossingNormalSpaceMap K r) :=
  (paperNormalCrossingNormalFamilyData K r).polynomialMap_injective

/-- The coordinate indexed by `i` is exactly the initial class of the `i`th gradient component. -/
theorem paperNormalCrossingNormalSpaceMap_X (r : ℕ) (i : Fin (r + 1 + 1)) :
    paperNormalCrossingNormalSpaceMap K r (MvPolynomial.X i) =
      paperNativeReesSpecialization (normalCrossingJacobianIdeal (F := K) (r + 1))
        (ReesGrading.mono _ 1 (pderiv i (normalCrossingPolynomial (F := K) (r + 1)))
          (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)) := by
  simpa only [paperNormalCrossingNormalSpaceMap, paperNormalCrossingNormalFamilyData,
    pderiv_normalCrossingPolynomial] using
    (paperNormalCrossingNormalFamilyData K r).polynomialMap_X i

/-- Transport the paid normal family to the actual native coface boundary minor ideal. -/
def paperCofaceBoundaryNormalFamilyData (r : ℕ) :
    PaperHomogeneousNormalFamilyData K (Fin (r + 1 + 1)) (Fin (r + 1 + 1))
      (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) := by
  rw [cofaceBoundaryMaximalMinorIdeal_eq_normalCrossingJacobianIdeal]
  exact paperNormalCrossingNormalFamilyData K r

/-- All coface coordinates in the boundary minor associated graded ring. -/
def paperCofaceBoundaryNormalSpaceMap (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →+*
      PaperIdealAssociatedGraded (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) :=
  (paperCofaceBoundaryNormalFamilyData K r).polynomialMap

/-- Boundary minor geometry retains a full polynomial family of coface directions. -/
theorem paperCofaceBoundaryNormalSpaceMap_injective (r : ℕ) :
    Function.Injective (paperCofaceBoundaryNormalSpaceMap K r) :=
  (paperCofaceBoundaryNormalFamilyData K r).polynomialMap_injective

/-- The same paid family in the native squarefree Veronese presentation. -/
def paperCofaceVeroneseNormalFamilyData (r : ℕ) :
    PaperHomogeneousNormalFamilyData K (Fin (r + 1 + 1)) (Fin (r + 1 + 1))
      (veroneseIdeal K (Fin (r + 1 + 1)) (r + 1)) := by
  rw [← normalCrossingJacobianIdeal_eq_veroneseIdeal]
  exact paperNormalCrossingNormalFamilyData K r

/-- All complementary-face directions in the squarefree Veronese associated graded ring. -/
def paperCofaceVeroneseNormalSpaceMap (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →+*
      PaperIdealAssociatedGraded (veroneseIdeal K (Fin (r + 1 + 1)) (r + 1)) :=
  (paperCofaceVeroneseNormalFamilyData K r).polynomialMap

/-- The native coface Veronese ideal retains a polynomial normal space in every dimension. -/
theorem paperCofaceVeroneseNormalSpaceMap_injective (r : ℕ) :
    Function.Injective (paperCofaceVeroneseNormalSpaceMap K r) :=
  (paperCofaceVeroneseNormalFamilyData K r).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
