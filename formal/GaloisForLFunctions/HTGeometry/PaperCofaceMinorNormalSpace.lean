import GaloisForLFunctions.HTGeometry.PaperCofaceNormalSpace
import GaloisForLFunctions.HTGeometry.MonomialSubstitution

/-!
# Independent normal directions from the actual coface boundary determinants

The native boundary minors differ from the coface monomials only by explicit
unit signs. Transport their characteristic-free independence through the
existing monomial substitution automorphism and the paper's Rees kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

variable (K : Type*) [Field K]

/-- Substitution by the actual maximal minors of the native weighted boundary matrix. -/
def paperCofaceBoundaryMinorSubstitution (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1)) K :=
  MvPolynomial.aeval (cofaceBoundaryMaximalMinor (F := K) (r + 1))

/-- The determinant signs give an existing polynomial coordinate automorphism. -/
theorem paperCofaceBoundaryMinorSubstitution_eq_comp (r : ℕ) :
    paperCofaceBoundaryMinorSubstitution K r =
      (paperCofaceSubstitution K r).comp
        (monomialSub (fun i : Fin (r + 1 + 1) => if i = 0 then (1 : K) else -1) (Equiv.refl _)) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [paperCofaceBoundaryMinorSubstitution, cofaceBoundaryMaximalMinor_zero,
      monomialSub_X, paperCofaceSubstitution]
  · simp [paperCofaceBoundaryMinorSubstitution, cofaceBoundaryMaximalMinor_succ,
      monomialSub_X, paperCofaceSubstitution]

/-- The actual boundary determinants satisfy no scalar polynomial relation. -/
theorem paperCofaceBoundaryMinorSubstitution_injective (r : ℕ) :
    Function.Injective (paperCofaceBoundaryMinorSubstitution K r) := by
  rw [paperCofaceBoundaryMinorSubstitution_eq_comp]
  exact (paperCofaceSubstitution_injective K r).comp
    (monomialSub_injective (fun i => by split_ifs <;> simp) (Equiv.refl _))

/-- Each actual maximal minor has the common degree, including its native sign. -/
theorem paperCofaceBoundaryMinor_homogeneous (r : ℕ) (i : Fin (r + 1 + 1)) :
    (cofaceBoundaryMaximalMinor (F := K) (r + 1) i).IsHomogeneous (r + 1) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [cofaceBoundaryMaximalMinor_zero]
    exact paperCofaceMonomial_homogeneous K r 0
  · rw [cofaceBoundaryMaximalMinor_succ]
    exact (paperCofaceMonomial_homogeneous K r j.succ).neg

/-- All normal-family data for the actual boundary matrix determinants. -/
def paperCofaceBoundaryMinorNormalFamilyData (r : ℕ) :
    PaperHomogeneousNormalFamilyData K (Fin (r + 1 + 1)) (Fin (r + 1 + 1))
      (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) where
  generator := cofaceBoundaryMaximalMinor (r + 1)
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem i := Ideal.subset_span ⟨i, rfl⟩
  homogeneous := paperCofaceBoundaryMinor_homogeneous K r
  independent := paperCofaceBoundaryMinorSubstitution_injective K r
  order_bound := by
    rw [cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal]
    exact paperVeroneseIdeal_weightOrder K _ _

/-- Polynomial coordinates given by all native boundary determinant initial classes. -/
def paperCofaceBoundaryMinorNormalSpaceMap (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →+*
      PaperIdealAssociatedGraded (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) :=
  (paperCofaceBoundaryMinorNormalFamilyData K r).polynomialMap

/-- All native boundary determinant initial classes remain polynomially independent. -/
theorem paperCofaceBoundaryMinorNormalSpaceMap_injective (r : ℕ) :
    Function.Injective (paperCofaceBoundaryMinorNormalSpaceMap K r) :=
  (paperCofaceBoundaryMinorNormalFamilyData K r).polynomialMap_injective

/-- The map sends each variable to the initial class of the corresponding actual matrix minor. -/
theorem paperCofaceBoundaryMinorNormalSpaceMap_X (r : ℕ) (i : Fin (r + 1 + 1)) :
    paperCofaceBoundaryMinorNormalSpaceMap K r (MvPolynomial.X i) =
      paperNativeReesSpecialization (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1))
        (ReesGrading.mono _ 1 (cofaceBoundaryMaximalMinor (F := K) (r + 1) i)
          (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)) :=
  (paperCofaceBoundaryMinorNormalFamilyData K r).polynomialMap_X i

end

end GaloisForLFunctions.HTGeometry
