import GaloisForLFunctions.HTGeometry.PaperVeroneseIndependentFaces
import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalFamily
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Full polynomial normal spaces for squarefree Veronese ideals

For degree `r + 1` in `r + 2 + extra` variables, explicitly choose as many
squarefree generators as ambient variables. Their exponent map is injective.
The source Rees coefficient kernel and nonnegative-weight theorem then retain
their independence in the actual native Veronese associated graded ring.
All assertions hold over arbitrary commutative coefficient rings.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

/-- The chosen independent faces in the native numbered ambient variables. -/
def paperVeroneseFullNormalFace (r extra : ℕ) (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    Finset (Fin (r + 1 + 1 + extra)) :=
  (paperVeroneseIndependentFace r extra i).image finSumFinEquiv

/-- Renumbering preserves the size of every chosen squarefree face. -/
theorem paperVeroneseFullNormalFace_card (r extra : ℕ) (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    (paperVeroneseFullNormalFace r extra i).card = r + 1 := by
  rw [paperVeroneseFullNormalFace, Finset.card_image_of_injective _ finSumFinEquiv.injective,
    paperVeroneseIndependentFace_card]

variable (K : Type*) [CommRing K]

/-- Explicit native squarefree generators of the Veronese ideal. -/
def paperVeroneseFullNormalGenerator (r extra : ℕ) (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    MvPolynomial (Fin (r + 1 + 1 + extra)) K :=
  ∏ j ∈ paperVeroneseFullNormalFace r extra i, MvPolynomial.X j

/-- These are the same independent monomials after numbering the variables. -/
theorem paperVeroneseFullNormalGenerator_eq_rename (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    paperVeroneseFullNormalGenerator K r extra i =
      MvPolynomial.rename finSumFinEquiv (paperVeroneseIndependentGenerator K r extra i) := by
  rw [paperVeroneseFullNormalGenerator, paperVeroneseFullNormalFace,
    Finset.prod_image (fun a _ b _ h => finSumFinEquiv.injective h)]
  simp only [paperVeroneseIndependentGenerator, map_prod, MvPolynomial.rename_X]

/-- Every chosen monomial is an actual generator of the native Veronese ideal. -/
theorem paperVeroneseFullNormalGenerator_mem (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    paperVeroneseFullNormalGenerator K r extra i ∈
      veroneseIdeal K (Fin (r + 1 + 1 + extra)) (r + 1) :=
  Ideal.subset_span ⟨paperVeroneseFullNormalFace r extra i,
    paperVeroneseFullNormalFace_card r extra i, rfl⟩

/-- Every native generator has the same positive homogeneous degree. -/
theorem paperVeroneseFullNormalGenerator_homogeneous (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    (paperVeroneseFullNormalGenerator K r extra i).IsHomogeneous (r + 1) := by
  have h := paperSquarefreeProduct_homogeneous_overRing K (paperVeroneseFullNormalFace r extra i)
  rwa [paperVeroneseFullNormalFace_card] at h

/-- Substitution by the selected generators in the actual native ambient ring. -/
def paperVeroneseFullNormalSubstitution (r extra : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) ⊕ Fin extra) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1 + extra)) K :=
  MvPolynomial.aeval (paperVeroneseFullNormalGenerator K r extra)

/-- The native substitution is the independent face substitution followed by renumbering. -/
theorem paperVeroneseFullNormalSubstitution_eq_comp (r extra : ℕ) :
    paperVeroneseFullNormalSubstitution K r extra =
      (MvPolynomial.rename finSumFinEquiv).comp (paperVeroneseIndependentSubstitution K r extra) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [paperVeroneseFullNormalSubstitution, paperVeroneseIndependentSubstitution,
    MvPolynomial.aeval_X, AlgHom.comp_apply]
  exact paperVeroneseFullNormalGenerator_eq_rename K r extra i

/-- The native chosen generators satisfy no polynomial relation over the coefficient ring. -/
theorem paperVeroneseFullNormalSubstitution_injective (r extra : ℕ) :
    Function.Injective (paperVeroneseFullNormalSubstitution K r extra) := by
  rw [paperVeroneseFullNormalSubstitution_eq_comp]
  exact (MvPolynomial.rename_injective finSumFinEquiv finSumFinEquiv.injective).comp
    (paperVeroneseIndependentSubstitution_injective K r extra)

/-- All prerequisites for the source normal-family theorem are paid in the actual Veronese ideal. -/
def paperVeroneseFullNormalFamilyData (r extra : ℕ) :
    PaperHomogeneousNormalFamilyData K (Fin (r + 1 + 1 + extra)) (Fin (r + 1 + 1) ⊕ Fin extra)
      (veroneseIdeal K (Fin (r + 1 + 1 + extra)) (r + 1)) where
  generator := paperVeroneseFullNormalGenerator K r extra
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := paperVeroneseFullNormalGenerator_mem K r extra
  homogeneous := paperVeroneseFullNormalGenerator_homogeneous K r extra
  independent := paperVeroneseFullNormalSubstitution_injective K r extra
  order_bound := paperVeroneseIdeal_weightOrder_overRing K _ _

/-- A polynomial normal map with one input variable per native ambient variable. -/
def paperVeroneseFullNormalSpaceMap (r extra : ℕ) :
    MvPolynomial (Fin (r + 1 + 1 + extra)) K →+*
      PaperIdealAssociatedGraded (veroneseIdeal K (Fin (r + 1 + 1 + extra)) (r + 1)) :=
  (paperVeroneseFullNormalFamilyData K r extra).polynomialMap.comp
    (MvPolynomial.rename finSumFinEquiv.symm).toRingHom

/-- Every positive Veronese degree below the variable count retains a full polynomial normal family. -/
theorem paperVeroneseFullNormalSpaceMap_injective (r extra : ℕ) :
    Function.Injective (paperVeroneseFullNormalSpaceMap K r extra) :=
  (paperVeroneseFullNormalFamilyData K r extra).polynomialMap_injective.comp
    (MvPolynomial.rename_injective finSumFinEquiv.symm finSumFinEquiv.symm.injective)

/-- No nonzero polynomial disappears under the full native normal map. -/
theorem paperVeroneseFullNormalSpaceMap_eq_zero_iff (r extra : ℕ)
    (p : MvPolynomial (Fin (r + 1 + 1 + extra)) K) :
    paperVeroneseFullNormalSpaceMap K r extra p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact paperVeroneseFullNormalSpaceMap_injective K r extra (by simpa only [map_zero] using h)
  · rintro rfl
    exact map_zero _

/-- Each input variable is sent to the actual initial class of its specified squarefree generator. -/
theorem paperVeroneseFullNormalSpaceMap_X (r extra : ℕ) (i : Fin (r + 1 + 1 + extra)) :
    paperVeroneseFullNormalSpaceMap K r extra (MvPolynomial.X i) =
      paperNativeReesSpecialization (veroneseIdeal K (Fin (r + 1 + 1 + extra)) (r + 1))
        (ReesGrading.mono _ 1 (paperVeroneseFullNormalGenerator K r extra (finSumFinEquiv.symm i))
          (by simpa only [pow_one] using
            paperVeroneseFullNormalGenerator_mem K r extra (finSumFinEquiv.symm i))) := by
  change (paperVeroneseFullNormalFamilyData K r extra).polynomialMap
    (MvPolynomial.rename finSumFinEquiv.symm (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]
  exact (paperVeroneseFullNormalFamilyData K r extra).polynomialMap_X (finSumFinEquiv.symm i)

end

end GaloisForLFunctions.HTGeometry
