import GaloisForLFunctions.HTGeometry.PaperTriangularExponentExtension
import GaloisForLFunctions.HTGeometry.PaperCofaceExponentEmbedding
import GaloisForLFunctions.HTGeometry.PaperSquarefreeWeightOrders

/-!
# A full independent family of squarefree Veronese generators

Start with the complementary faces on `r + 2` variables. For every extra
variable, adjoin its product with the first `r` core variables. All faces
have size `r + 1`; the triangular exponent map proves independence over
arbitrary commutative coefficient rings.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

/-- The fixed size-`r` core face used for every extra variable. -/
def paperVeroneseCoreFace (r : ℕ) : Finset (Fin (r + 1 + 1)) :=
  Finset.univ.image (Fin.castAdd 2 : Fin r → Fin (r + 1 + 1))

/-- The common core face has its prescribed size, also when it is empty. -/
theorem paperVeroneseCoreFace_card (r : ℕ) : (paperVeroneseCoreFace r).card = r := by
  rw [paperVeroneseCoreFace, Finset.card_image_of_injective _ (Fin.castAdd_injective r 2)]
  simp

/-- Core cofaces together with one squarefree face for each extra variable. -/
def paperVeroneseIndependentFace (r extra : ℕ) :
    Fin (r + 1 + 1) ⊕ Fin extra → Finset (Fin (r + 1 + 1) ⊕ Fin extra)
  | Sum.inl i => (Finset.univ.erase i).image Sum.inl
  | Sum.inr j => insert (Sum.inr j) ((paperVeroneseCoreFace r).image Sum.inl)

/-- Every chosen generator has the common Veronese degree. -/
theorem paperVeroneseIndependentFace_card (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    (paperVeroneseIndependentFace r extra i).card = r + 1 := by
  cases i with
  | inl i =>
    rw [paperVeroneseIndependentFace, Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  | inr j =>
    rw [paperVeroneseIndependentFace, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ Sum.inl_injective, paperVeroneseCoreFace_card]

/-- The squarefree exponent of the fixed core face. -/
def paperVeroneseCoreExponent (r : ℕ) : Fin (r + 1 + 1) →₀ ℕ :=
  ∑ i ∈ paperVeroneseCoreFace r, Finsupp.single i 1

/-- The extended coface exponent transformation for the full chosen family. -/
def paperVeroneseIndependentExponentMap (r extra : ℕ) :
    (Fin (r + 1 + 1) ⊕ Fin extra →₀ ℕ) →+ (Fin (r + 1 + 1) ⊕ Fin extra →₀ ℕ) :=
  paperTriangularExponentMap (paperCofaceExponentMap r) (paperVeroneseCoreExponent r)

/-- Every input exponent remains recoverable after adjoining arbitrarily many extra variables. -/
theorem paperVeroneseIndependentExponentMap_injective (r extra : ℕ) :
    Function.Injective (paperVeroneseIndependentExponentMap r extra) :=
  paperTriangularExponentMap_injective _ _ (paperCofaceExponentMap_injective r)

/-- Each variable is sent to the squarefree exponent of its specified face. -/
theorem paperVeroneseIndependentExponentMap_single (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    paperVeroneseIndependentExponentMap r extra (Finsupp.single i 1) =
      ∑ j ∈ paperVeroneseIndependentFace r extra i, Finsupp.single j 1 := by
  cases i with
  | inl i =>
    rw [paperVeroneseIndependentExponentMap, paperTriangularExponentMap_single_inl,
      paperCofaceExponentMap_single, Finsupp.sumElim_eq_add]
    simp only [Finsupp.mapDomain_zero, add_zero, Finsupp.mapDomain_finsetSum,
      Finsupp.mapDomain_single, paperVeroneseIndependentFace]
    symm
    exact Finset.sum_image (fun a _ b _ h => Sum.inl_injective h)
  | inr j =>
    rw [paperVeroneseIndependentExponentMap, paperTriangularExponentMap_single_inr,
      Finsupp.sumElim_eq_add, paperVeroneseCoreExponent]
    simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
      paperVeroneseIndependentFace]
    rw [Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => Sum.inl_injective h)]
    exact add_comm _ _

variable (K : Type*) [CommRing K]

/-- Actual squarefree face monomials, over any commutative coefficient ring. -/
def paperVeroneseIndependentGenerator (r extra : ℕ) (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    MvPolynomial (Fin (r + 1 + 1) ⊕ Fin extra) K :=
  ∏ j ∈ paperVeroneseIndependentFace r extra i, MvPolynomial.X j

/-- All selected generators are homogeneous of the required positive degree. -/
theorem paperVeroneseIndependentGenerator_homogeneous (r extra : ℕ)
    (i : Fin (r + 1 + 1) ⊕ Fin extra) :
    (paperVeroneseIndependentGenerator K r extra i).IsHomogeneous (r + 1) := by
  have h := paperSquarefreeProduct_homogeneous_overRing K (paperVeroneseIndependentFace r extra i)
  rwa [paperVeroneseIndependentFace_card] at h

/-- Simultaneous substitution by the actual chosen Veronese face monomials. -/
def paperVeroneseIndependentSubstitution (r extra : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) ⊕ Fin extra) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) ⊕ Fin extra) K :=
  MvPolynomial.aeval (paperVeroneseIndependentGenerator K r extra)

/-- The native face substitution is exactly the map induced by the injective exponent map. -/
theorem paperVeroneseIndependentSubstitution_eq_mapDomain (r extra : ℕ) :
    paperVeroneseIndependentSubstitution K r extra =
      AddMonoidAlgebra.mapDomainAlgHom K K (paperVeroneseIndependentExponentMap r extra) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [paperVeroneseIndependentSubstitution, MvPolynomial.aeval_X]
  change paperVeroneseIndependentGenerator K r extra i =
    AddMonoidAlgebra.mapDomain (paperVeroneseIndependentExponentMap r extra)
      (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : K))
  rw [AddMonoidAlgebra.mapDomain_single]
  change paperVeroneseIndependentGenerator K r extra i =
    MvPolynomial.monomial (paperVeroneseIndependentExponentMap r extra (Finsupp.single i 1)) 1
  rw [paperVeroneseIndependentExponentMap_single]
  exact prod_X_eq_monomial _

/-- The full selected squarefree family satisfies no scalar polynomial relation over any ring. -/
theorem paperVeroneseIndependentSubstitution_injective (r extra : ℕ) :
    Function.Injective (paperVeroneseIndependentSubstitution K r extra) := by
  rw [paperVeroneseIndependentSubstitution_eq_mapDomain]
  exact AddMonoidAlgebra.mapDomain_injective (paperVeroneseIndependentExponentMap_injective r extra)

end

end GaloisForLFunctions.HTGeometry
