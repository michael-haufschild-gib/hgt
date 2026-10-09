import GaloisForLFunctions.HTGeometry.PaperHomogeneousNormalRelations
import GaloisForLFunctions.HTGeometry.PaperSquarefreeWeightOrders

/-!
# All squarefree Veronese relations survive in the normal cone

Apply the source Rees coefficient kernel to every squarefree generator of
the native Veronese ideal, including infinitely many ambient variables.
The whole generator subring embeds in the associated graded ring with its
original polynomial relations, over any commutative coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

variable (K σ : Type*) [CommRing K] [DecidableEq σ]

/-- Fully paid presentation data for every native squarefree generator of a fixed positive degree. -/
def paperVeroneseNormalPresentation (r : ℕ) :
    PaperHomogeneousNormalPresentationData K σ {s : Finset σ // s.card = r + 1}
      (veroneseIdeal K σ (r + 1)) where
  generator s := ∏ i ∈ s.val, MvPolynomial.X i
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem s := Ideal.subset_span ⟨s.val, s.property, rfl⟩
  homogeneous s := by
    simpa only [s.property] using paperSquarefreeProduct_homogeneous_overRing K s.val
  order_bound := paperVeroneseIdeal_weightOrder_overRing K σ (r + 1)

/-- Simultaneous substitution into the actual initial classes of all Veronese generators. -/
def paperVeroneseNormalMap (r : ℕ) :
    MvPolynomial {s : Finset σ // s.card = r + 1} K →+*
      PaperIdealAssociatedGraded (veroneseIdeal K σ (r + 1)) :=
  (paperVeroneseNormalPresentation K σ r).polynomialMap

/-- Every relation between squarefree initial classes is exactly a relation of the original monomials. -/
theorem paperVeroneseNormalMap_relations_iff (r : ℕ)
    (p : MvPolynomial {s : Finset σ // s.card = r + 1} K) :
    paperVeroneseNormalMap K σ r p = 0 ↔
      MvPolynomial.aeval (fun s : {s : Finset σ // s.card = r + 1} =>
        ∏ i ∈ s.val, (MvPolynomial.X i : MvPolynomial σ K)) p = 0 :=
  (paperVeroneseNormalPresentation K σ r).polynomialMap_eq_zero_iff p

/-- The full squarefree Veronese relation ideal is unchanged in normal coordinates. -/
theorem paperVeroneseNormalMap_kernel (r : ℕ) :
    RingHom.ker (paperVeroneseNormalMap K σ r) =
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : {s : Finset σ // s.card = r + 1} =>
          ∏ i ∈ s.val, (MvPolynomial.X i : MvPolynomial σ K))).toRingHom :=
  (paperVeroneseNormalPresentation K σ r).kernel_eq

/-- Every coordinate has its exact native squarefree monomial as degree-one Rees representative. -/
theorem paperVeroneseNormalMap_X (r : ℕ) (s : {s : Finset σ // s.card = r + 1}) :
    paperVeroneseNormalMap K σ r (MvPolynomial.X s) =
      paperNativeReesSpecialization (veroneseIdeal K σ (r + 1))
        (ReesGrading.mono _ 1 (∏ i ∈ s.val, (MvPolynomial.X i : MvPolynomial σ K))
          (by rw [pow_one]; exact Ideal.subset_span ⟨s.val, s.property, rfl⟩)) :=
  (paperVeroneseNormalPresentation K σ r).polynomialMap_X s

/-- The full squarefree Veronese coordinate ring maps into the native associated graded ring. -/
def paperVeroneseRelationQuotientMap (r : ℕ) :
    (MvPolynomial {s : Finset σ // s.card = r + 1} K ⧸
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : {s : Finset σ // s.card = r + 1} =>
          ∏ i ∈ s.val, (MvPolynomial.X i : MvPolynomial σ K))).toRingHom) →+*
      PaperIdealAssociatedGraded (veroneseIdeal K σ (r + 1)) :=
  (paperVeroneseNormalPresentation K σ r).relationQuotientMap

/-- The original squarefree relation quotient embeds without losing any nonzero class. -/
theorem paperVeroneseRelationQuotientMap_injective (r : ℕ) :
    Function.Injective (paperVeroneseRelationQuotientMap K σ r) :=
  (paperVeroneseNormalPresentation K σ r).relationQuotientMap_injective

/-- The actual squarefree Veronese subring embeds into the normal cone ring. -/
def paperVeroneseGeneratorRingEmbedding (r : ℕ) :
    (MvPolynomial.aeval (R := K)
      (fun s : {s : Finset σ // s.card = r + 1} =>
        ∏ i ∈ s.val, (MvPolynomial.X i : MvPolynomial σ K))).toRingHom.range →+*
      PaperIdealAssociatedGraded (veroneseIdeal K σ (r + 1)) :=
  (paperVeroneseNormalPresentation K σ r).generatorRingEmbedding

/-- Every element of the full native squarefree generator subring survives in normal coordinates. -/
theorem paperVeroneseGeneratorRingEmbedding_injective (r : ℕ) :
    Function.Injective (paperVeroneseGeneratorRingEmbedding K σ r) :=
  (paperVeroneseNormalPresentation K σ r).generatorRingEmbedding_injective

end

end GaloisForLFunctions.HTGeometry
