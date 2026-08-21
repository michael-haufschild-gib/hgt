import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAdjoin
import GaloisForLFunctions.HTGeometry.FixedFieldDegreeCriterion
import GaloisForLFunctions.HTGeometry.DeckDegreeUpperBound

/-!
# A single generator identifies a subfield with the invariants of a deck group

A subfield sitting inside the invariants of a finite faithful action is the whole invariant field
as soon as the ambient field is generated over it by one element whose minimal polynomial has
degree the order of the group.  This is the usable form of "a degree-`d` cover with deck group of
order `d` is Galois": the degree hypothesis is supplied by one generator rather than by a global
degree computation.

In the differential setting the generator hypothesis may be weakened to *differential* generation.
An algebraic element carries no new jets, so differential generation by an algebraic element is
already ordinary generation, and the two forms coincide.

* `eq_fixedPoints_of_adjoin_simple_eq_top`, `eq_fixedPoints_of_differentialAdjoin_eq_top` — the
  `MulSemiringAction` form;
* `finrank_le_of_differentialAdjoin_eq_top`,
  `finiteDimensional_of_differentialAdjoin_eq_top`,
  `eq_fixedField_of_differentialAdjoin_eq_top` — the automorphism-subgroup form, which supplies
  exactly the one-sided degree estimate that the deck-degree criterion still asks for;
* `adjoin_differentialJetSet_eq_top_of_base`, `eq_fixedField_of_algebraic_generator`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **One algebraic generator of the right degree identifies the invariants.** -/
theorem eq_fixedPoints_of_adjoin_simple_eq_top
    {K : Type*} [Field K] (L : Subfield K)
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G K] [FaithfulSMul G K]
    (hle : L ≤ FixedPoints.subfield G K)
    {a : K} (ha : IsAlgebraic L a)
    (htop : IntermediateField.adjoin L ({a} : Set K) = ⊤)
    (hdeg : (minpoly L a).natDegree = Fintype.card G) :
    L = FixedPoints.subfield G K := by
  haveI : FiniteDimensional L K := by
    have h1 : FiniteDimensional L (IntermediateField.adjoin L ({a} : Set K)) :=
      IntermediateField.adjoin.finiteDimensional ha.isIntegral
    rw [htop] at h1
    exact (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv.finiteDimensional
  refine eq_fixedPoints_subfield_of_finrank L hle ?_
  have h1 := IntermediateField.adjoin.finrank (K := L) (L := K) ha.isIntegral
  rw [htop, IntermediateField.finrank_top'] at h1
  rw [h1, hdeg]

/-- **The differential form.**  Differential generation by an algebraic element of the right degree
identifies a derivation-closed subfield with the invariants of a finite faithful action. -/
theorem eq_fixedPoints_of_differentialAdjoin_eq_top
    {K : Type*} [Field K] [Differential K] [CharZero K]
    (L : Subfield K) (hL : ∀ x ∈ L, x′ ∈ L)
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G K] [FaithfulSMul G K]
    (hle : L ≤ FixedPoints.subfield G K)
    {a : K} (ha : IsAlgebraic L a)
    (htop : IntermediateField.adjoin L (differentialJetSet ({a} : Set K)) = ⊤)
    (hdeg : (minpoly L a).natDegree = Fintype.card G) :
    L = FixedPoints.subfield G K := by
  letI := subfieldDifferential L hL
  haveI := subfield_differentialAlgebra L hL
  refine eq_fixedPoints_of_adjoin_simple_eq_top L hle ha ?_ hdeg
  rw [← differentialAdjoin_singleton_eq_adjoin ha]
  exact htop

/-! ### The automorphism-subgroup form -/

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] [CharZero K]

/-- **A differential generator bounds the degree.**  If the ambient differential field is generated
over a derivation-closed intermediate field by the jets of a single algebraic element, its degree is
the degree of that element's minimal polynomial. -/
theorem finrank_le_of_differentialAdjoin_eq_top
    (E : IntermediateField C K) (hE : DerivationClosed E)
    {a : K} (ha : IsAlgebraic E a)
    (htop : IntermediateField.adjoin E (differentialJetSet ({a} : Set K)) = ⊤)
    {d : ℕ} (hd : (minpoly E a).natDegree ≤ d) :
    Module.finrank E K ≤ d := by
  letI := derivationClosedDifferential E hE
  haveI := derivationClosed_differentialAlgebra E hE
  have hadj : IntermediateField.adjoin E ({a} : Set K) = ⊤ := by
    rw [← differentialAdjoin_singleton_eq_adjoin ha]
    exact htop
  have h1 := IntermediateField.adjoin.finrank (K := E) (L := K) ha.isIntegral
  rw [hadj, IntermediateField.finrank_top'] at h1
  omega

theorem finiteDimensional_of_differentialAdjoin_eq_top
    (E : IntermediateField C K) (hE : DerivationClosed E)
    {a : K} (ha : IsAlgebraic E a)
    (htop : IntermediateField.adjoin E (differentialJetSet ({a} : Set K)) = ⊤) :
    FiniteDimensional E K := by
  letI := derivationClosedDifferential E hE
  haveI := derivationClosed_differentialAlgebra E hE
  have hadj : IntermediateField.adjoin E ({a} : Set K) = ⊤ := by
    rw [← differentialAdjoin_singleton_eq_adjoin ha]
    exact htop
  have h1 : FiniteDimensional E (IntermediateField.adjoin E ({a} : Set K)) :=
    IntermediateField.adjoin.finiteDimensional ha.isIntegral
  rw [hadj] at h1
  exact (IntermediateField.topEquiv (F := E) (E := K)).toLinearEquiv.finiteDimensional

/-- **The deck description of a differential cover from one generator.**  A derivation-closed
intermediate field inside the invariants of a finite automorphism group, over which the ambient
differential field is differentially generated by a single element of degree at most the order of
the group, is exactly the invariant field. -/
theorem eq_fixedField_of_differentialAdjoin_eq_top
    (Γ : Subgroup (K ≃ₐ[C] K)) [Fintype Γ]
    (E : IntermediateField C K) (hE : DerivationClosed E)
    (hfix : E ≤ IntermediateField.fixedField Γ)
    {a : K} (ha : IsAlgebraic E a)
    (htop : IntermediateField.adjoin E (differentialJetSet ({a} : Set K)) = ⊤)
    (hd : (minpoly E a).natDegree ≤ Nat.card Γ) :
    E = IntermediateField.fixedField Γ := by
  haveI := finiteDimensional_of_differentialAdjoin_eq_top E hE ha htop
  exact eq_fixedField_of_finrank_le Γ E hfix
    (finrank_le_of_differentialAdjoin_eq_top E hE ha htop hd)

omit [CharZero K] in
/-- Differential generation passes to any larger base field. -/
theorem adjoin_differentialJetSet_eq_top_of_base
    (E : IntermediateField C K) {s : Set K}
    (htop : IntermediateField.adjoin C (differentialJetSet s) = ⊤) :
    IntermediateField.adjoin (E : Type _) (differentialJetSet s) = ⊤ := by
  have h1 : (IntermediateField.adjoin (E : Type _) (differentialJetSet s)).restrictScalars C
      = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← htop, IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin (E : Type _) _ hy
  rwa [IntermediateField.restrictScalars_eq_top_iff] at h1

/-- **The finite deck description of a differential cover.**  If the ambient differential field is
differentially generated over the constants by a single point, then every derivation-closed
intermediate field inside the invariants of a finite automorphism group, over which that point is
algebraic of degree at most the order of the group, is exactly the invariant field.

This is the field-theoretic content of `alpha^{n*} K = K^{ker(alpha^n)}`: the only geometric input
left is the degree of the covering map, as an algebraic equation for the generic point over the
pullback. -/
theorem eq_fixedField_of_algebraic_generator
    (Γ : Subgroup (K ≃ₐ[C] K)) [Fintype Γ]
    (E : IntermediateField C K) (hE : DerivationClosed E)
    (hfix : E ≤ IntermediateField.fixedField Γ)
    {g : K} (hgen : IntermediateField.adjoin C (differentialJetSet ({g} : Set K)) = ⊤)
    (ha : IsAlgebraic E g)
    (hd : (minpoly E g).natDegree ≤ Nat.card Γ) :
    E = IntermediateField.fixedField Γ :=
  eq_fixedField_of_differentialAdjoin_eq_top Γ E hE hfix ha
    (adjoin_differentialJetSet_eq_top_of_base E hgen) hd

end GaloisForLFunctions.HTGeometry
