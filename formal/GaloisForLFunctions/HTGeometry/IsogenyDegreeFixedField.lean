import GaloisForLFunctions.HTGeometry.DeckFixedFieldSimpleGenerator

/-!
# The deck description from one algebraic equation of the covering degree

The deck description `alpha^{n*} K = K^{Gamma_n}` needs, beyond formal facts about the pullback, a
single order-zero input: the generic point satisfies an algebraic equation over the pullback whose
degree is the degree of the covering.  Here that input is packaged directly: a nonzero polynomial of
degree at most the order of the deck group, satisfied by the generic point over the intermediate
field, suffices.

The minimal polynomial can only have smaller degree, so the differential degree bound of
`finrank_le_of_differentialAdjoin_eq_top` applies, and Artin's theorem closes the gap in the other
direction.

* `eq_fixedField_of_annihilating_poly`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] [CharZero K]

/-- **The deck description from one annihilating polynomial of the covering degree.** -/
theorem eq_fixedField_of_annihilating_poly
    (Γ : Subgroup (K ≃ₐ[C] K)) [Fintype Γ]
    (E : IntermediateField C K) (hE : DerivationClosed E)
    (hfix : E ≤ IntermediateField.fixedField Γ)
    {g : K} (hgen : IntermediateField.adjoin C (differentialJetSet ({g} : Set K)) = ⊤)
    {q : Polynomial E} (hq0 : q ≠ 0) (hq : Polynomial.aeval g q = 0)
    (hdeg : q.natDegree ≤ Nat.card Γ) :
    E = IntermediateField.fixedField Γ := by
  have halg : IsAlgebraic E g := ⟨q, hq0, hq⟩
  refine eq_fixedField_of_algebraic_generator Γ E hE hfix hgen halg ?_
  have hle : (minpoly E g).degree ≤ q.degree :=
    minpoly.degree_le_of_ne_zero (A := E) (x := g) hq0 hq
  have hne : minpoly E g ≠ 0 := minpoly.ne_zero halg.isIntegral
  have hnat : (minpoly E g).natDegree ≤ q.natDegree :=
    Polynomial.natDegree_le_natDegree hle
  omega

end

end GaloisForLFunctions.HTGeometry
