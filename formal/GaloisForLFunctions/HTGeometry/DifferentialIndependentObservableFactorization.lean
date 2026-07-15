import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet
import GaloisForLFunctions.HTGeometry.DisjointRationalFunctionFields

/-!
# Factorization of disjoint differentially independent observables

In algebraic quantum field theory, independence of separated observable sectors is expressed by
an injective tensor-product comparison and by the absence of a hidden common observable algebra.
For a differentially independent family, disjoint labelled jet sectors satisfy exact field-theoretic
analogues of both statements.

The result is stronger than faithfulness of the observable net.  Two resolution vectors supported
on disjoint clock labels generate linearly disjoint fields; their tensor product over the base is a
domain, and their field intersection is exactly the base field.  The clock labels are observational
sectors, not temporal parameters.
-/

open Function Set Subalgebra MvPolynomial Algebra
open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Algebraically independent families indexed by the two summands of a disjoint union generate
linearly disjoint intermediate fields.  This transports the canonical rational-function tensor
factorization to the actual generated fields. -/
theorem algebraicIndependent_sum_adjoin_linearDisjoint
    {F E ι κ : Type*} [Field F] [Field E] [Algebra F E]
    (x : ι → E) (y : κ → E)
    (hxy : AlgebraicIndependent F (Sum.elim x y)) :
    (IntermediateField.adjoin F (Set.range x)).LinearDisjoint
      (IntermediateField.adjoin F (Set.range y)) := by
  let KX := FractionRing (MvPolynomial ι F)
  let KY := FractionRing (MvPolynomial κ F)
  let KXY := FractionRing (MvPolynomial (ι ⊕ κ) F)
  let fx : KX →ₐ[F] KXY := mvFractionRename Sum.inl Sum.inl_injective
  let fy : KY →ₐ[F] KXY := mvFractionRename Sum.inr Sum.inr_injective
  let gxy : KXY →ₐ[F] E :=
    (IntermediateField.val _).comp hxy.aevalEquivField.toAlgHom
  have hld : fx.fieldRange.LinearDisjoint fy.fieldRange :=
    canonicalRationalFieldRanges_linearDisjoint (F := F) (ι := ι) (κ := κ)
  have hmap := hld.map gxy
  have htotal (q : MvPolynomial (ι ⊕ κ) F) :
      gxy (algebraMap (MvPolynomial (ι ⊕ κ) F) KXY q) =
        MvPolynomial.aeval (Sum.elim x y) q := by
    simpa only [gxy, AlgHom.comp_apply] using
      hxy.aevalEquivField_algebraMap_apply_coe q
  have hxrange : (gxy.comp fx).fieldRange =
      IntermediateField.adjoin F (Set.range x) := by
    apply IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (g := MvPolynomial.aeval x)
    · apply MvPolynomial.ringHom_ext <;> intro i
      · change gxy (fx (algebraMap (MvPolynomial ι F) KX (MvPolynomial.C i))) =
          MvPolynomial.aeval x (MvPolynomial.C i)
        rw [mvFractionRename_algebraMap, htotal]
        simp
      · change gxy (fx (algebraMap (MvPolynomial ι F) KX (MvPolynomial.X i))) =
          MvPolynomial.aeval x (MvPolynomial.X i)
        rw [mvFractionRename_algebraMap, htotal]
        simp
    · exact (Algebra.adjoin_range_eq_range_aeval F x).symm
  have hyrange : (gxy.comp fy).fieldRange =
      IntermediateField.adjoin F (Set.range y) := by
    apply IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (g := MvPolynomial.aeval y)
    · apply MvPolynomial.ringHom_ext <;> intro i
      · change gxy (fy (algebraMap (MvPolynomial κ F) KY (MvPolynomial.C i))) =
          MvPolynomial.aeval y (MvPolynomial.C i)
        rw [mvFractionRename_algebraMap, htotal]
        simp
      · change gxy (fy (algebraMap (MvPolynomial κ F) KY (MvPolynomial.X i))) =
          MvPolynomial.aeval y (MvPolynomial.X i)
        rw [mvFractionRename_algebraMap, htotal]
        simp
    · exact (Algebra.adjoin_range_eq_range_aeval F y).symm
  rw [AlgHom.map_fieldRange, AlgHom.map_fieldRange, hxrange, hyrange] at hmap
  exact hmap

/-- Disjoint subfamilies of one algebraically independent family generate linearly disjoint
fields. -/
theorem algebraicIndependent_disjoint_adjoin_linearDisjoint
    {F E α : Type*} [Field F] [Field E] [Algebra F E]
    {z : α → E} (hz : AlgebraicIndependent F z)
    {s t : Set α} (hst : Disjoint s t) :
    (IntermediateField.adjoin F (z '' s)).LinearDisjoint
      (IntermediateField.adjoin F (z '' t)) := by
  let e : s ⊕ t → α := Sum.elim ((↑) : s → α) ((↑) : t → α)
  have he : Function.Injective e := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext hab)
    · have hab' : (a : α) = (b : α) := hab
      exact False.elim ((Set.disjoint_left.1 hst) a.2 (hab'.symm ▸ b.2))
    · have hab' : (a : α) = (b : α) := hab
      exact False.elim ((Set.disjoint_left.1 hst) b.2 (hab' ▸ a.2))
    · exact congrArg Sum.inr (Subtype.ext hab)
  have hsum : AlgebraicIndependent F
      (Sum.elim (fun i : s => z i) (fun i : t => z i)) := by
    have hsum' : AlgebraicIndependent F (z ∘ e) := hz.comp e he
    have heval : z ∘ e = Sum.elim (fun i : s => z i) (fun i : t => z i) := by
      funext p
      cases p <;> rfl
    rw [heval] at hsum'
    exact hsum'
  have hsrange : Set.range (fun i : s => z i) = z '' s := by
    ext a
    simp
  have htrange : Set.range (fun i : t => z i) = z '' t := by
    ext a
    simp
  rw [← hsrange, ← htrange]
  exact algebraicIndependent_sum_adjoin_linearDisjoint
    (fun i : s => z i) (fun i : t => z i) hsum

/-- Disjoint labelled jet sectors of a differentially independent family are linearly disjoint
over the coefficient field. -/
theorem differentialIndependent_disjointJetFields_linearDisjoint
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : ι → E} (hx : DifferentialIndependent F x)
    {s t : Set (ι × ℕ)} (hst : Disjoint s t) :
    (IntermediateField.adjoin F
        ((fun p : ι × ℕ => differentialJet p.2 (x p.1)) '' s)).LinearDisjoint
      (IntermediateField.adjoin F
        ((fun p : ι × ℕ => differentialJet p.2 (x p.1)) '' t)) :=
  algebraicIndependent_disjoint_adjoin_linearDisjoint hx hst

/-- Resolution vectors supported on disjoint clock labels generate linearly disjoint observable
fields. -/
theorem differentialIndependent_disjoint_familyObservableFields_linearDisjoint
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : ι → E} (hx : DifferentialIndependent F x)
    (M N : ι → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    (differentialFamilyObservableField F x M).LinearDisjoint
      (differentialFamilyObservableField F x N) := by
  apply differentialIndependent_disjointJetFields_linearDisjoint hx
  rw [Set.disjoint_left]
  intro p hpM hpN
  rcases hdisjoint p.1 with hM | hN
  · simpa [differentialFamilyVisibleJetIndices, hM] using hpM
  · simpa [differentialFamilyVisibleJetIndices, hN] using hpN

/-- **Exact common-observable law.**  Disjoint clock sectors share only the coefficient field. -/
theorem differentialIndependent_disjoint_familyObservableFields_inf_eq_bot
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : ι → E} (hx : DifferentialIndependent F x)
    (M N : ι → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    differentialFamilyObservableField F x M ⊓
        differentialFamilyObservableField F x N = ⊥ :=
  (differentialIndependent_disjoint_familyObservableFields_linearDisjoint
    hx M N hdisjoint).inf_eq_bot

/-- **Observable tensor-domain law.**  The tensor product of two disjoint clock-observable fields
has no zero divisors over the coefficient field. -/
theorem differentialIndependent_disjoint_familyObservableFields_tensor_isDomain
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : ι → E} (hx : DifferentialIndependent F x)
    (M N : ι → ℕ) (hdisjoint : ∀ i, M i = 0 ∨ N i = 0) :
    IsDomain
      (differentialFamilyObservableField F x M ⊗[F]
        differentialFamilyObservableField F x N) :=
  (differentialIndependent_disjoint_familyObservableFields_linearDisjoint
    hx M N hdisjoint).isDomain

end

end GaloisForLFunctions.HTGeometry
