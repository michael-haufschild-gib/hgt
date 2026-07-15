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

/-!
## Free-transverse saturation

Linear disjointness also controls a more asymmetric reconstruction question.  Suppose one observes
all jets of an intrinsic family, but only a selected set of those jets after adjoining selected
jets of a transverse family.  Joint differential independence forces exact saturation: transverse
observables reveal none of the omitted intrinsic jets.  This is the zero-defect case of the
Kähler–Ore saturation-conductor program.
-/

/-- Three jointly algebraically independent blocks generate two fields whose intersection is
exactly the field generated by their common block.  Unlike the differential-field version, the
three blocks may be arbitrary selected families of jet observables. -/
theorem algebraicIndependent_threeBlock_adjoin_inf
    {F E A B C : Type*} [Field F] [Field E] [Algebra F E]
    (a : A → E) (b : B → E) (c : C → E)
    (habc : AlgebraicIndependent F (Sum.elim a (Sum.elim b c))) :
    IntermediateField.adjoin F (Set.range (Sum.elim a b)) ⊓
        IntermediateField.adjoin F (Set.range (Sum.elim a c)) =
      IntermediateField.adjoin F (Set.range a) := by
  let K0 : IntermediateField F E := IntermediateField.adjoin F (Set.range a)
  have hbcAlg : AlgebraicIndependent K0 (Sum.elim b c) := by
    change AlgebraicIndependent (IntermediateField.adjoin F (Set.range a))
      (Sum.elim b c)
    apply IntermediateField.algebraicIndependent_adjoin_iff.mpr
    have hswap : AlgebraicIndependent F (Sum.elim (Sum.elim b c) a) := by
      have h := habc.comp (Equiv.sumComm (B ⊕ C) A)
        (Equiv.sumComm (B ⊕ C) A).injective
      simpa using h
    exact (AlgebraicIndependent.sumElim_iff.mp hswap).2
  have hld :
      (IntermediateField.adjoin K0 (Set.range b)).LinearDisjoint
        (IntermediateField.adjoin K0 (Set.range c)) :=
    algebraicIndependent_sum_adjoin_linearDisjoint b c hbcAlg
  have hmeet := restrictScalars_adjoin_inf_eq_commonBase_of_linearDisjoint
    K0 (Set.range b) (Set.range c) hld
  have habSet : Set.range (Sum.elim a b) = Set.range a ∪ Set.range b := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      rcases i with i | j
      · exact Set.mem_union_left _ ⟨i, rfl⟩
      · exact Set.mem_union_right _ ⟨j, rfl⟩
    · rintro (hz | hz)
      · rcases hz with ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · rcases hz with ⟨j, rfl⟩
        exact ⟨Sum.inr j, rfl⟩
  have hacSet : Set.range (Sum.elim a c) = Set.range a ∪ Set.range c := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      rcases i with i | j
      · exact Set.mem_union_left _ ⟨i, rfl⟩
      · exact Set.mem_union_right _ ⟨j, rfl⟩
    · rintro (hz | hz)
      · rcases hz with ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      · rcases hz with ⟨j, rfl⟩
        exact ⟨Sum.inr j, rfl⟩
  have hleft :
      (IntermediateField.adjoin K0 (Set.range b)).restrictScalars F =
        IntermediateField.adjoin F (Set.range (Sum.elim a b)) := by
    change (IntermediateField.adjoin
      (IntermediateField.adjoin F (Set.range a)) (Set.range b)).restrictScalars F = _
    rw [IntermediateField.adjoin_adjoin_left, habSet]
  have hright :
      (IntermediateField.adjoin K0 (Set.range c)).restrictScalars F =
        IntermediateField.adjoin F (Set.range (Sum.elim a c)) := by
    change (IntermediateField.adjoin
      (IntermediateField.adjoin F (Set.range a)) (Set.range c)).restrictScalars F = _
    rw [IntermediateField.adjoin_adjoin_left, hacSet]
  rw [hleft, hright] at hmeet
  exact hmeet

/-- **Free-transverse saturation law.**  Let `y` be an intrinsic clock family and `z` a jointly
differentially independent transverse family.  For arbitrary sets `s` and `t` of visible jets,
intersecting the full differential field of `y` with the field generated by the visible `y`-jets
and visible `z`-jets recovers exactly the visible `y`-field.  Thus a free transverse extension
cannot manufacture access to any hidden intrinsic jet. -/
theorem differentialIndependent_transverseObservable_inf
    {F E I J : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (y : I → E) (z : J → E)
    (hyz : DifferentialIndependent F (Sum.elim y z))
    (s : Set (I × ℕ)) (t : Set (J × ℕ)) :
    differentialAdjoin F (Set.range y) ⊓
        IntermediateField.adjoin F
          ((fun p : I × ℕ ↦ differentialJet p.2 (y p.1)) '' s ∪
            (fun p : J × ℕ ↦ differentialJet p.2 (z p.1)) '' t) =
      IntermediateField.adjoin F
        ((fun p : I × ℕ ↦ differentialJet p.2 (y p.1)) '' s) := by
  let yjet : I × ℕ → E := fun p ↦ differentialJet p.2 (y p.1)
  let zjet : J × ℕ → E := fun p ↦ differentialJet p.2 (z p.1)
  let a : s → E := fun p ↦ yjet p.1
  let b : ↑(sᶜ) → E := fun p ↦ yjet p.1
  let c : t → E := fun p ↦ zjet p.1
  let e : s ⊕ (↑(sᶜ) ⊕ t) → (I ⊕ J) × ℕ :=
    Sum.elim
      (fun p ↦ (Sum.inl p.1.1, p.1.2))
      (Sum.elim
        (fun p ↦ (Sum.inl p.1.1, p.1.2))
        (fun p ↦ (Sum.inr p.1.1, p.1.2)))
  have he : Function.Injective e := by
    intro p q hpq
    rcases p with p | p
    · rcases q with q | q
      · congr 1
        apply Subtype.ext
        simp [e] at hpq
        exact Prod.ext hpq.1 hpq.2
      · rcases q with q | q
        · simp [e] at hpq
          have hpval : p.1 = q.1 := Prod.ext hpq.1 hpq.2
          exact False.elim (q.2 (hpval ▸ p.2))
        · simp [e] at hpq
    · rcases p with p | p
      · rcases q with q | q
        · simp [e] at hpq
          have hpval : p.1 = q.1 := Prod.ext hpq.1 hpq.2
          exact False.elim (p.2 (hpval.symm ▸ q.2))
        · rcases q with q | q
          · congr 2
            apply Subtype.ext
            simp [e] at hpq
            exact Prod.ext hpq.1 hpq.2
          · simp [e] at hpq
      · rcases q with q | q
        · simp [e] at hpq
        · rcases q with q | q
          · simp [e] at hpq
          · congr 2
            apply Subtype.ext
            simp [e] at hpq
            exact Prod.ext hpq.1 hpq.2
  have hthree : AlgebraicIndependent F (Sum.elim a (Sum.elim b c)) := by
    have hfull : AlgebraicIndependent F
        (fun p : (I ⊕ J) × ℕ ↦
          differentialJet p.2 (Sum.elim y z p.1)) := hyz
    have hcomp := hfull.comp e he
    have hfun :
        ((fun p : (I ⊕ J) × ℕ ↦
          differentialJet p.2 (Sum.elim y z p.1)) ∘ e) =
          Sum.elim a (Sum.elim b c) := by
      funext p
      rcases p with p | p
      · rfl
      · rcases p with p | p <;> rfl
    rw [hfun] at hcomp
    exact hcomp
  have hcore := algebraicIndependent_threeBlock_adjoin_inf a b c hthree
  have hyall : Set.range (Sum.elim a b) = Set.range yjet := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      rcases p with p | p
      · exact ⟨p.1, rfl⟩
      · exact ⟨p.1, rfl⟩
    · rintro ⟨p, rfl⟩
      by_cases hp : p ∈ s
      · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
      · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩
  have hvis : Set.range (Sum.elim a c) = yjet '' s ∪ zjet '' t := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      rcases p with p | p
      · exact Set.mem_union_left _ ⟨p.1, p.2, rfl⟩
      · exact Set.mem_union_right _ ⟨p.1, p.2, rfl⟩
    · rintro (hw | hw)
      · rcases hw with ⟨p, hp, rfl⟩
        exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
      · rcases hw with ⟨p, hp, rfl⟩
        exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩
  have ha : Set.range a = yjet '' s := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hjetSet : differentialJetSet (Set.range y) = Set.range yjet := by
    ext w
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, n, rfl⟩
      exact ⟨(i, n), rfl⟩
    · rintro ⟨⟨i, n⟩, rfl⟩
      exact ⟨y i, ⟨i, rfl⟩, n, rfl⟩
  rw [hyall, hvis, ha] at hcore
  change IntermediateField.adjoin F (differentialJetSet (Set.range y)) ⊓
      IntermediateField.adjoin F (yjet '' s ∪ zjet '' t) =
    IntermediateField.adjoin F (yjet '' s)
  rw [hjetSet]
  exact hcore

end

end GaloisForLFunctions.HTGeometry
