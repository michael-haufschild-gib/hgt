import GaloisForLFunctions.HTGeometry.WickContractedMatroidPersistence

/-!
# Differential-algebraic coefficient-field base change

Differential independence is insensitive to adjoining any set of differentially algebraic
coefficients. The set-valued persistence theorem supplies one direction; this module proves the
exact set and family equivalences, identifies the complete relative differential matroid with the
original one, and derives arbitrary-observation DA/HT invariance. Contracting such a coefficient
set is consequently just deleting its loop directions.
-/

open Matroid Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- Differential independence descends along an injective coefficient-field extension. -/
theorem DifferentialIndependent.restrictScalars
    {F K E ι : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [Differential E] {x : ι → E} (hx : DifferentialIndependent K x) :
    DifferentialIndependent F x := by
  unfold DifferentialIndependent at hx ⊢
  exact AlgebraicIndependent.restrictScalars
    (FaithfulSMul.algebraMap_injective F K) hx

/-- **Set-level differential-algebraic base-change law.**  Adjoining any set of elements that
are individually differentially algebraic over the coefficient field preserves differential
independence of every set.  This is the proof kernel for all family and singleton forms below. -/
theorem diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {I G : Set E} (hI : DiffIndepOn F I)
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DiffIndepOn (differentialAdjoin F G) I := by
  have hEmpty : differentialAdjoin F (∅ : Set E) = ⊥ := by
    apply le_antisymm
    · rw [differentialAdjoin]
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨g, hg, _, _⟩
      exact hg.elim
    · exact bot_le
  have hIEmpty : DiffIndepOn (differentialAdjoin F (∅ : Set E)) I := by
    rw [hEmpty]
    exact DifferentialIndependent.extendScalars hI
  apply diffIndepOn_differentialAdjoin_of_forall_finite_subset
  intro G₀ hG₀ hfin
  have hDA : ∀ g ∈ G₀,
      DifferentialAlgebraicOver (differentialAdjoin F (∅ : Set E)) g := by
    intro g hg
    exact differentialAlgebraicOver_mono (hG g (hG₀ hg))
  have hstage :=
    diffIndepOn_differentialAdjoin_union_finite_of_differentialAlgebraicOver
      (F := F) (E := E) (S := (∅ : Set E)) (I := I) (G₀ := G₀)
      hfin hDA hIEmpty
  rw [Set.empty_union] at hstage
  exact hstage

/-- **Exact set-level differential-algebraic base change.** Adjoining an arbitrary set of
elements individually differentially algebraic over the coefficient field preserves and reflects
differential independence of every set. -/
theorem diffIndepOn_differentialAdjoin_iff_of_differentialAlgebraicOver
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {I G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DiffIndepOn (differentialAdjoin F G) I ↔ DiffIndepOn F I := by
  constructor
  · exact DifferentialIndependent.restrictScalars
  · exact fun hI ↦
      diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver hI hG

/-- **Differential-algebraic base change preserves the entire differential matroid.** If every
adjoined coefficient is differentially algebraic over `F`, then the relative differential
matroid over the generated field is exactly the original differential matroid over `F`. This
single identity simultaneously controls every finite or infinite family, closure, circuit, rank,
DA, and HT predicate; no independence or finiteness assumption is imposed on the adjoined set. -/
theorem differentialMatroidOverDifferentialAdjoin_eq_of_differentialAlgebraicOver
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    differentialMatroidOverDifferentialAdjoin F E G =
      differentialMatroid F E := by
  apply Matroid.ext_indep
  · simp [differentialMatroid_ground]
  · intro I _
    rw [differentialMatroidOverDifferentialAdjoin_indep_iff,
      differentialMatroid_indep_iff]
    exact diffIndepOn_differentialAdjoin_iff_of_differentialAlgebraicOver hG

/-- **DA contraction is deletion.** Contracting an arbitrary, possibly infinite and dependent,
set of elements individually differentially algebraic over the base has no rank effect: it is
exactly deletion of those loop directions. -/
theorem differentialMatroid_contract_eq_delete_of_differentialAlgebraicOver
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    differentialMatroid F E ／ G = differentialMatroid F E ＼ G := by
  rw [differentialMatroid_contract_eq_delete_differentialMatroidOverDifferentialAdjoin,
    differentialMatroidOverDifferentialAdjoin_eq_of_differentialAlgebraicOver hG]

/-- **Arbitrary differential-algebraic base-change law.**  Adjoining any set of elements that
are individually differentially algebraic over the coefficient field preserves differential
independence of every indexed family. -/
theorem DifferentialIndependent.extendScalarsDifferentialAdjoin
    {F E : Type u} {ι : Type v} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} {G : Set E} (hx : DifferentialIndependent F x)
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DifferentialIndependent (differentialAdjoin F G) x := by
  classical
  let e : ι ≃ Set.range x := Equiv.ofInjective x hx.injective
  have hRange : DiffIndepOn F (Set.range x) := by
    change DifferentialIndependent F (Subtype.val : Set.range x → E)
    have h := hx.comp e.symm e.symm.injective
    simpa [e] using h
  have hRangeBase :=
    diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver hRange hG
  have h := hRangeBase.comp e e.injective
  simpa [e] using! h

/-- **Exact family-level differential-algebraic base change.** Adjoining an arbitrary set of
differentially algebraic coefficients preserves and reflects joint differential independence of
every indexed family. -/
theorem differentialIndependent_differentialAdjoin_iff
    {F E : Type u} {ι : Type v} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} {G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DifferentialIndependent (differentialAdjoin F G) x ↔
      DifferentialIndependent F x := by
  constructor
  · exact DifferentialIndependent.restrictScalars
  · exact fun hx ↦
      DifferentialIndependent.extendScalarsDifferentialAdjoin hx hG

/-- **Differential-algebraic base-change law.**  Adjoining one differentially algebraic element
to the coefficient field preserves differential independence of an arbitrary indexed family. -/
theorem DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} {g : E} (hx : DifferentialIndependent F x)
    (hg : DifferentialAlgebraicOver F g) :
    DifferentialIndependent (differentialAdjoin F ({g} : Set E)) x := by
  classical
  let e : ι ≃ Set.range x := Equiv.ofInjective x hx.injective
  have hRange : DiffIndepOn F (Set.range x) := by
    change DifferentialIndependent F
      (Subtype.val : Set.range x → E)
    have h := hx.comp e.symm e.symm.injective
    simpa [e] using h
  have hRangeBase :
      DiffIndepOn (differentialAdjoin F ({g} : Set E)) (Set.range x) :=
    diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver hg hRange
  have h := hRangeBase.comp e e.injective
  simpa [e] using! h

/-- Hypertranscendence is unchanged after adjoining an arbitrary set of differentially algebraic
coefficients. -/
theorem hypertranscendentalOver_differentialAdjoin_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : E} {G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    HypertranscendentalOver (differentialAdjoin F G) x ↔
      HypertranscendentalOver F x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    hypertranscendentalOver_iff_differentialIndependent_singleton]
  constructor
  · exact DifferentialIndependent.restrictScalars
  · exact fun hx ↦
      DifferentialIndependent.extendScalarsDifferentialAdjoin hx hG

/-- Differential algebraicity is unchanged after adjoining an arbitrary set of coefficients
that are individually differentially algebraic over the original field. -/
theorem differentialAlgebraicOver_differentialAdjoin_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : E} {G : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DifferentialAlgebraicOver (differentialAdjoin F G) x ↔
      DifferentialAlgebraicOver F x := by
  simpa only [HypertranscendentalOver, not_not] using
    not_congr (hypertranscendentalOver_differentialAdjoin_iff hG)

/-- **Relative DA base-change law.** Differentially algebraic coefficients remain invisible after
adjoining an arbitrary observation set: adjoining `G` before `S` does not change differential
algebraicity over the field generated by `S`. -/
theorem differentialAlgebraicOver_iteratedDifferentialAdjoin_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : E} {G S : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    DifferentialAlgebraicOver
        (differentialAdjoin (differentialAdjoin F G) S) x ↔
      DifferentialAlgebraicOver (differentialAdjoin F S) x := by
  letI : Differential ↥(differentialAdjoin F S) :=
    derivationClosedDifferential _ (derivationClosed_differentialAdjoin F S)
  letI : DifferentialAlgebra ↥(differentialAdjoin F S) E :=
    ⟨fun c ↦ derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F S) c⟩
  have hGS : ∀ g ∈ G,
      DifferentialAlgebraicOver (differentialAdjoin F S) g :=
    fun g hg ↦ differentialAlgebraicOver_mono (hG g hg)
  have h := differentialAlgebraicOver_differentialAdjoin_iff
    (F := differentialAdjoin F S) (E := E) (G := G) (x := x) hGS
  rw [← differentialAlgebraicOver_union_iff_nested (F := F) S G x] at h
  rw [Set.union_comm] at h
  rw [differentialAlgebraicOver_union_iff_nested (F := F) G S x] at h
  exact h

/-- **Relative HT base-change law.** The same arbitrary differentially algebraic coefficient
extension preserves and reflects hypertranscendence over every generated observation field. -/
theorem hypertranscendentalOver_iteratedDifferentialAdjoin_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : E} {G S : Set E} (hG : ∀ g ∈ G, DifferentialAlgebraicOver F g) :
    HypertranscendentalOver
        (differentialAdjoin (differentialAdjoin F G) S) x ↔
      HypertranscendentalOver (differentialAdjoin F S) x := by
  simpa only [HypertranscendentalOver] using not_congr
    (differentialAlgebraicOver_iteratedDifferentialAdjoin_iff
      (F := F) (E := E) (x := x) (G := G) (S := S) hG)

/-- **Differential-algebraic base-change equivalence.**  Adjoining one differentially algebraic
coefficient does not change whether an element is hypertranscendental. -/
theorem hypertranscendentalOver_differentialAdjoinSingleton_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x g : E} (hg : DifferentialAlgebraicOver F g) :
    HypertranscendentalOver (differentialAdjoin F ({g} : Set E)) x ↔
      HypertranscendentalOver F x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    hypertranscendentalOver_iff_differentialIndependent_singleton]
  constructor
  · exact DifferentialIndependent.restrictScalars
  · exact fun hx ↦
      DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton hx hg

end

end GaloisForLFunctions.HTGeometry
