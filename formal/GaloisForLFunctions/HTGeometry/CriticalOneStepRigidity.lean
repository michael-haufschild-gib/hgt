import GaloisForLFunctions.HTGeometry.CriticalFreeParameterPrimitivity
import GaloisForLFunctions.HTGeometry.CriticalRecipMemSourceSup

/-!
# One-step postcritical rigidity

A primitive finite extension stays primitive after adjoining an independent transcendental, so a
single element of the extended extension which is not already in the extended base generates
everything: the free parameter together with one escaping element recovers the whole source.

For the critical jet tower this says that the observation field, the new raw coordinate and the new
reciprocal coordinate generate the source field extended by the new raw coordinate.  The escape of
the reciprocal coordinate is unconditional, and the primitivity input is full geometric monodromy.
-/

open IntermediateField

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Two generators suffice after a transcendental base change.**  If the finite Galois extension
`B/F` contains the source `A` as a primitive step and `t` is transcendental over `A`, then any
element of `A(t)` outside `F(t)` generates `A(t)` over `F` together with `t`. -/
theorem adjoin_pair_eq_top_of_primitive_of_notMem
    {F A B Ω : Type*} [Field F] [Field A] [Field B] [Field Ω]
    [Algebra F A] [Algebra F B] [Algebra A Ω] [Algebra F Ω] [IsScalarTower F A Ω]
    [FiniteDimensional F B] [IsGalois F B]
    (φ : A →ₐ[F] B)
    (hprim : ∀ P : IntermediateField F B, P ≤ φ.fieldRange → P = ⊥ ∨ P = φ.fieldRange)
    {t : Ω} (ht : Transcendental A t)
    (y : ↥(IntermediateField.adjoin A {t}))
    (hy : (y : Ω) ∉ IntermediateField.adjoin F {t}) :
    IntermediateField.adjoin F
        ({⟨t, IntermediateField.mem_adjoin_simple_self A t⟩, y} :
          Set ↥(IntermediateField.adjoin A {t}))
      = ⊤ := by
  classical
  have hkey := adjoin_eq_map_of_primitive_of_notMem φ hprim ht y hy
  have hself := adjoinToFrac_apply_self φ ht
  have hmapW : (IntermediateField.adjoin F
        ({⟨t, IntermediateField.mem_adjoin_simple_self A t⟩, y} :
          Set ↥(IntermediateField.adjoin A {t}))).map (adjoinToFrac φ ht)
      = IntermediateField.adjoin F
        ({fracX B, adjoinToFrac φ ht y} : Set (FractionRing (Polynomial B))) := by
    rw [IntermediateField.adjoin_map]
    congr 1
    rw [Set.image_insert_eq, Set.image_singleton, hself]
  refine eq_top_iff.2 fun a _ => ?_
  have h1 : adjoinToFrac φ ht a
      ∈ IntermediateField.adjoin ↥(IntermediateField.adjoin F {fracX B})
        {adjoinToFrac φ ht y} := by
    rw [hkey]
    exact fracMap_mem_adjoin φ ((fracRealizeEquiv ht).symm a)
  have h2 : adjoinToFrac φ ht a
      ∈ IntermediateField.adjoin F
        ({fracX B, adjoinToFrac φ ht y} : Set (FractionRing (Polynomial B))) := by
    have hres : (IntermediateField.adjoin ↥(IntermediateField.adjoin F {fracX B})
          {adjoinToFrac φ ht y}).restrictScalars F
        = IntermediateField.adjoin F
          ((IntermediateField.adjoin F {fracX B} : Set (FractionRing (Polynomial B)))
            ∪ {adjoinToFrac φ ht y}) :=
      IntermediateField.restrictScalars_adjoin F _ _
    have h1' : adjoinToFrac φ ht a
        ∈ IntermediateField.adjoin F
          ((IntermediateField.adjoin F {fracX B} : Set (FractionRing (Polynomial B)))
            ∪ {adjoinToFrac φ ht y}) := by
      rw [← hres]
      exact h1
    refine (IntermediateField.adjoin_le_iff.2 ?_) h1'
    rintro z (hz | hz)
    · have hz' : z ∈ IntermediateField.adjoin F {fracX B} := hz
      refine (IntermediateField.adjoin_le_iff.2 ?_) hz'
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      exact IntermediateField.subset_adjoin F _ (by rw [hw]; exact Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact IntermediateField.subset_adjoin F _ (Or.inr rfl)
  rw [← hmapW] at h2
  obtain ⟨w, hw, hwa⟩ := (IntermediateField.mem_map _).1 h2
  rwa [adjoinToFrac_injective φ ht hwa] at hw

/-- Membership in a field generated inside an intermediate field pushes forward to the ambient
field. -/
theorem mem_adjoin_image_of_mem_adjoin_subtype
    {F A Ω : Type*} [Field F] [Field A] [Field Ω] [Algebra F A] [Algebra A Ω] [Algebra F Ω]
    [IsScalarTower F A Ω] {T : IntermediateField A Ω} {S : Set ↥T} {z : ↥T}
    (hz : z ∈ IntermediateField.adjoin F S) :
    (z : Ω) ∈ IntermediateField.adjoin F (((↑) : ↥T → Ω) '' S) := by
  have hmap := (IntermediateField.mem_map
    (f := AlgHom.restrictScalars F T.val)
    (IntermediateField.adjoin F S)).2 ⟨z, hz, rfl⟩
  rwa [IntermediateField.adjoin_map] at hmap

/-- Membership in a field generated over an intermediate field is membership in the field generated
by that intermediate field together with the generators. -/
theorem mem_adjoin_union_of_mem_adjoin_intermediate
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (O : IntermediateField F Ω) (S : Set Ω) {x : Ω}
    (hx : x ∈ IntermediateField.adjoin ↥O S) :
    x ∈ IntermediateField.adjoin F ((O : Set Ω) ∪ S) := by
  rw [← IntermediateField.restrictScalars_adjoin F O S]
  exact hx

/-- **One-step postcritical rigidity.**  Under full geometric monodromy the critical observation
field, the new raw coordinate and the new reciprocal coordinate generate exactly the critical source
field extended by the new raw coordinate: one postcritical reciprocal coefficient recovers the whole
source over the observation field with its free parameter. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfull : criticalGeometricMonodromy K m n = ⊤) :
    criticalObservationField K m n
        ⊔ IntermediateField.adjoin K {postcriticalRawFieldElement K m n}
        ⊔ IntermediateField.adjoin K {postcriticalReciprocalFieldElement K m n}
      = criticalSourceFieldSup K m n := by
  classical
  letI : IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (genericJetField K (m + n)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  letI : IsScalarTower (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  letI : Normal (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : IsGalois (criticalObservationField K m n)
      (criticalNormalClosure K m n) := inferInstance
  have ht := postcriticalRawFieldElement_transcendental_criticalSourceField K m n
  have hymem : postcriticalReciprocalFieldElement K m n
      ∈ IntermediateField.adjoin ↥(criticalSourceField K m n)
        {postcriticalRawFieldElement K m n} :=
    mem_adjoin_of_mem_sup _ _
      (postcriticalReciprocalFieldElement_mem_criticalSourceFieldSup K m n)
  have hynot : postcriticalReciprocalFieldElement K m n
      ∉ IntermediateField.adjoin ↥(criticalObservationField K m n)
        {postcriticalRawFieldElement K m n} := fun h =>
    postcriticalReciprocalFieldElement_notMem_criticalObservation_sup_raw K hm hn
      (mem_sup_of_mem_adjoin _ _ h)
  have htop := adjoin_pair_eq_top_of_primitive_of_notMem
    (criticalSourceNormalClosureEmbedding K m n)
    (eq_bot_or_eq_criticalSourceNormalClosureFieldRange_of_full_monodromy K hm hn hfull)
    ht ⟨postcriticalReciprocalFieldElement K m n, hymem⟩ hynot
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (criticalObservationField_le_criticalSourceField K).trans
        (le_sup_left (α := IntermediateField K (genericJetField K (m + n))))
    · exact le_sup_right (α := IntermediateField K (genericJetField K (m + n)))
    · refine IntermediateField.adjoin_le_iff.2 ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact postcriticalReciprocalFieldElement_mem_criticalSourceFieldSup K m n
  · intro x hx
    have hx' : x ∈ IntermediateField.adjoin ↥(criticalSourceField K m n)
        {postcriticalRawFieldElement K m n} := mem_adjoin_of_mem_sup _ _ hx
    have hmem : (⟨x, hx'⟩ : ↥(IntermediateField.adjoin ↥(criticalSourceField K m n)
          {postcriticalRawFieldElement K m n}))
        ∈ IntermediateField.adjoin ↥(criticalObservationField K m n)
          ({⟨postcriticalRawFieldElement K m n,
              IntermediateField.mem_adjoin_simple_self _ _⟩,
            ⟨postcriticalReciprocalFieldElement K m n, hymem⟩} :
            Set ↥(IntermediateField.adjoin ↥(criticalSourceField K m n)
              {postcriticalRawFieldElement K m n})) := by
      rw [htop]
      trivial
    have himg : x ∈ IntermediateField.adjoin ↥(criticalObservationField K m n)
        ({postcriticalRawFieldElement K m n, postcriticalReciprocalFieldElement K m n} :
          Set (genericJetField K (m + n))) := by
      have h0 := mem_adjoin_image_of_mem_adjoin_subtype
        (F := ↥(criticalObservationField K m n)) hmem
      rw [Set.image_insert_eq, Set.image_singleton] at h0
      exact h0
    have hx'' : x ∈ IntermediateField.adjoin K
        ((criticalObservationField K m n : Set (genericJetField K (m + n)))
          ∪ {postcriticalRawFieldElement K m n, postcriticalReciprocalFieldElement K m n}) :=
      mem_adjoin_union_of_mem_adjoin_intermediate _ _ himg
    refine (IntermediateField.adjoin_le_iff.2 ?_) hx''
    rintro z (hz | hz)
    · exact (le_sup_left (α := IntermediateField K (genericJetField K (m + n)))).trans
        (le_sup_left (α := IntermediateField K (genericJetField K (m + n)))) hz
    · rcases hz with hz | hz
      · refine (le_sup_right (α := IntermediateField K (genericJetField K (m + n)))).trans
          (le_sup_left (α := IntermediateField K (genericJetField K (m + n)))) ?_
        rw [hz]
        exact IntermediateField.subset_adjoin _ _ rfl
      · rw [Set.mem_singleton_iff] at hz
        refine le_sup_right (α := IntermediateField K (genericJetField K (m + n))) ?_
        rw [hz]
        exact IntermediateField.subset_adjoin _ _ rfl


end GaloisForLFunctions.HTGeometry

end
