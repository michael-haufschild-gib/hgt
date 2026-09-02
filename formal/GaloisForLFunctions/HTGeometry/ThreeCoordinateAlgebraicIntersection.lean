import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableFactorization
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic

/-!
# Relative algebraic closures of independent coordinate pairs

For three algebraically independent coordinates, an element algebraic over each of two coordinate
pair fields sharing one coordinate is already algebraic over that common coordinate field.  This
is the regular-intersection identity needed by the three-field rank-one factorization.

The proof is the exchange-property argument made exact through mathlib's algebraic matroid: closure
commutes with intersection on subsets of one independent set.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Common-coordinate closure for any independent family.**  Two two-coordinate algebraic
closures with distinct transverse coordinates intersect inside the algebraic closure of their
common coordinate. -/
theorem isAlgebraic_over_commonCoordinate_of_independent
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    (v : ι → E) (hv : AlgebraicIndependent F v) {i j k : ι} (hjk : j ≠ k) {q : E}
    (hij : IsAlgebraic (IntermediateField.adjoin F (v '' ({i, j} : Set ι))) q)
    (hik : IsAlgebraic (IntermediateField.adjoin F (v '' ({i, k} : Set ι))) q) :
    IsAlgebraic (IntermediateField.adjoin F ({v i} : Set E)) q := by
  let M : Matroid E := AlgebraicIndependent.matroid F E
  have hfull : M.Indep (Set.range v) := by
    apply AlgebraicIndependent.matroid_indep_iff.mpr
    exact hv.to_subtype_range
  have hsub : v '' ({i, j} : Set ι) ∪ v '' ({i, k} : Set ι) ⊆ Set.range v := by
    intro e he
    rcases he with he | he
    · obtain ⟨a, _, rfl⟩ := he
      exact ⟨a, rfl⟩
    · obtain ⟨a, _, rfl⟩ := he
      exact ⟨a, rfl⟩
  have hu : M.Indep (v '' ({i, j} : Set ι) ∪ v '' ({i, k} : Set ι)) :=
    hfull.mono hsub
  have hinter : v '' ({i, j} : Set ι) ∩ v '' ({i, k} : Set ι) = {v i} := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      rcases ha with rfl | rfl
      · rfl
      · rcases hb with rfl | rfl
        · exact hab.symm
        · exact False.elim (hjk (hv.injective hab).symm)
    · intro he
      subst e
      exact ⟨⟨i, Or.inl rfl, rfl⟩, ⟨i, Or.inl rfl, rfl⟩⟩
  have hqij : q ∈ M.closure (v '' ({i, j} : Set ι)) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact (Subalgebra.mem_algebraicClosure _ _).mpr
      (GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField _ hij)
  have hqik : q ∈ M.closure (v '' ({i, k} : Set ι)) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact (Subalgebra.mem_algebraicClosure _ _).mpr
      (GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField _ hik)
  have hq : q ∈ M.closure ({v i} : Set E) := by
    rw [← hinter, hu.closure_inter_eq_inter_closure]
    exact ⟨hqij, hqik⟩
  rw [AlgebraicIndependent.matroid_closure_eq] at hq
  exact GaloisForLFunctions.isAlgebraic_intermediateField_of_isAlgebraic_algebraAdjoin _
    ((Subalgebra.mem_algebraicClosure _ _).mp hq)

/-- **Regular intersection of two independent coordinate-pair algebraic closures.** -/
theorem isAlgebraic_over_commonCoordinate_of_threeCoordinate
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : Fin 3 → E) (hv : AlgebraicIndependent F v) {q : E}
    (h01 : IsAlgebraic (IntermediateField.adjoin F (v '' ({0, 1} : Set (Fin 3)))) q)
    (h02 : IsAlgebraic (IntermediateField.adjoin F (v '' ({0, 2} : Set (Fin 3)))) q) :
    IsAlgebraic (IntermediateField.adjoin F ({v 0} : Set E)) q := by
  let M : Matroid E := AlgebraicIndependent.matroid F E
  have hfull : M.Indep (Set.range v) := by
    apply AlgebraicIndependent.matroid_indep_iff.mpr
    exact hv.to_subtype_range
  have hsub : v '' ({0, 1} : Set (Fin 3)) ∪ v '' ({0, 2} : Set (Fin 3)) ⊆ Set.range v := by
    intro e he
    rcases he with he | he
    · obtain ⟨i, _, rfl⟩ := he
      exact ⟨i, rfl⟩
    · obtain ⟨i, _, rfl⟩ := he
      exact ⟨i, rfl⟩
  have hu : M.Indep (v '' ({0, 1} : Set (Fin 3)) ∪ v '' ({0, 2} : Set (Fin 3))) :=
    hfull.mono hsub
  have hinter : v '' ({0, 1} : Set (Fin 3)) ∩ v '' ({0, 2} : Set (Fin 3)) = {v 0} := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, hij⟩⟩
      rcases hi with rfl | rfl
      · rfl
      · rcases hj with rfl | rfl
        · exact hij.symm
        · exact False.elim (by
            have hfin : (2 : Fin 3) = 1 := hv.injective hij
            have hnat : (2 : ℕ) = 1 := congrArg Fin.val hfin
            omega)
    · intro he
      subst e
      exact ⟨⟨0, Or.inl rfl, rfl⟩, ⟨0, Or.inl rfl, rfl⟩⟩
  have hq01 : q ∈ M.closure (v '' ({0, 1} : Set (Fin 3))) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact (Subalgebra.mem_algebraicClosure _ _).mpr
      (GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField _ h01)
  have hq02 : q ∈ M.closure (v '' ({0, 2} : Set (Fin 3))) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact (Subalgebra.mem_algebraicClosure _ _).mpr
      (GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField _ h02)
  have hq : q ∈ M.closure ({v 0} : Set E) := by
    rw [← hinter, hu.closure_inter_eq_inter_closure]
    exact ⟨hq01, hq02⟩
  rw [AlgebraicIndependent.matroid_closure_eq] at hq
  exact GaloisForLFunctions.isAlgebraic_intermediateField_of_isAlgebraic_algebraAdjoin _
    ((Subalgebra.mem_algebraicClosure _ _).mp hq)

end

end GaloisForLFunctions.HTGeometry
