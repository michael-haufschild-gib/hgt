import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import GaloisForLFunctions.HTGeometry.DifferentialMatroidFiniteClosure
import GaloisForLFunctions.HTGeometry.MatroidNatRank
import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction

/-!
# Differential transcendence rank for the gluing engine

The genuine differential matroid supplies the natural rank used by the orbit-gluing theorems.
Consequently, `Rank.IndepSet` for this rank is exactly differential independence, rather than an
abstract rank hypothesis.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set
open MatroidGluing

noncomputable section

universe u

/-- Differential transcendence rank on finite subsets of a differential field extension. -/
def differentialRank
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] : Rank E :=
  matroidRank (differentialMatroid F E)

/-- Independence in the differential rank is exactly differential independence. -/
theorem differentialRank_indepSet_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] {S : Set E} :
    (differentialRank F E).IndepSet S ↔ DiffIndepOn F S := by
  rw [differentialRank, matroidRank_indepSet_iff, differentialMatroid_indep_iff]

namespace HTGeometry.DifferentialAlgEquiv

/-- A coefficient-fixing differential automorphism carries every differentially independent set
to a differentially independent image. -/
theorem diffIndepOn_image
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) {S : Set E} (hS : DiffIndepOn F S) :
    DiffIndepOn F (σ.toAlgEquiv '' S) := by
  let e : S ≃ σ.toAlgEquiv '' S :=
    Equiv.Set.imageOfInjOn σ.toAlgEquiv S σ.toAlgEquiv.injective.injOn
  have hmap := σ.differentialIndependent_map hS
  apply (differentialIndependent_equiv e
    (Subtype.val : σ.toAlgEquiv '' S → E)).mp
  simpa [e, Equiv.Set.imageOfInjOn] using! hmap

/-- Differential independence is invariant under a coefficient-fixing differential automorphism. -/
theorem diffIndepOn_image_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : DifferentialAlgEquiv F E) (S : Set E) :
    DiffIndepOn F (σ.toAlgEquiv '' S) ↔ DiffIndepOn F S := by
  constructor
  · intro h
    have hback := σ.symm.diffIndepOn_image h
    have heq : σ.symm.toAlgEquiv '' (σ.toAlgEquiv '' S) = S := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa [DifferentialAlgEquiv.symm] using hz
      · intro hx
        exact ⟨σ.toAlgEquiv x, ⟨x, hx, rfl⟩, by
          simp [DifferentialAlgEquiv.symm]⟩
    rwa [heq] at hback
  · exact σ.diffIndepOn_image

end HTGeometry.DifferentialAlgEquiv

/-- A coefficient-fixing differential automorphism is an automorphism of the differential
matroid. -/
theorem differentialMatroid_mapEquiv_differentialAlgEquiv
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (σ : HTGeometry.DifferentialAlgEquiv F E) :
    (differentialMatroid F E).mapEquiv σ.toAlgEquiv.toEquiv =
      differentialMatroid F E := by
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [Matroid.mapEquiv_indep_iff, differentialMatroid_indep_iff,
      differentialMatroid_indep_iff]
    simpa [HTGeometry.DifferentialAlgEquiv.symm] using
      (σ.symm.diffIndepOn_image_iff I)

/-- Every coefficient-fixing differential automorphism preserves the genuine differential rank. -/
theorem HTGeometry.DifferentialAlgEquiv.mem_differentialRank_rankAutSubgroup
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] (σ : HTGeometry.DifferentialAlgEquiv F E) :
    σ.toAlgEquiv.toEquiv ∈ (differentialRank F E).rankAutSubgroup := by
  apply matroidRank_mem_rankAutSubgroup_of_mapEquiv_eq
  exact differentialMatroid_mapEquiv_differentialAlgEquiv σ

/-- Off-face differential algebraicity of every translated finite packet is exactly the concrete
input needed for rank-neutrality in the gluing engine. -/
theorem differentialRank_crossNeutral_of_image_differentialAlgebraic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] (e : Equiv.Perm E) (S : Set E)
    (hDA : ∀ t : Finset E, (↑t : Set E) ⊆ S → ∀ n : ℤ, ∀ z,
      z ∈ (↑(t.image ⇑(e ^ n)) : Set E) →
        DifferentialAlgebraicOver (differentialAdjoin F (↑t : Set E)) z) :
    (differentialRank F E).CrossNeutral e S := by
  apply matroidRank_crossNeutral_of_image_subset_closure
    (differentialMatroid F E) (by simp) e S
  intro t ht n z hz
  by_cases ht0 : t = ∅
  · subst t
    simp at hz
  letI : Nonempty t := Finset.nonempty_coe_sort.mpr (Finset.nonempty_iff_ne_empty.mpr ht0)
  obtain ⟨m, ⟨q⟩⟩ := Finite.exists_equiv_fin t
  cases m with
  | zero =>
      exact False.elim (Fin.elim0 (q (Classical.choice (inferInstance : Nonempty t))))
  | succ k =>
      let x : Fin (k + 1) → E := Subtype.val ∘ q.symm
      have hrange : Set.range x = (↑t : Set E) := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact (q.symm i).2
        · intro hy
          exact ⟨q ⟨y, hy⟩, by simp [x]⟩
      rw [← hrange]
      apply (differentialMatroid_mem_closure_range_fin_succ_iff
        (F := F) x z).mpr
      rw [hrange]
      exact hDA t ht n z hz

/-- The six-face gluing theorem specialized to genuine differential independence.  The remaining
hypotheses are precisely the analytic star-freeness and off-star differential-algebraicity inputs. -/
theorem differentialRank_orderThree_sixFace_diffIndepOn
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E]
    (O : Fin 4 × Fin 4 → Set E)
    (σ : Fin 4 → HTGeometry.DifferentialAlgEquiv F E)
    (hStarIndep : ∀ q : Fin 4, (differentialRank F E).IndepSet
      (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => q = p.1 ∨ q = p.2), O e))
    (height : Fin 4 → E → ℤ)
    (hStarStable : ∀ q : Fin 4, ∀ x,
      x ∈ (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => q = p.1 ∨ q = p.2), O e) →
      ∀ n : ℤ, ((σ q).toAlgEquiv.toEquiv ^ n) x ∈
        (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
          (fun p => q = p.1 ∨ q = p.2), O e))
    (hStarHeight : ∀ q : Fin 4, ∀ x,
      x ∈ (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => q = p.1 ∨ q = p.2), O e) →
      ∀ n : ℤ, height q (((σ q).toAlgEquiv.toEquiv ^ n) x) = height q x + n)
    (hOffDA : ∀ q : Fin 4, ∀ t : Finset E,
      (↑t : Set E) ⊆
        (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
          (fun p => ¬ (q = p.1 ∨ q = p.2)), O e) →
      ∀ n : ℤ, ∀ z, z ∈ (↑(t.image ⇑((σ q).toAlgEquiv.toEquiv ^ n)) : Set E) →
        DifferentialAlgebraicOver (differentialAdjoin F (↑t : Set E)) z) :
    DiffIndepOn F
      (⋃ e ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), O e) := by
  rw [← differentialRank_indepSet_iff]
  apply Rank.orderThree_sixFace_indep (differentialRank F E) O
    (fun q => (σ q).toAlgEquiv.toEquiv)
  · intro q
    exact (differentialRank F E).freeIndepOrbit_of_indep
      (σ q).mem_differentialRank_rankAutSubgroup (hStarIndep q)
      (Rank.hasFreeTranslates_of_intHeight _ _ (height q)
        (hStarStable q) (hStarHeight q))
  · intro q
    exact differentialRank_crossNeutral_of_image_differentialAlgebraic
      (σ q).toAlgEquiv.toEquiv _ (hOffDA q)

end

end GaloisForLFunctions
