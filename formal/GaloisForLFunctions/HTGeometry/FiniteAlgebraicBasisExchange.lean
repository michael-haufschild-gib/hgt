import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite algebraic coordinate-frame exchange

An algebraically independent family has the expected transcendence degree in its generated field.
Consequently, if a field is algebraic over one finite independent coordinate frame, it is algebraic
over every independent frame with the same finite cardinality.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- An algebraically independent family is a transcendence basis of the ordinary field that it
generates, so the transcendence degree of that field is exactly the cardinality of the family. -/
theorem trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent
    {F E I : Type u} [Field F] [Field E] [Algebra F E]
    (x : I → E) (hx : AlgebraicIndependent F x) :
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range x)) = Cardinal.mk I := by
  let L := IntermediateField.adjoin F (Set.range x)
  let xL : I → L := fun i =>
    ⟨x i, IntermediateField.subset_adjoin F (Set.range x) (Set.mem_range_self i)⟩
  have hxL : AlgebraicIndependent F xL := by
    apply AlgebraicIndependent.of_comp (L.val : L →ₐ[F] E)
    simpa only [Function.comp_apply, L, xL] using! hx
  have htop : IntermediateField.adjoin F (Set.range xL) = ⊤ := by
    let J := IntermediateField.adjoin F (Set.range xL)
    apply top_unique
    intro z hz
    change z ∈ J
    let p : ∀ y, y ∈ L → Prop := fun y hy => (⟨y, hy⟩ : L) ∈ J
    change p (z : E) z.2
    refine IntermediateField.adjoin_induction F (p := p) ?_ ?_ ?_ ?_ ?_ z.2
    · rintro y ⟨i, rfl⟩
      change xL i ∈ J
      exact IntermediateField.subset_adjoin F (Set.range xL) (Set.mem_range_self i)
    · intro c
      change algebraMap F L c ∈ J
      exact IntermediateField.algebraMap_mem J c
    · intro a b ha hb haJ hbJ
      simpa only [p, Subtype.coe_eta] using! J.add_mem haJ hbJ
    · intro a ha haJ
      simpa only [p, Subtype.coe_eta] using! J.inv_mem haJ
    · intro a b ha hb haJ hbJ
      simpa only [p, Subtype.coe_eta] using! J.mul_mem haJ hbJ
  have halg : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range xL)) L := by
    constructor
    intro a
    apply GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_mem_intermediateField_adjoin
    rw [htop]
    trivial
  have hbasis : IsTranscendenceBasis F xL :=
    hxL.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  simpa only [L] using hbasis.cardinalMk_eq_trdeg.symm

/-- A finite algebraically independent frame whose size equals the ambient transcendence degree is
a transcendence basis: the ambient field is algebraic over its generated field. -/
theorem isAlgebraic_adjoin_of_algebraicIndependent_fin_of_trdeg_eq
    {C A : Type} [Field C] [Field A] [Algebra C A] {n : ℕ}
    (y : Fin n → A) (hy : AlgebraicIndependent C y)
    (hAtr : Algebra.trdeg C A = n) :
    Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range y)) A := by
  let L := IntermediateField.adjoin C (Set.range y)
  have hytr : Algebra.trdeg C L = n := by
    simpa using
      trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent y hy
  have hysum := trdeg_add_eq C L (A := A)
  rw [hytr, hAtr] at hysum
  have hzero : Algebra.trdeg L A = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hysum with hlarge | hzero
    · have hfinite : (n : Cardinal) < Cardinal.aleph0 := by
        simp
      exact False.elim ((not_le_of_gt hfinite)
        (le_trans (le_max_left Cardinal.aleph0 (Algebra.trdeg L A)) hlarge))
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- If a field is algebraic over one `n`-element algebraically independent coordinate frame, then
it is algebraic over every other `n`-element algebraically independent coordinate frame. -/
theorem isAlgebraic_adjoin_of_algebraicIndependent_fin
    {C A : Type} [Field C] [Field A] [Algebra C A] {n : ℕ}
    (x y : Fin n → A) (hx : AlgebraicIndependent C x)
    (hy : AlgebraicIndependent C y)
    [Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range x)) A] :
    Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range y)) A := by
  let E := IntermediateField.adjoin C (Set.range x)
  have hxtr : Algebra.trdeg C E = n := by
    simpa using
      trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent x hx
  letI : Algebra.IsAlgebraic E A := inferInstance
  have hxzero : Algebra.trdeg E A = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have hxsum := trdeg_add_eq C E (A := A)
  have hAtr : Algebra.trdeg C A = n := by
    rw [hxtr, hxzero, add_zero] at hxsum
    exact hxsum.symm
  exact isAlgebraic_adjoin_of_algebraicIndependent_fin_of_trdeg_eq y hy hAtr

end GaloisForLFunctions.HTGeometry
