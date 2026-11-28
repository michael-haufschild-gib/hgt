import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteAbelianRestrictions
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentFromInvariantFactor

/-! Over a normal middle field, a finite abelian relative stage lies in
one that is also Galois over the smaller field. The normal closure stays
in the relative maximal abelian extension. -/

noncomputable section

open IntermediateField
open scoped commutatorElement

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (L : IntermediateField K Ω) [Normal K L] [IsGalois L Ω]

theorem normal_restrictScalars_maximalAbelianExtension :
    Normal K ((maximalAbelianExtension L Ω).restrictScalars K) := by
  let r : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let j : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
  let H := r.ker
  let J : Subgroup Gal(Ω/K) := ⁅H, H⁆
  let e := restrictionKernelEquiv K L Ω
  have hj : j.range = H := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact (e.symm s).2
    · intro s hs
      exact ⟨e ⟨s, hs⟩, AlgEquiv.ext fun _ => rfl⟩
  have hJ : (commutator Gal(Ω/L)).map j = J := by
    rw [map_commutator_eq, hj]
  letI : J.Normal := ⟨fun s hs τ => by
    let c := (MulAut.conj τ).toMonoidHom
    have hH : H.map c ≤ H := by
      rintro _ ⟨g, hg, rfl⟩
      exact Subgroup.Normal.conj_mem (inferInstance : H.Normal) g hg τ
    have hc : J.map c ≤ J :=
      (Subgroup.map_commutator H H c).le.trans (Subgroup.commutator_mono hH hH)
    exact hc ⟨s, hs, rfl⟩⟩
  have he : (maximalAbelianExtension L Ω).restrictScalars K = fixedField J := by
    apply IntermediateField.ext
    intro x
    change x ∈ maximalAbelianExtension L Ω ↔ x ∈ fixedField J
    rw [maximalAbelianExtension, mem_fixedField_iff, mem_fixedField_iff, ← hJ]
    constructor
    · intro hx t ht
      obtain ⟨s, hs, he⟩ := Subgroup.mem_map.mp ht
      rw [← he]
      exact hx s (Subgroup.le_topologicalClosure _ hs)
    · intro hx s hs
      let S := MulAction.stabilizer Gal(Ω/L) x
      have hS : IsClosed (S : Set Gal(Ω/L)) := S.isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral x)
      have hsub : commutator Gal(Ω/L) ≤ S := fun z hz => hx (j z) ⟨z, hz, rfl⟩
      exact (Subgroup.topologicalClosure_minimal _ hsub hS) hs
  rw [he]
  exact (IsGalois.of_fixedField_normal_subgroup J).to_normal

theorem normalClosure_restrictScalars_le_maximalAbelianExtension
    (V : IntermediateField L Ω) [IsAbelianGalois L V] :
    normalClosure K (V.restrictScalars K) Ω ≤ (maximalAbelianExtension L Ω).restrictScalars K := by
  letI := normal_restrictScalars_maximalAbelianExtension L
  exact IntermediateField.normalClosure_le_iff_of_normal.mpr (le_maximalAbelianExtension V)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.normal_restrictScalars_maximalAbelianExtension
#print axioms GlobalTheory.Reciprocity.normalClosure_restrictScalars_le_maximalAbelianExtension
