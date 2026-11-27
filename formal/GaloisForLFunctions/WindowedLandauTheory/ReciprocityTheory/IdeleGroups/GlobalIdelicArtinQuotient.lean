import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.GlobalIdelicArtin

/-! The compact idelic quotient maps onto the maximal abelian Galois
group. Surjectivity on every finite subextension gives a directed
family of nonempty compact fibres. -/

noncomputable section

open Topology IntermediateField

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "𝒜" => finiteAbelianExtensions K Ω
local notation "M" => maximalAbelianExtension K Ω

omit [NumberField K] in
private theorem restrictAbPi_eq_of_le {L L' : 𝒜} (h : (L : IntermediateField K Ω) ≤ L')
    {g g' : M ≃ₐ[K] M} (hg : restrictAbPi K Ω g L' = restrictAbPi K Ω g' L') :
    restrictAbPi K Ω g L = restrictAbPi K Ω g' L := by
  letI := L.2.2
  letI := L'.2.2
  ext x
  have he := congrArg (fun σ : (L' : IntermediateField K Ω) ≃ₐ[K] (L' : IntermediateField K Ω) =>
    (σ ⟨x, h x.2⟩ : Ω)) hg
  simpa only [restrictAbPi, restrictAb_apply, Subtype.mk.injEq] using he

omit [NumberField K] in
private theorem surjective_of_compact_finite_restrictions {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (a : B → (M ≃ₐ[K] M)) (ha : Continuous a)
    (hf : ∀ L : 𝒜, Function.Surjective fun x => restrictAbPi K Ω (a x) L) :
    Function.Surjective a := by
  intro σ
  haveI : Nonempty 𝒜 := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let S (L : 𝒜) := {x : B | restrictAbPi K Ω (a x) L = restrictAbPi K Ω σ L}
  have hc (L : 𝒜) : IsClosed (S L) := by
    letI := L.2.2
    letI : T2Space ((L : IntermediateField K Ω) ≃ₐ[K] (L : IntermediateField K Ω)) :=
      krullTopology_t2
    exact isClosed_eq
      ((continuous_apply L).comp ((continuous_restrictAbPi (F := K) (Ω := Ω)).comp ha))
      continuous_const
  have hd : Directed (· ⊇ ·) S := by
    intro L L'
    letI := L.2.1
    letI := L.2.2
    letI := L'.2.1
    letI := L'.2.2
    let F := (L : IntermediateField K Ω) ⊔ (L' : IntermediateField K Ω)
    have hF : F ≤ M := sup_le (le_maximalAbelianExtension _) (le_maximalAbelianExtension _)
    let T : 𝒜 := ⟨F, inferInstance, isAbelianGalois_of_le_maximalAbelianExtension F hF⟩
    exact ⟨T, fun _ h => restrictAbPi_eq_of_le K Ω le_sup_left h,
      fun _ h => restrictAbPi_eq_of_le K Ω le_sup_right h⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hd (fun L => hf L _) (fun L => (hc L).isCompact) hc
  exact ⟨x, injective_restrictAbPi (funext fun L => Set.mem_iInter.mp hx L)⟩

theorem exists_open_quotient_global_idelic_artin :
    ∃ a : CompactIdeleClassQuotient K →* (M ≃ₐ[K] M), IsOpenQuotientMap a ∧ MatchesFiniteIdelicArtin K Ω a := by
  obtain ⟨a, ha, hArtin, hf⟩ := exists_global_idelic_artin K Ω
  have hs := surjective_of_compact_finite_restrictions K Ω a ha hf
  letI : T2Space (M ≃ₐ[K] M) := krullTopology_t2
  let e := QuotientGroup.quotientKerEquivOfSurjective a hs
  have he : Continuous e :=
    (QuotientGroup.isQuotientMap_mk a.ker).continuous_iff.mpr ha
  let E := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact ⟨a, ⟨hs, ha, E.isOpenMap.comp QuotientGroup.isOpenMap_coe⟩, hArtin⟩

end GlobalTheory.Reciprocity
