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
local notation "C" => CompactIdeleClassQuotient K

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
/-- On a compact source, having compatible target values in each finite
abelian restriction suffices for having the target value globally. -/
theorem exists_eq_of_compact_finite_restrictions {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (a : B → (M ≃ₐ[K] M)) (ha : Continuous a) (σ : M ≃ₐ[K] M)
    (hf : ∀ L : 𝒜, ∃ x, restrictAbPi K Ω (a x) L = restrictAbPi K Ω σ L) :
    ∃ x, a x = σ := by
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
    S hd hf (fun L => (hc L).isCompact) hc
  exact ⟨x, injective_restrictAbPi (funext fun L => Set.mem_iInter.mp hx L)⟩

theorem exists_open_quotient_global_idelic_artin :
    ∃ a : CompactIdeleClassQuotient K →* (M ≃ₐ[K] M), IsOpenQuotientMap a ∧ MatchesFiniteIdelicArtin K Ω a := by
  obtain ⟨a, ha, hArtin, hf⟩ := exists_global_idelic_artin K Ω
  have hs : Function.Surjective a := fun σ =>
    exists_eq_of_compact_finite_restrictions K Ω a ha σ (fun L => hf L _)
  letI : T2Space (M ≃ₐ[K] M) := krullTopology_t2
  let e := QuotientGroup.quotientKerEquivOfSurjective a hs
  have he : Continuous e :=
    (QuotientGroup.isQuotientMap_mk a.ker).continuous_iff.mpr ha
  let E := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact ⟨a, ⟨hs, ha, E.isOpenMap.comp QuotientGroup.isOpenMap_coe⟩, hArtin⟩

/-- An open subgroup containing the global Artin kernel contains a finite restriction kernel. -/
theorem exists_finite_restriction_kernel_le
    (a : C →* (M ≃ₐ[K] M)) (ha : Continuous a)
    (N : Subgroup C) (hN : IsOpen (N : Set C)) (hker : a.ker ≤ N) :
    ∃ L : 𝒜, ∀ x, restrictAbPi K Ω (a x) L = 1 → x ∈ N := by
  classical
  by_contra! hn
  haveI : Nonempty 𝒜 := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let S (L : 𝒜) := {x : C | x ∉ N ∧ restrictAbPi K Ω (a x) L = 1}
  have hc (L : 𝒜) : IsClosed (S L) := by
    letI := L.2.2
    letI : T2Space ((L : IntermediateField K Ω) ≃ₐ[K] (L : IntermediateField K Ω)) := krullTopology_t2
    exact hN.isClosed_compl.inter (isClosed_eq
      ((continuous_apply L).comp ((continuous_restrictAbPi (F := K) (Ω := Ω)).comp ha))
      continuous_const)
  have hd : Directed (· ⊇ ·) S := by
    intro L L'
    letI := L.2.1
    letI := L.2.2
    letI := L'.2.1
    letI := L'.2.2
    let F := (L : IntermediateField K Ω) ⊔ (L' : IntermediateField K Ω)
    have hF : F ≤ M := sup_le (le_maximalAbelianExtension _) (le_maximalAbelianExtension _)
    let T : 𝒜 := ⟨F, inferInstance, isAbelianGalois_of_le_maximalAbelianExtension F hF⟩
    have restrict_one (V : 𝒜) : restrictAbPi K Ω (1 : M ≃ₐ[K] M) V = 1 := by
      letI := V.2.2
      exact map_one (restrictAb (V : IntermediateField K Ω) (le_maximalAbelianExtension _))
    have hsub (V : 𝒜) (hV : (V : IntermediateField K Ω) ≤ F) : S T ⊆ S V := by
      rintro x ⟨hx, h⟩
      exact ⟨hx, (restrictAbPi_eq_of_le K Ω hV (h.trans (restrict_one T).symm)).trans (restrict_one V)⟩
    exact ⟨T, hsub L le_sup_left, hsub L' le_sup_right⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hd
    (fun L => by obtain ⟨y, hy, hNy⟩ := hn L; exact ⟨y, hNy, hy⟩) (fun L => (hc L).isCompact) hc
  have hmem (L : 𝒜) : x ∈ S L := Set.mem_iInter.mp hx L
  have hxker : a x = 1 := by
    apply injective_restrictAbPi
    funext L
    letI := L.2.2
    exact (hmem L).2.trans (map_one (restrictAb (L : IntermediateField K Ω)
      (le_maximalAbelianExtension _))).symm
  exact (hmem (⟨⊥, inferInstance, inferInstance⟩ : 𝒜)).1 (hker (MonoidHom.mem_ker.mpr hxker))

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_eq_of_compact_finite_restrictions
