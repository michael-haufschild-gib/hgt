import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteAbelianRestrictions

/-! Compatible automorphisms on finite abelian subextensions assemble
uniquely in the Krull topology. Compactness supplies a point in the
intersection of the fibres prescribed by all restrictions. -/

noncomputable section

open IntermediateField

namespace GlobalTheory.Reciprocity

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {B : Type*} [Monoid B] [TopologicalSpace B]

local notation "𝒜" => finiteAbelianExtensions K Ω
local notation "M" => maximalAbelianExtension K Ω

omit [TopologicalSpace B] in
private theorem exists_abelian_restrictions
    (f : ∀ L : 𝒜, B →* ((L : IntermediateField K Ω) ≃ₐ[K] (L : IntermediateField K Ω)))
    (hf : ∀ (L L' : 𝒜) (h : (L : IntermediateField K Ω) ≤ L') (b : B) (x : (L : IntermediateField K Ω)),
      ((f L' b ⟨x, h x.2⟩ : (L' : IntermediateField K Ω)) : Ω) =
        ((f L b x : (L : IntermediateField K Ω)) : Ω))
    (b : B) :
    ∃ g : M ≃ₐ[K] M, ∀ L : 𝒜, restrictAbPi K Ω g L = f L b := by
  haveI : Nonempty 𝒜 := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let S (L : 𝒜) := {g : M ≃ₐ[K] M | restrictAbPi K Ω g L = f L b}
  have hcl (L : 𝒜) : IsClosed (S L) := by
    haveI := L.2.2
    haveI : T2Space ((L : IntermediateField K Ω) ≃ₐ[K] (L : IntermediateField K Ω)) :=
      krullTopology_t2
    exact isClosed_eq ((continuous_apply L).comp continuous_restrictAbPi) continuous_const
  have hne (L : 𝒜) : (S L).Nonempty := by
    haveI := L.2.2
    exact restrictAb_surjective (L : IntermediateField K Ω) _ _
  have hle {L L' : 𝒜} (h : (L : IntermediateField K Ω) ≤ L') : S L' ⊆ S L := by
    intro g hg
    haveI := L.2.2
    haveI := L'.2.2
    change restrictAbPi K Ω g L' = f L' b at hg
    change restrictAbPi K Ω g L = f L b
    ext x
    have e := congrArg (fun σ : (L' : IntermediateField K Ω) ≃ₐ[K] (L' : IntermediateField K Ω) =>
      ((σ ⟨x, h x.2⟩ : (L' : IntermediateField K Ω)) : Ω)) hg
    simp only [restrictAbPi, restrictAb_apply] at e ⊢
    exact e.trans (hf L L' h b x)
  have hdir : Directed (· ⊇ ·) S := by
    intro L L'
    haveI := L.2.1
    haveI := L.2.2
    haveI := L'.2.1
    haveI := L'.2.2
    let T := (L : IntermediateField K Ω) ⊔ (L' : IntermediateField K Ω)
    have hT : T ≤ M := sup_le (le_maximalAbelianExtension _) (le_maximalAbelianExtension _)
    exact ⟨⟨T, inferInstance, isAbelianGalois_of_le_maximalAbelianExtension T hT⟩,
      hle le_sup_left, hle le_sup_right⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hdir hne (fun L => (hcl L).isCompact) hcl
  exact ⟨g, fun L => Set.mem_iInter.mp hg L⟩

theorem exists_continuous_abelian_hom
    (f : ∀ L : 𝒜, B →* ((L : IntermediateField K Ω) ≃ₐ[K] (L : IntermediateField K Ω)))
    (hc : ∀ L, Continuous (f L))
    (hf : ∀ (L L' : 𝒜) (h : (L : IntermediateField K Ω) ≤ L') (b : B) (x : (L : IntermediateField K Ω)),
      ((f L' b ⟨x, h x.2⟩ : (L' : IntermediateField K Ω)) : Ω) =
        ((f L b x : (L : IntermediateField K Ω)) : Ω)) :
    ∃ g : B →* (M ≃ₐ[K] M), Continuous g ∧ ∀ (L : 𝒜) b, restrictAbPi K Ω (g b) L = f L b := by
  choose g hg using exists_abelian_restrictions f hf
  let F : B →* (M ≃ₐ[K] M) :=
    { toFun := g
      map_one' := ext_restrictAb fun L hfin hab => by
        let v : 𝒜 := ⟨L, hfin, hab⟩
        have h : restrictAb L (le_maximalAbelianExtension L) (g 1) = f v 1 := hg 1 v
        rw [h, map_one, map_one]
      map_mul' x y := ext_restrictAb fun L hfin hab => by
        let v : 𝒜 := ⟨L, hfin, hab⟩
        have h : restrictAb L (le_maximalAbelianExtension L) (g (x * y)) = f v (x * y) := hg _ v
        rw [h, map_mul, map_mul]
        exact congrArg₂ (· * ·) (hg x v).symm (hg y v).symm }
  refine ⟨F, continuous_iff_restrictAb.mpr (fun L hfin hab => ?_), fun L b => hg b L⟩
  let v : 𝒜 := ⟨L, hfin, hab⟩
  have he : (fun b => restrictAb L (le_maximalAbelianExtension L) (F b)) = f v :=
    funext fun b => hg b v
  rw [he]
  exact hc v

end GlobalTheory.Reciprocity
