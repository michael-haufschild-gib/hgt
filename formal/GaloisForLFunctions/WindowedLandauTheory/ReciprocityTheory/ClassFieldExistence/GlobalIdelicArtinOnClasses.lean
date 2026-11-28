import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalIdelicArtinKernelClosure
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.GlobalIdelicArtinQuotient

/-! On the ordinary idele class group, the global Artin map is an
open quotient with kernel the closure of the archimedean positive classes. -/

noncomputable section

open NumberField Topology

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K : Type) [Field K] [NumberField K]

def ideleClassToCompact : IdeleClassGroup K →* CompactIdeleClassQuotient K :=
  QuotientGroup.lift _ (toCompactIdeleClassQuotient K)
    (fun x ⟨u, hu⟩ => by
      rw [← hu]
      exact toCompactIdeleClassQuotient_diagonal K u)

@[simp] theorem ideleClassToCompact_mk (x : IdeleGroup K) :
    ideleClassToCompact K (IdeleClassGroup.mk K x) = toCompactIdeleClassQuotient K x := rfl

theorem isOpenQuotientMap_ideleClassToCompact : IsOpenQuotientMap (ideleClassToCompact K) := by
  let q := ideleClassToCompact K
  let p := IdeleClassGroup.mk K
  let Q := toCompactIdeleClassQuotient K
  have hp := IdeleClassGroup.mk_surjective K
  have hs : Function.Surjective q := fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ c
    exact ⟨p x, rfl⟩
  have hc : Continuous q := (QuotientGroup.isQuotientMap_mk (diagonal K).range).continuous_iff.mpr
    (show Continuous Q from QuotientGroup.continuous_mk)
  refine ⟨hs, hc, fun U hU => ?_⟩
  have he : q '' U = Q '' (p ⁻¹' U) := by
    change q '' U = (q ∘ p) '' (p ⁻¹' U)
    rw [Set.image_comp, Set.image_preimage_eq _ hp]
  rw [he]
  exact QuotientGroup.isOpenMap_coe _ (hU.preimage (IdeleClassGroup.continuous_mk K))

private theorem comap_archPositive_map_mk :
    ((archPositive K).map (IdeleClassGroup.mk K)).comap (IdeleClassGroup.mk K) =
      (diagonal K).range ⊔ archPositive K := by
  let q := IdeleClassGroup.mk K
  ext x
  constructor
  · rintro ⟨a, ha, he⟩
    have h : x / a ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk K, MonoidHom.mem_ker]
      change q (x / a) = 1
      rw [map_div, he, div_self']
    exact Subgroup.mem_sup.mpr ⟨x / a, h, a, ha, div_mul_cancel _ _⟩
  · intro h
    obtain ⟨_, ⟨u, rfl⟩, a, ha, rfl⟩ := Subgroup.mem_sup.mp h
    refine ⟨a, ha, ?_⟩
    change q a = q (diagonal K u * a)
    rw [map_mul, show q (diagonal K u) = 1 from IdeleClassGroup.mk_diagonal K u]
    exact (one_mul (q a)).symm

variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem ordinary_globalArtin_ker_eq_archPositive_closure
    (a : CompactIdeleClassQuotient K →* Gal(maximalAbelianExtension K Ω/K))
    (ha : Continuous a) (hm : MatchesFiniteIdelicArtin K Ω a) :
    (a.comp (ideleClassToCompact K)).ker =
      ((archPositive K).map (IdeleClassGroup.mk K)).topologicalClosure := by
  let q := IdeleClassGroup.mk K
  let b := a.comp (ideleClassToCompact K)
  let C := (archPositive K).map q
  have h₁ : q ⁻¹' (b.ker : Set (IdeleClassGroup K)) =
      (((diagonal K).range ⊔ archPositive K).topologicalClosure : Set (IdeleGroup K)) := by
    change ((a.comp (toCompactIdeleClassQuotient K)).ker : Set (IdeleGroup K)) = _
    rw [globalArtin_idele_ker_eq_closure a ha hm]
  have h₂ : q ⁻¹' closure (C : Set (IdeleClassGroup K)) =
      (((diagonal K).range ⊔ archPositive K).topologicalClosure : Set (IdeleGroup K)) := by
    rw [(IdeleClassGroup.isOpenMap_mk K).preimage_closure_eq_closure_preimage
      (IdeleClassGroup.continuous_mk K)]
    change closure ((C.comap q : Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) = _
    rw [comap_archPositive_map_mk K]
    rfl
  apply SetLike.coe_injective
  ext x
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K x
  change y ∈ q ⁻¹' (b.ker : Set (IdeleClassGroup K)) ↔ y ∈ q ⁻¹' closure (C : Set (IdeleClassGroup K))
  rw [h₁, h₂]

theorem exists_global_idelic_artin_on_classes :
    ∃ a : CompactIdeleClassQuotient K →* Gal(maximalAbelianExtension K Ω/K),
      MatchesFiniteIdelicArtin K Ω a ∧
      IsOpenQuotientMap (a.comp (ideleClassToCompact K)) ∧
      (a.comp (ideleClassToCompact K)).ker =
        ((archPositive K).map (IdeleClassGroup.mk K)).topologicalClosure := by
  obtain ⟨a, ha, hm⟩ := exists_open_quotient_global_idelic_artin K Ω
  refine ⟨a, hm, ha.comp (isOpenQuotientMap_ideleClassToCompact K), ?_⟩
  exact ordinary_globalArtin_ker_eq_archPositive_closure K Ω a ha.continuous hm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_global_idelic_artin_on_classes
