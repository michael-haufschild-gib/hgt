import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayCharactersOfGlobalArtin

/-! Rational ray kernels give a neighbourhood basis in the compact
idele quotient. Thus the global Artin kernel on ideles is the closure
of the product of the diagonal and positive archimedean ideles. -/

noncomputable section

open NumberField Topology GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

local notation "C" => CompactIdeleClassQuotient K
local notation "G" => Gal(maximalAbelianExtension K Ω/K)

private theorem globalArtin_mem_nhds_of_ker (a : C →* G)
    (ha : MatchesFiniteIdelicArtin K Ω a) (U : Set C) (hU : U ∈ 𝓝 1) :
    ∀ y ∈ a.ker, y ∈ U := by
  obtain ⟨c, hc, h⟩ := exists_rationalRay_ker_mem_nhds U hU
  letI := hc
  let m := normModulus K c
  let r := compactToRayClass m
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  letI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have hr : IsOpen (r.ker : Set C) :=
    (isOpen_discrete ({1} : Set (RayClassGroup m))).preimage (continuous_compactToRayClass m)
  intro x hx
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact h z (globalArtin_ker_le_open a ha r.ker hr hx)

theorem globalArtin_ker_eq_closure_bot (a : C →* G)
    (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a) :
    a.ker = (⊥ : Subgroup C).topologicalClosure := by
  letI : T2Space G := krullTopology_t2
  apply le_antisymm
  · intro x hx
    change x ∈ closure ((⊥ : Subgroup C) : Set C)
    rw [mem_closure_iff_nhds_one]
    intro U hU
    exact ⟨1, Subgroup.one_mem _, by
      rw [one_div]
      exact globalArtin_mem_nhds_of_ker a ha U hU x⁻¹ (inv_mem hx)⟩
  · apply Subgroup.topologicalClosure_minimal _ bot_le
    change IsClosed (a ⁻¹' ({1} : Set G))
    exact isClosed_singleton.preimage hc

theorem globalArtin_idele_ker_eq_closure (a : C →* G)
    (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a) :
    (a.comp (toCompactIdeleClassQuotient K)).ker =
      ((diagonal K).range ⊔ archPositive K).topologicalClosure := by
  let q := toCompactIdeleClassQuotient K
  change a.ker.comap q = _
  rw [globalArtin_ker_eq_closure_bot a hc ha]
  apply SetLike.coe_injective
  change q ⁻¹' closure ((⊥ : Subgroup C) : Set C) = closure _
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  rw [hqo.preimage_closure_eq_closure_preimage hq]
  congr 1
  ext x
  exact Subgroup.mem_bot.trans (QuotientGroup.eq_one_iff x)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.globalArtin_idele_ker_eq_closure
