import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianGaloisAssembly
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicArtinCompatibility
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.CompactIdelicClassQuotient

/-! Finite idelic Artin maps assemble continuously on the compact
quotient by principal and positive archimedean ideles. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField FractionalIdeal GaloisForLFunctions Topology
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "𝒜" => finiteAbelianExtensions K Ω
local notation "M" => maximalAbelianExtension K Ω

/-- A global map recovers the finite ideal Artin maps on their idelic rays. -/
def MatchesFiniteIdelicArtin (a : CompactIdeleClassQuotient K →* (M ≃ₐ[K] M)) : Prop :=
  ∀ V : 𝒜,
    let L := (V : IntermediateField K Ω)
    letI : FiniteDimensional K L := V.2.1
    letI : IsAbelianGalois K L := V.2.2
    letI : CommGroup Gal(L/K) :=
      { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    letI : NumberField L := NumberField.of_module_finite K L
    letI : Fintype Gal(L/K) := Fintype.ofFinite _
    ∃ m : Modulus K,
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin ↔ ¬ IsUnramifiedPrime K L Gal(L/K) v) ∧
      ∀ x : idelesOneMod m,
        restrictAbPi K Ω (a (toCompactIdeleClassQuotient K x.val)) V =
          artinMap K L Gal(L/K) (toFractionalIdeal x.val)

theorem exists_global_idelic_artin :
    ∃ a : CompactIdeleClassQuotient K →* (M ≃ₐ[K] M), Continuous a ∧ MatchesFiniteIdelicArtin K Ω a ∧
      ∀ L : 𝒜, Function.Surjective fun c => restrictAbPi K Ω (a c) L := by
  classical
  have hex (V : 𝒜) :
      let L := (V : IntermediateField K Ω)
      letI : FiniteDimensional K L := V.2.1
      letI : IsAbelianGalois K L := V.2.2
      letI : CommGroup Gal(L/K) :=
        { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
      letI : NumberField L := NumberField.of_module_finite K L
      letI : Fintype Gal(L/K) := Fintype.ofFinite _
      ∃ (m : Modulus K) (φ : IdeleGroup K →* Gal(L/K)),
        Continuous φ ∧ Function.Surjective φ ∧
        (∀ x : Kˣ, φ (diagonal K x) = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin ↔ ¬ IsUnramifiedPrime K L Gal(L/K) v) ∧
        ∀ y : idelesOneMod m, φ y.val = artinMap K L Gal(L/K) (toFractionalIdeal y.val) := by
    let L := (V : IntermediateField K Ω)
    letI : FiniteDimensional K L := V.2.1
    letI : IsAbelianGalois K L := V.2.2
    letI : CommGroup Gal(L/K) :=
      { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    letI : NumberField L := NumberField.of_module_finite K L
    letI : Fintype Gal(L/K) := Fintype.ofFinite _
    letI : DiscreteTopology Gal(L/K) := krullTopology_discreteTopology_of_finiteDimensional K L
    exact exists_finite_idelic_artin K L Gal(L/K)
  choose m φ hc hs hd hu hp using hex
  have hcompat (U V : 𝒜) (hUV : (U : IntermediateField K Ω) ≤ V) (y : IdeleGroup K)
      (x : (U : IntermediateField K Ω)) :
      ((φ V y ⟨x, hUV x.2⟩ : (V : IntermediateField K Ω)) : Ω) =
        ((φ U y x : (U : IntermediateField K Ω)) : Ω) := by
    let A := (U : IntermediateField K Ω)
    let B := (V : IntermediateField K Ω)
    letI : Algebra A B := (IntermediateField.inclusion hUV).toAlgebra
    letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := U.2.1
    letI := V.2.1
    letI := U.2.2
    letI := V.2.2
    letI : CommGroup Gal(A/K) :=
      { (inferInstance : Group Gal(A/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    letI : CommGroup Gal(B/K) :=
      { (inferInstance : Group Gal(B/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    letI : NumberField A := NumberField.of_module_finite K A
    letI : NumberField B := NumberField.of_module_finite K B
    letI : Fintype Gal(A/K) := Fintype.ofFinite _
    letI : Fintype Gal(B/K) := Fintype.ofFinite _
    have hh := DFunLike.congr_fun
      (finite_idelic_artin_restrict K A B Gal(A/K) Gal(B/K) (m U) (m V) (φ U) (φ V)
        (hd U) (hd V)
        (fun v hv => not_not.mp fun h => hv ((hu U v).mpr h))
        (fun v hv => not_not.mp fun h => hv ((hu V v).mpr h)) (hp U) (hp V)) y
    letI : FaithfulSMul A B :=
      (faithfulSMul_iff_algebraMap_injective A B).mpr (algebraMap A B).injective
    have he := congrArg (fun σ : Gal(A/K) => algebraMap A B (σ • x)) hh
    have h := IsGaloisGroup.algebraMap_restrictHom_smul (G := Gal(B/K)) (G' := Gal(A/K))
      (A := K) (B := A) (C := B) (φ V y) x
    exact (congrArg (fun z : B => (z : Ω)) (he.symm.trans h)).symm
  obtain ⟨g, hg, hgφ⟩ := exists_continuous_abelian_hom φ hc hcompat
  have hker : (diagonal K).range ≤ g.ker := by
    rintro _ ⟨x, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply ext_restrictAb
    intro L hfin hab
    have h := hgφ (⟨L, hfin, hab⟩ : 𝒜) (diagonal K x)
    change restrictAb L (le_maximalAbelianExtension L) (g (diagonal K x)) = _ at h
    rw [h, hd, map_one]
  have harch : archPositive K ≤ g.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply ext_restrictAb
    intro L hfin hab
    let v : 𝒜 := ⟨L, hfin, hab⟩
    have hxfin : toFinite K x = 1 := MonoidHom.mem_ker.mp hx.1
    have hxproj (w : HeightOneSpectrum (𝓞 K)) : finiteProj w x = 1 := by
      apply Units.ext
      exact congrArg (fun z : (FiniteAdeleRing (𝓞 K) K)ˣ =>
        (z : FiniteAdeleRing (𝓞 K) K) w) hxfin
    have hm : x ∈ idelesOneMod (m v) :=
      (mem_idelesOneMod _).2 ⟨fun w _ => by rw [hxproj]; exact one_mem _,
        fun w _ => (mem_positiveAt.mp hx.2) w (Set.mem_univ _)⟩
    have hideal : toFractionalIdeal x = 1 := toFractionalIdeal_eq_iff.mpr fun w => by
      rw [ord, ← coe_finiteProj, hxproj, Units.val_one, map_one, WithZero.log_one, neg_zero]
      rw [Units.val_one, count_one]
    rw [map_one]
    change restrictAbPi K Ω (g x) v = 1
    rw [hgφ, hp v ⟨x, hm⟩, hideal, map_one]
  let a : CompactIdeleClassQuotient K →* (M ≃ₐ[K] M) :=
    QuotientGroup.lift _ g (sup_le hker harch)
  refine ⟨a, Continuous.quotient_lift hg _, ?_, fun L z => ?_⟩
  · intro L
    exact ⟨m L, hu L, fun x => (hgφ L x.val).trans (hp L x)⟩
  · obtain ⟨x, hx⟩ := hs L z
    exact ⟨toCompactIdeleClassQuotient K x, (hgφ L x).trans hx⟩

end GlobalTheory.Reciprocity
