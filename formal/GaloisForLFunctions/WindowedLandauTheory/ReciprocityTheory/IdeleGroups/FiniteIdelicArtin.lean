import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayContinuity
import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsTrivialOnARayWithOnlyRamifiedPrimesInTheModulus
import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsSurjective

/-! The finite Artin map on fractional ideals extends to ideles through
the ray quotient. Its finite target has the discrete topology. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

private def rayArtin (𝔪 : Modulus K) (hrec : rayPrincipal 𝔪 ≤ (artinMap K L G).ker) :
    RayClassGroup 𝔪 →* G :=
  QuotientGroup.lift _ ((artinMap K L G).comp (idealGroup 𝔪).subtype) fun _ hx =>
    hrec (Subgroup.mem_subgroupOf.mp hx)

/-- A finite abelian extension has a continuous, surjective idelic
Artin map trivial on the diagonal, with its ideal values on the ray. -/
theorem exists_finite_idelic_artin [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (𝔪 : Modulus K) (φ : IdeleGroup K →* G),
      Continuous φ ∧ Function.Surjective φ ∧
      (∀ a : Kˣ, φ (diagonal K a) = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin ↔ ¬ IsUnramifiedPrime K L G v) ∧
      ∀ x : idelesOneMod 𝔪, φ x.val = artinMap K L G (toFractionalIdeal x.val) := by
  obtain ⟨I, hI, hu, hr⟩ := exists_ideal_rayPrincipal_le_ker_artinMap K L G
  let m : Modulus K := ⟨I, hI, Set.univ⟩
  have hram (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.fin) :
      IsUnramifiedPrime K L G v := not_not.mp (fun h => hv ((hu v).mpr h))
  let f := rayArtin K L G m hr
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨I, hI⟩ := (MonoidHom.range_eq_top.mp (range_artinMap_comp_subtype K L G m hram)) g
    exact ⟨rayClass m I, hI⟩
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  letI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have hc : Continuous f := continuous_of_discreteTopology
  refine ⟨m, f.comp (toRayClass m), hc.comp (continuous_toRayClass m),
    hf.comp (toRayClass_surjective m), ?_, hu, ?_⟩
  · intro a
    rw [MonoidHom.comp_apply, toRayClass_diagonal, map_one]
  · intro x
    have h := toRayClass_normalized m 1 x
    simp only [map_one, one_mul] at h
    rw [MonoidHom.comp_apply, h]
    rfl

end GlobalTheory.Reciprocity
