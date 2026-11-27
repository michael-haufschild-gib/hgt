import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicArtinCompatibility

/-! Passing to a fixed field enlarges the idelic Artin kernel by the
inverse image of the corresponding subgroup of the Galois group. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

/-- A finite idelic Artin map agrees with the ideal Artin symbols on the
ideles normalized at a modulus supported on the ramified primes. -/
def IsFiniteIdelicArtin {K L : Type u} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] (φ : IdeleGroup K →* Gal(L/K)) : Prop :=
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  ∃ m : Modulus K,
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin ↔ ¬ IsUnramifiedPrime K L Gal(L/K) v) ∧
    ∀ x : idelesOneMod m, φ x.val = artinMap K L Gal(L/K) (toFractionalIdeal x.val)

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M] [IsAbelianGalois K M] [Fintype Gal(M/K)]

local instance : CommGroup Gal(M/K) :=
  { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (L : IntermediateField K M) [IsAbelianGalois K L] :
    CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

omit [NumberField K] [NumberField M] [Fintype Gal(M/K)] in
private theorem eq_restriction (L : IntermediateField K M) [IsAbelianGalois K L] [Fintype Gal(L/K)]
    [NumberField L] :
    IsGaloisGroup.restrictHom Gal(M/K) Gal(L/K) K L M = AlgEquiv.restrictNormalHom L := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L M).injective
  change ((IsGaloisGroup.restrictHom Gal(M/K) Gal(L/K) K L M σ x : L) : M) =
    ((AlgEquiv.restrictNormalHom L σ x : L) : M)
  rw [AlgEquiv.restrictNormalHom_apply]
  exact IsGaloisGroup.algebraMap_restrictHom_smul Gal(M/K) Gal(L/K) K L M σ x

theorem exists_finite_idelic_artin_of_kernel_le
    (m : Modulus K) (φ : IdeleGroup K →* Gal(M/K))
    (hd : ∀ a : Kˣ, φ (diagonal K a) = 1)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.fin → IsUnramifiedPrime K M Gal(M/K) v)
    (hp : ∀ x : idelesOneMod m, φ x.val = artinMap K M Gal(M/K) (toFractionalIdeal x.val))
    (N : Subgroup (IdeleGroup K)) (hN : φ.ker ≤ N) :
    ∃ (L : IntermediateField K M) (hL : IsAbelianGalois K L),
      letI := hL
      ∃ ψ : IdeleGroup K →* Gal(L/K),
        Continuous ψ ∧ Function.Surjective ψ ∧ ψ.ker = N ∧ IsFiniteIdelicArtin ψ := by
  let H := N.map φ
  let L := fixedField H
  letI : IsAbelianGalois K L := IsAbelianGalois.of_algHom L.val
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : DiscreteTopology Gal(L/K) := krullTopology_discreteTopology_of_finiteDimensional K L
  obtain ⟨q, ψ, hc, hs, hqd, hqu, hqp⟩ := exists_finite_idelic_artin K L Gal(L/K)
  have hr : (AlgEquiv.restrictNormalHom L).comp φ = ψ := by
    rw [← eq_restriction L]
    exact finite_idelic_artin_restrict K L M Gal(L/K) Gal(M/K) q m ψ φ hqd hd
      (fun v hv => not_not.mp (fun h => hv ((hqu v).mpr h))) hu hqp hp
  refine ⟨L, inferInstance, ψ, hc, hs, ?_, ⟨q, hqu, hqp⟩⟩
  have hk : (AlgEquiv.restrictNormalHom L).ker = H :=
    L.restrictNormalHom_ker.trans (fixingSubgroup_fixedField H)
  rw [← hr, ← MonoidHom.comap_ker, hk]
  ext x
  change φ x ∈ N.map φ ↔ x ∈ N
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y⁻¹ * x ∈ φ.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
    simpa only [mul_inv_cancel_left] using N.mul_mem hy (hN h)
  · intro hx
    exact ⟨x, hx, rfl⟩

end GlobalTheory.Reciprocity
