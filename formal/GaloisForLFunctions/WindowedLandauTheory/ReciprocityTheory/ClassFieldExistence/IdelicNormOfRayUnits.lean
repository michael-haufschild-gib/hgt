import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.NormUnitsAtUnramifiedPrimes
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormOfLocalUnits
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArchimedeanPowerIndex
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayClass

/-! An idele of trivial divisor satisfying sufficiently deep rational
ray congruences is the norm of an idele integral at every finite place. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal WithZero GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped NumberField.LiesOver IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype G := Fintype.ofFinite _

local notation "D" => Module.finrank K L

theorem mem_range_ideleNorm_of_mem_ray_trivial_divisor {c : ℕ} [NeZero c]
    (hDc : D ∣ c)
    (hur : ∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K L G v)
    (hpow : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K c).fin →
      ∀ x : (v.adicCompletion K)ˣ, x ∈ unitsLevel v (exponent (normModulus K c) v) →
        ∃ z : (v.adicCompletion K)ˣ, z ∈ unitsLevel v 0 ∧ z ^ D = x)
    {x : IdeleGroup K} (hx : x ∈ idelesOneMod (normModulus K c))
    (hI : toFractionalIdeal x = 1) : x ∈ (ideleNorm (K := K) (L := L)).range := by
  have hD : 0 < D := Module.finrank_pos
  letI : NeZero D := ⟨hD.ne'⟩
  have hx' := (mem_idelesOneMod _).mp hx
  refine mem_range_ideleNorm_of_localIntegralPreimages x (fun v => ?_) (fun v => ?_)
  · by_cases hv : v.asIdeal ∣ (normModulus K c).fin
    · exact exists_integral_fibre_of_pow v _ (hpow v hv _ (hx'.1 v hv))
    · have hv' : ¬ v.asIdeal ∣ (normModulus K D).fin := fun h =>
        hv (h.trans (Ideal.dvd_iff_le.mpr (normModulus_fin_le_of_dvd K hDc)))
      have h0 : ord v x = 0 := by
        simpa only [Units.val_one, count_one] using (toFractionalIdeal_eq_iff.mp hI v)
      have hu := (ord_eq_zero_iff v x).mp h0
      have hxu : finiteProj v x ∈ unitsLevel v 0 := by
        rw [unitsLevel_zero, Submonoid.mem_units_iff, ← map_inv]
        exact hu
      exact exists_integral_fibre_of_unramified v (hur v hv)
        (valued_natCast_eq_one_of_not_dvd v D hv') _ hxu
  · obtain ⟨z, hz⟩ := mem_range_power_infiniteCompletion v (infiniteProj v x) hD
      (fun hv => hx'.2 ⟨v, hv⟩ (Set.mem_univ _))
    exact ⟨_, (infiniteLocalNorm_of_scalar v z).trans hz⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.mem_range_ideleNorm_of_mem_ray_trivial_divisor
