import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.NormsOfLocalCongruences
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormDivisor
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayRefinement

/-! The finite idelic Artin map commutes with the relative norm in a
Galois tower. Diagonal approximation reduces the identity to the
compatibility of the ideal Artin maps at unramified primes. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable (K E M : Type u) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
  [IsScalarTower K E M] [IsGalois K E] [IsAbelianGalois E M] [IsAbelianGalois K M]

local notation "H" => Gal(M/E)
local notation "Γ" => Gal(M/K)

local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : CommGroup Γ :=
  { (inferInstance : Group Γ) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype H := Fintype.ofFinite _

local instance : Fintype Γ := Fintype.ofFinite _

/-- Under a Galois tower, applying the lower Artin map after the idelic
norm equals the upper Artin map followed by the inclusion of automorphisms. -/
theorem finiteIdelicArtin_comp_ideleNorm
    (j : H →* Γ) (hj : ∀ (h : H) (x : M), j h • x = h • x)
    (f : IdeleGroup K →* Γ) (g : IdeleGroup E →* H)
    (hf : IsFiniteIdelicArtin f) (hg : IsFiniteIdelicArtin g)
    (hfd : ∀ a : Kˣ, f (diagonal K a) = 1) (hgd : ∀ a : Eˣ, g (diagonal E a) = 1) :
    f.comp (ideleNorm (K := K) (L := E)) = j.comp g := by
  obtain ⟨m, hu, hm⟩ := hf
  obtain ⟨n, -, hn⟩ := hg
  let c := m.fin.absNorm * n.fin.absNorm
  letI : NeZero c := ⟨mul_ne_zero
    (fun h => m.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
    (fun h => n.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))⟩
  have hmc := normModulus_fin_le_of_absNorm_dvd K m
    (d := c) (dvd_mul_right m.fin.absNorm n.fin.absNorm)
  have hnc := normModulus_fin_le_of_absNorm_dvd E n
    (d := c) (dvd_mul_left n.fin.absNorm m.fin.absNorm)
  apply MonoidHom.ext
  intro y
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod (normModulus E c) y
  let Y := diagonal E a * y
  have hY : Y ∈ idelesOneMod n :=
    idelesOneMod_le_of_refinement hnc (Set.subset_univ _) ha
  have hN : ideleNorm (K := K) Y ∈ idelesOneMod m :=
    idelesOneMod_le_of_refinement hmc (Set.subset_univ _)
      (ideleNorm_mem_idelesOneMod_rational c Y ha)
  have hgY : g Y = g y := by
    change g (diagonal E a * y) = g y
    rw [map_mul, hgd, one_mul]
  have hfN : f (ideleNorm (K := K) Y) = f (ideleNorm (K := K) y) := by
    change f (ideleNorm (diagonal E a * y)) = f (ideleNorm y)
    rw [map_mul, ideleNorm_diagonal, map_mul, hfd, one_mul]
  change f (ideleNorm (K := K) y) = j (g y)
  rw [← hfN, ← hgY]
  calc
    f (ideleNorm (K := K) Y) = artinMap K M Γ (toFractionalIdeal (ideleNorm Y)) :=
      hm ⟨_, hN⟩
    _ = artinMap K M Γ (idealNormHom K E (toFractionalIdeal Y)) := by
      rw [toFractionalIdeal_ideleNorm]
    _ = j (artinMap E M H (toFractionalIdeal Y)) := by
      symm
      apply map_artinMap_eq_artinMap_idealNormHom K E M j hj
      intro w hw
      refine not_not.mp fun hram => ?_
      have hwm := (hu (w.under (𝓞 K))).mpr hram
      have hcompat : (w.under (𝓞 K)).asIdeal ∣ (normModulus K c).fin :=
        hwm.trans (Ideal.dvd_iff_le.mpr hmc)
      have hcast := (dvd_normModulus_fin_iff K c (w.under (𝓞 K))).mp hcompat
      change algebraMap (𝓞 K) (𝓞 E) (c : 𝓞 K) ∈ w.asIdeal at hcast
      rw [map_natCast] at hcast
      have hwc := (dvd_normModulus_fin_iff E c w).mpr hcast
      exact hw ((count_toFractionalIdeal w Y).trans (ord_eq_zero_of_mem_idelesOneMod _ ha hwc))
    _ = j (g Y) := congrArg j (hn ⟨_, hY⟩).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_comp_ideleNorm
