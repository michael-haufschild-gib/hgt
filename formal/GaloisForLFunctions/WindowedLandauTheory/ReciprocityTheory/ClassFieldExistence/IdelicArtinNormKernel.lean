import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormDivisor
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormOfRayUnits
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayClassNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel

/-! The kernel of finite idelic Artin reciprocity is the product of
principal ideles and norms. The ideal norm theorem removes the divisor.
The remaining congruent units lift separately at all places. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

local notation "G" => Gal(L/K)
local notation "D" => Module.finrank K L

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype G := Fintype.ofFinite _

private theorem exists_artin_norm_refinement (q : Modulus K) :
    ∃ (c : ℕ) (hc : NeZero c), letI := hc
      (normModulus K c).fin ≤ q.fin ∧ D ∣ c ∧
      (∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K L G v) ∧
      rayPrincipal (normModulus K c) ≤ (artinMap K L G).ker ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K c).fin →
        ∀ x : (v.adicCompletion K)ˣ, x ∈ unitsLevel v (exponent (normModulus K c) v) →
          ∃ z : (v.adicCompletion K)ˣ, z ∈ unitsLevel v 0 ∧ z ^ D = x) := by
  obtain ⟨a, ha, hau, har⟩ := exists_rayPrincipal_le_ker_artinMap K L G
  letI := ha
  let b := a * q.fin.absNorm
  letI : NeZero b := ⟨mul_ne_zero (NeZero.ne a)
    (fun h => q.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))⟩
  letI : NeZero D := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨c, hc, hbc, hD, hp⟩ := exists_rational_multiple_for_integral_powers (K := K) b D
  letI := hc
  have hac : a ∣ c := (dvd_mul_right a q.fin.absNorm).trans hbc
  have hqa : q.fin.absNorm ∣ c := (dvd_mul_left q.fin.absNorm a).trans hbc
  refine ⟨c, hc, normModulus_fin_le_of_absNorm_dvd K q hqa, hD, ?_,
    (rayPrincipal_normModulus_le_of_dvd K hac).trans har, hp⟩
  intro v hv
  refine hau v fun h => hv ?_
  exact ((dvd_normModulus_fin_iff K a v).mpr h).trans
    (Ideal.dvd_iff_le.mpr (normModulus_fin_le_of_dvd K hac))

private theorem artin_eq_one_on_ideleNorm {c : ℕ} [NeZero c]
    (f : IdeleGroup K →* G) (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (hf : ∀ x : idelesOneMod (normModulus K c),
      f x.val = artinMap K L G (toFractionalIdeal x.val)) (y : IdeleGroup L) :
    f (ideleNorm y) = 1 := by
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod (normModulus L c) y
  let Y := diagonal L a * y
  have h : ideleNorm (K := K) Y ∈ idelesOneMod (normModulus K c) :=
    ideleNorm_mem_idelesOneMod_rational c Y ha
  have he := hf ⟨ideleNorm Y, h⟩
  change f (ideleNorm Y) = artinMap K L G (toFractionalIdeal (ideleNorm Y)) at he
  rw [toFractionalIdeal_ideleNorm, artinMap_idealNormHom] at he
  rw [show Y = diagonal L a * y from rfl, map_mul, map_mul, ideleNorm_diagonal, hd, one_mul] at he
  exact he

private theorem normalized_idele_in_diagonal_sup_norm {c : ℕ} [NeZero c]
    (hD : D ∣ c) (hu : ∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K L G v)
    (hr : rayPrincipal (normModulus K c) ≤ (artinMap K L G).ker)
    (hp : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K c).fin →
      ∀ x : (v.adicCompletion K)ˣ, x ∈ unitsLevel v (exponent (normModulus K c) v) →
        ∃ z : (v.adicCompletion K)ˣ, z ∈ unitsLevel v 0 ∧ z ^ D = x)
    (x : idelesOneMod (normModulus K c))
    (hx : artinMap K L G (toFractionalIdeal x.val) = 1) :
    x.val ∈ (diagonal K).range ⊔ (ideleNorm (K := K) (L := L)).range := by
  let I := toCoprimeIdeals (normModulus K c) x
  obtain ⟨J, p, hpr, he⟩ := exists_ray_mul_coprimeNorm_of_artin_eq_one K L c G hu hr I hx
  obtain ⟨a, ha, rfl⟩ := hpr
  obtain ⟨y, hy⟩ := toCoprimeIdeals_surjective (normModulus L c) J
  have hY : ideleNorm (K := K) y.val ∈ idelesOneMod (normModulus K c) :=
    ideleNorm_mem_idelesOneMod_rational c _ y.2
  have ha' : diagonal K a ∈ idelesOneMod (normModulus K c) := by
    rw [← rayUnits_eq] at ha
    exact ha
  let z := x.val / (diagonal K a * ideleNorm y.val)
  have hz : z ∈ idelesOneMod (normModulus K c) := div_mem x.2 (mul_mem ha' hY)
  have hJ : toFractionalIdeal y.val = J.val := congrArg Subtype.val hy
  have hquot : toFractionalIdeal z = 1 := by
    change toFractionalIdeal (x.val / (diagonal K a * ideleNorm y.val)) = 1
    rw [map_div, map_mul, toFractionalIdeal_diagonal, toFractionalIdeal_ideleNorm, hJ]
    change toFractionalIdeal x.val / _ = 1
    rw [he]
    change I.val / I.val = 1
    exact div_self' I.val
  obtain ⟨b, hb⟩ := mem_range_ideleNorm_of_mem_ray_trivial_divisor hD hu hp hz hquot
  refine Subgroup.mem_sup.mpr ⟨diagonal K a, ⟨a, rfl⟩,
    ideleNorm (y.val * b), ⟨y.val * b, rfl⟩, ?_⟩
  rw [map_mul, ← mul_assoc, hb]
  change (diagonal K a * ideleNorm y.val) *
    (x.val / (diagonal K a * ideleNorm y.val)) = x.val
  rw [mul_comm, div_mul_cancel]

/-- The finite Artin kernel consists of principal ideles times idelic norms. -/
theorem finiteIdelicArtin_ker_eq_diagonal_sup_ideleNorm
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1) :
    f.ker = (diagonal K).range ⊔ (ideleNorm (K := K) (L := L)).range := by
  obtain ⟨q, -, hq⟩ := hf
  obtain ⟨c, hc, hfin, hD, hu, hr, hp⟩ := exists_artin_norm_refinement (L := L) q
  letI := hc
  let m := normModulus K c
  have hfm (x : idelesOneMod m) : f x.val = artinMap K L G (toFractionalIdeal x.val) :=
    hq ⟨x.val, idelesOneMod_le_of_refinement hfin (Set.subset_univ _) x.2⟩
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod m x
    let X : idelesOneMod m := ⟨diagonal K a * x, ha⟩
    have hX : artinMap K L G (toFractionalIdeal X.val) = 1 := by
      rw [← hfm]
      change f (diagonal K a * x) = 1
      rw [map_mul, hd, one_mul]
      exact hx
    have hm := normalized_idele_in_diagonal_sup_norm hD hu hr hp X hX
    have hle : (diagonal K).range ≤ (diagonal K).range ⊔ (ideleNorm (K := K) (L := L)).range :=
      le_sup_left
    have hA := hle (show diagonal K a ∈ (diagonal K).range from ⟨a, rfl⟩)
    have he := Subgroup.mul_mem _ (inv_mem hA) hm
    change (diagonal K a)⁻¹ * (diagonal K a * x) ∈ _ at he
    rwa [inv_mul_cancel_left] at he
  · rintro _ ⟨a, rfl⟩
    exact hd a
  · rintro _ ⟨y, rfl⟩
    exact artin_eq_one_on_ideleNorm f hd hfm y

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_ker_eq_diagonal_sup_ideleNorm
