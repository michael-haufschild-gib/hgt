import GaloisForLFunctions.RHTower.Artin.RelativeNormsOfRayElementsAreRayElements
import GaloisForLFunctions.RHTower.Artin.TheKernelOfTheArtinMapIsTheNormGroup

/-! The relative ideal norm descends to ray classes at a rational
modulus. Prime-to-modulus factors suffice for norm preimages there. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

universe u

variable (K E : Type u) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  (c : ℕ) [NeZero c]

/-- The relative norm between the fractional ideal groups prime to c. -/
def coprimeIdealNorm : idealGroup (normModulus E c) →* idealGroup (normModulus K c) :=
  ((idealNormHom K E).comp (idealGroup (normModulus E c)).subtype).codRestrict _
    fun I => idealNormHom_mem_idealGroup K E c I.2

/-- The relative norm between ray class groups of the same rational modulus. -/
def rayClassNorm : RayClassGroup (normModulus E c) →* RayClassGroup (normModulus K c) :=
  QuotientGroup.lift _ ((rayClass (normModulus K c)).comp (coprimeIdealNorm K E c)) fun _ hI =>
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
      (idealNormHom_mem_rayPrincipal K E c (Subgroup.mem_subgroupOf.mp hI)))

@[simp]
theorem rayClassNorm_apply (I : idealGroup (normModulus E c)) :
    rayClassNorm K E c (rayClass (normModulus E c) I) =
      rayClass (normModulus K c) (coprimeIdealNorm K E c I) := rfl

section CoprimePart

variable {K}

private def coprimePart (m : Modulus K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ →*
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  letI := Classical.propDecidable
  primeValuesHom fun v : HeightOneSpectrum (𝓞 K) => if v.asIdeal ∣ m.fin then 1 else idealUnit v.ne_bot

private theorem coprimePart_mem (m : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    coprimePart m I ∈ idealGroup m := by
  classical
  refine primeValuesHom_mem _ I fun v _ => ?_
  change (if v.asIdeal ∣ m.fin then 1 else idealUnit v.ne_bot) ∈ idealGroup m
  split_ifs with h
  · exact one_mem _
  · exact idealUnit_prime_mem_idealGroup m h

private theorem coprimePart_eq_of_mem (m : Modulus K) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : I ∈ idealGroup m) : coprimePart m I = I := by
  classical
  refine (primeValuesHom_congr I ?_).trans (primeValuesHom_idealUnit I)
  intro v hv
  exact if_neg (fun h => hv (hI v h))

end CoprimePart

private theorem coprimePart_comp_idealNormHom :
    (coprimePart (normModulus K c)).comp (idealNormHom K E) =
      (idealNormHom K E).comp (coprimePart (normModulus E c)) := by
  classical
  let f := (coprimePart (normModulus K c)).comp (idealNormHom K E)
  let g := (idealNormHom K E).comp (coprimePart (normModulus E c))
  have h (w : HeightOneSpectrum (𝓞 E)) : f (idealUnit w.ne_bot) = g (idealUnit w.ne_bot) := by
    have he : w.asIdeal ∣ (normModulus E c).fin ↔ (w.under (𝓞 K)).asIdeal ∣
        (normModulus K c).fin := by
      rw [dvd_normModulus_fin_iff, dvd_normModulus_fin_iff]
      change _ ↔ algebraMap (𝓞 K) (𝓞 E) (c : 𝓞 K) ∈ w.asIdeal
      rw [map_natCast]
    change coprimePart (normModulus K c) (idealNormHom K E (idealUnit w.ne_bot)) =
      idealNormHom K E (coprimePart (normModulus E c) (idealUnit w.ne_bot))
    rw [idealNormHom_idealUnit_prime, map_pow, coprimePart, coprimePart,
      primeValuesHom_idealUnit_prime, primeValuesHom_idealUnit_prime]
    by_cases hw : w.asIdeal ∣ (normModulus E c).fin
    · rw [if_pos hw, if_pos (he.mp hw), one_pow, map_one]
    · rw [if_neg hw, if_neg (he.not.mp hw), idealNormHom_idealUnit_prime]
  change f = g
  rw [eq_primeValuesHom f, eq_primeValuesHom g]
  exact congrArg primeValuesHom (funext h)

theorem range_coprimeIdealNorm_eq_subgroupOf :
    (coprimeIdealNorm K E c).range =
      (idealNormHom K E).range.subgroupOf (idealGroup (normModulus K c)) := by
  ext I
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨J.val, rfl⟩
  · rintro ⟨J, hJ⟩
    let X := coprimePart (normModulus E c) J
    refine ⟨⟨X, coprimePart_mem _ J⟩, Subtype.ext ?_⟩
    change idealNormHom K E X = I.val
    have h := DFunLike.congr_fun (coprimePart_comp_idealNormHom K E c) J
    exact h.symm.trans (by
      change coprimePart (normModulus K c) (idealNormHom K E J) = I.val
      exact (congrArg (coprimePart (normModulus K c)) hJ).trans (coprimePart_eq_of_mem _ I.2))

variable (G : Type u) [CommGroup G] [Fintype G] [MulSemiringAction G E] [IsGaloisGroup G K E]

/-- An ideal in the kernel of the Artin map is a ray ideal times the norm
of an ideal prime to the same rational modulus. -/
theorem exists_ray_mul_coprimeNorm_of_artin_eq_one
    (hu : ∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K E G v)
    (hr : rayPrincipal (normModulus K c) ≤ (artinMap K E G).ker)
    (I : idealGroup (normModulus K c)) (hI : artinMap K E G I.val = 1) :
    ∃ (J : idealGroup (normModulus E c)) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
      a ∈ rayPrincipal (normModulus K c) ∧ a * idealNormHom K E J.val = I.val := by
  have hm : I ∈ normIdealGroup K E (normModulus K c) := by
    rw [← ker_artinMap_comp_subtype K E G _ hu hr]
    exact MonoidHom.mem_ker.mpr hI
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (Subgroup.mem_subgroupOf.mp hm)
  have hb' : b ∈ idealGroup (normModulus K c) := by
    rw [show b = a⁻¹ * I.val by rw [← hab, inv_mul_cancel_left]]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (rayPrincipal_le _ ha)) I.2
  have ht : (⟨b, hb'⟩ : idealGroup (normModulus K c)) ∈ (coprimeIdealNorm K E c).range := by
    rw [range_coprimeIdealNorm_eq_subgroupOf]
    exact hb
  obtain ⟨J, hJ⟩ := ht
  exact ⟨J, a, ha, (congrArg (a * ·) (congrArg Subtype.val hJ)).trans hab⟩

end GlobalTheory.Reciprocity
