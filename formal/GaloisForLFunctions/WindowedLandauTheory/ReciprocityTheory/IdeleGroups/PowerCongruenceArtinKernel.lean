import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.PowerCongruenceIdeles
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FiniteIdelicArtin

/-! Local power congruences lie in the finite Artin kernel when all
ramified primes are included and the exponent kills the Galois group. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable {K L G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- Any finite continuous idelic character trivial on all n-th powers kills
the corresponding local power congruences once its ray support is included. -/
theorem powerCongruence_le_ker_of_idelesOneMod
    {B : Type*} [Group B] {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (m : Modulus K) (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin → v ∈ S)
    (φ : IdeleGroup K →* B) (hpow : ∀ x : IdeleGroup K, φ (x ^ n) = 1)
    (hφ : ∀ z ∈ idelesOneMod m, (∀ v, ord v z = 0) → φ z = 1) :
    powerCongruence n S ≤ φ.ker := by
  intro x hx
  obtain ⟨y, z, rfl, hf, hi, ho⟩ := exists_normalized_of_mem_powerCongruence hx
  have hz : z ∈ idelesOneMod m := (mem_idelesOneMod m).mpr
    ⟨fun v hv => by rw [hf v (hS v hv)]; exact one_mem _,
      fun w _ => by simp [hi w.val]⟩
  change φ (y ^ n * z) = 1
  rw [map_mul, hpow y, hφ z hz ho, one_mul]

theorem powerCongruence_le_ker_finite_idelic_artin
    {n : ℕ} (hn : ∀ g : G, g ^ n = 1) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (m : Modulus K) (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin → v ∈ S)
    (φ : IdeleGroup K →* G)
    (hφ : ∀ x : idelesOneMod m, φ x.val = artinMap K L G (toFractionalIdeal x.val)) :
    powerCongruence n S ≤ φ.ker := by
  refine powerCongruence_le_ker_of_idelesOneMod S m hS φ
    (fun x => by rw [map_pow, hn]) fun z hz ho => ?_
  have hzI : toFractionalIdeal z = 1 :=
    toFractionalIdeal_eq_iff.mpr fun v => by simpa only [Units.val_one, count_one] using ho v
  rw [hφ ⟨z, hz⟩, hzI, map_one]

end GlobalTheory.Reciprocity
