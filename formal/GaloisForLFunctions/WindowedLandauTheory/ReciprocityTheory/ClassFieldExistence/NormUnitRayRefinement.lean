import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDeepRoots
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.NormsOfLocalCongruences
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayNeighborhoods
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayRefinement
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicArtinCompatibility

/-! A rational ray modulus can be refined so that at each prime of
the refined modulus its congruence subgroup consists of integral powers. -/

noncomputable section

open NumberField IsDedekindDomain WithZero GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleRay

variable {K : Type} [Field K] [NumberField K]

theorem valued_natCast_eq_one_of_not_dvd (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) [NeZero n]
    (hv : ¬ v.asIdeal ∣ (normModulus K n).fin) : Valued.v (n : v.adicCompletion K) = 1 := by
  rw [valued_natCast_ray_exponent v n, (exponent_eq_zero_iff _ v).mpr hv]
  simp

theorem exists_rational_multiple_for_integral_powers (c n : ℕ) [NeZero c] [NeZero n] :
    ∃ (d : ℕ) (hd : NeZero d), letI := hd
      c ∣ d ∧ n ∣ d ∧ ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣ (normModulus K d).fin →
        ∀ x : (v.adicCompletion K)ˣ, x ∈ unitsLevel v (exponent (normModulus K d) v) →
          ∃ z : (v.adicCompletion K)ˣ, z ∈ unitsLevel v 0 ∧ z ^ n = x := by
  classical
  choose s hs hunit hroot using fun v : HeightOneSpectrum (𝓞 K) =>
    exists_unitsLevel_pow_roots v n (NeZero.ne n)
  let S := (finite_primes_dvd (normModulus K n)).toFinset
  obtain ⟨a, ha, hdepth⟩ := exists_rational_ray_levels S (fun v => s v.val)
  letI := ha
  let d := c * n * a
  letI : NeZero d := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne c) (NeZero.ne n)) (NeZero.ne a)⟩
  have hcd : c ∣ d := (dvd_mul_right c n).trans (dvd_mul_right (c * n) a)
  have hnd : n ∣ d := (dvd_mul_left n c).trans (dvd_mul_right (c * n) a)
  have had : a ∣ d := dvd_mul_left a (c * n)
  refine ⟨d, inferInstance, hcd, hnd, fun v hv x hx => hroot v x ?_⟩
  apply unitsLevel_antitone v _ hx
  by_cases h : v.asIdeal ∣ (normModulus K n).fin
  · have hvS : v ∈ S := (finite_primes_dvd (normModulus K n)).mem_toFinset.mpr h
    have hlev := hdepth ⟨v, hvS⟩
    have hmono := exponent_le_of_dvd (Ideal.dvd_iff_le.mpr (normModulus_fin_le_of_dvd K had)) v
    exact (Nat.le_succ (s v)).trans (hlev.trans hmono)
  · rw [hunit v (valued_natCast_eq_one_of_not_dvd v n h)]
    exact (one_le_exponent_iff _ v).mpr hv

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_rational_multiple_for_integral_powers
