import GaloisForLFunctions.RHTower.Artin.InvariantDivisorsDescendOutsideALargeSetOfPrimes
import GaloisForLFunctions.RHTower.Artin.TheArtinMapOverAnIntermediateFieldIsTheArtinMapOfTheNorm

/-! Conjugate primes of a Galois extension have the same relative ideal norm. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Reciprocity

universe u

variable (K E : Type u) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  (G : Type u) [CommGroup G] [MulSemiringAction G E] [IsGaloisGroup G K E]

attribute [local instance] primeMulAction

omit [NumberField E] in
/-- The underlying prime ideal of a conjugate place is the conjugate ideal. -/
theorem asIdeal_prime_smul (g : G) (w : HeightOneSpectrum (𝓞 E)) :
    (g • w).asIdeal = g • w.asIdeal := by
  ext a
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem idealNormHom_idealUnit_smul (g : G) (w : HeightOneSpectrum (𝓞 E)) :
    idealNormHom K E (idealUnit (g • w).ne_bot) = idealNormHom K E (idealUnit w.ne_bot) := by
  have hf : (g • w).asIdeal.inertiaDeg (𝓞 K) = w.asIdeal.inertiaDeg (𝓞 K) :=
    (congrArg (fun I : Ideal (𝓞 E) => I.inertiaDeg (𝓞 K)) (asIdeal_prime_smul E G g w)).trans
      (Ideal.inertiaDeg_smul (𝓞 K) _ g)
  rw [idealNormHom_idealUnit_prime, idealNormHom_idealUnit_prime, under_smul K E G, hf]

theorem prime_dvd_normModulus_smul_iff (c : ℕ) [NeZero c] (g : G)
    (w : HeightOneSpectrum (𝓞 E)) :
    (g • w).asIdeal ∣ (normModulus E c).fin ↔ w.asIdeal ∣ (normModulus E c).fin := by
  rw [dvd_normModulus_fin_iff, dvd_normModulus_fin_iff, asIdeal_prime_smul E G,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change MulSemiringAction.toRingHom G (𝓞 E) g⁻¹ (c : 𝓞 E) ∈ w.asIdeal ↔ _
  rw [map_natCast]

end GlobalTheory.Reciprocity
