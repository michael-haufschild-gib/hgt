import GaloisForLFunctions.RHTower.Artin.TheReciprocityLawForLinearCharacters
import GaloisForLFunctions.RHTower.Artin.EveryRayClassCharacterIsInducedFromAPrimitiveCharacterOfItsConductor

/-!
# The Artin symbols of a linear character are the values of a primitive ray class character

Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of
`G`. There are `c ≥ 1`, a modulus `𝔫` of `K` and a primitive ray class character `ψ` modulo `𝔫`
with `(χ, v) = ψ(v)` for every prime `v ∤ c`, and for `Re s > 1`

  `L(s, χ, L/K) = L(s, ψ) · Π_{v | c} (1 − ψ(v) N(v)^{-s}) (1 − (χ, v) N(v)^{-s})^{-1}`

(`exists_primitive_heckeCharacter_artinSymbol`).

Proof: the reciprocity law gives a ray class character modulo `(c) ∞` with the Artin symbols of
`χ` as values outside `c`; `ψ` is its primitive character, with the same values outside `c`, and
the two `L`-series differ by the Euler factors of `ψ` at the primes dividing `c`.
-/

open scoped Classical BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin symbols of a linear character are the values of a primitive ray class
character**, outside the primes dividing some `c ≥ 1`; the Artin Euler product is the Hecke
`L`-series of this character up to the Euler factors at the primes dividing `c`. -/
theorem exists_primitive_heckeCharacter_artinSymbol (χ : LinearCharacter G) :
    ∃ (c : ℕ) (_ : NeZero c) (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫),
      heckeFiniteConductor 𝔫 ψ = 𝔫.fin ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
        artinSymbol K L χ v = heckeValue 𝔫 ψ v.asIdeal) ∧
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
          (linearCharacterLine χ) s = heckeL 𝔫 ψ s *
            ∏ v ∈ (finite_primes_dvd (normModulus K c)).toFinset,
              ((1 - heckeValue 𝔫 ψ v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (-s)) *
                (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) := by
  obtain ⟨c, hc, ψ, hval, hL⟩ := exists_artinEulerProduct_linearCharacter_eq_heckeL_mul K L χ
  refine ⟨c, hc, conductorModulus (normModulus K c) ψ, primitiveHecke (normModulus K c) ψ,
    heckeFiniteConductor_primitiveHecke (normModulus K c) ψ, fun v hv => ?_, fun s hs => ?_⟩
  · rw [hval v hv, heckeValue_primitiveHecke_prime (normModulus K c) ψ v hv]
  · rw [hL s hs, heckeL_eq_heckeL_primitiveHecke_mul (normModulus K c) ψ hs, mul_assoc,
      ← Finset.prod_mul_distrib]

end GaloisForLFunctions
