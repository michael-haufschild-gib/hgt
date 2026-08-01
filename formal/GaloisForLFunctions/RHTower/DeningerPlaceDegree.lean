import GaloisForLFunctions.RHTower.DeningerLocalDegree
import GaloisForLFunctions.RHTower.DeningerPlaceRestriction

/-!
# The local degree of a finite place over `ℚ`

The local degree of a finite place is the local degree of its maximal ideal over the rational
prime below it.  In a tower of number fields it factors as the degree of the restricted place
times the relative local degree, because the local degree is multiplicative in towers.

This is the weight that normalizes the place space: dividing it by the absolute degree gives a
weight unchanged by enlarging the field.

* `deningerPlaceDegree` : the local degree of a finite place over `ℚ`.
* `deningerPlaceDegree_tower` : its factorization along a tower of number fields.
-/

namespace RHTower

open NumberField IsDedekindDomain Module

section PlaceDegree

variable {K : Type*} [Field K] [NumberField K]

/-- The local degree over `ℚ` of a finite place. -/
noncomputable def deningerPlaceDegree (w : FinitePlace K) : ℕ :=
  deningerLocalDegree (Ideal.under ℤ w.maximalIdeal.asIdeal) w.maximalIdeal.asIdeal

end PlaceDegree

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The local degree factors along a tower.**  The degree of a place of `L` over `ℚ` is the
degree of its restriction to `K` times the relative degree. -/
theorem deningerPlaceDegree_tower (w : FinitePlace L) :
    deningerPlaceDegree w
      = deningerPlaceDegree (deningerRestrictPlace (K := K) w)
        * deningerLocalDegree (Ideal.under (𝓞 K) w.maximalIdeal.asIdeal)
            w.maximalIdeal.asIdeal := by
  set Q : Ideal (𝓞 L) := w.maximalIdeal.asIdeal with hQ
  have hQbot : Q ≠ ⊥ := w.maximalIdeal.ne_bot
  haveI hQprime : Q.IsPrime := w.maximalIdeal.isPrime
  have hPbot : Ideal.under (𝓞 K) Q ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hQbot
  have hpbot : Ideal.under ℤ Q ≠ ⊥ := Ideal.under_ne_bot ℤ hQbot
  haveI hpmax : (Ideal.under ℤ Q).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hpbot (Ideal.IsPrime.under ℤ Q)
  haveI hPmax : (Ideal.under (𝓞 K) Q).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hPbot (Ideal.IsPrime.under (𝓞 K) Q)
  haveI hPover : (Ideal.under (𝓞 K) Q).LiesOver (Ideal.under ℤ Q) := by
    rw [← Ideal.under_under (A := ℤ) (B := 𝓞 K) Q]
    exact Ideal.over_under (A := ℤ) (Ideal.under (𝓞 K) Q)
  have hg0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) (Ideal.under (𝓞 K) Q) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hPbot
  have hfg : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.under ℤ Q) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hpbot
  have hrestrict : (deningerRestrictPlace (K := K) w).maximalIdeal.asIdeal
      = Ideal.under (𝓞 K) Q := by
    rw [deningerRestrictPlace_maximalIdeal, deningerUnderSpectrum_asIdeal]
  have htower := deningerLocalDegree_tower (R := ℤ) (S := 𝓞 K) (T := 𝓞 L)
    (p := Ideal.under ℤ Q) (P := Ideal.under (𝓞 K) Q) (Q := Q) hg0 hfg
  rw [deningerPlaceDegree, deningerPlaceDegree, hrestrict,
    Ideal.under_under (A := ℤ) (B := 𝓞 K) Q, htower]

end Tower

end RHTower
