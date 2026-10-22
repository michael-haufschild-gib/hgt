import GaloisForLFunctions.RHTower.Deninger.DeningerFinitePlaceSumBaseChange
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia

/-!
# The local degree of a prime

The local degree of a prime over a prime below it is `e · f`.  It is multiplicative in towers,
because both the ramification index and the inertia degree are, and the local degrees of the
primes above a fixed prime add up to the degree of the extension.

These two facts are what normalizes the place space: weighting a place by its local degree over
`ℚ` and dividing by the absolute degree gives a weight that is unchanged by enlarging the field.

* `deningerLocalDegree` : the local degree `e · f`.
* `deningerLocalDegree_tower` : multiplicativity in a tower.
* `deningerLocalDegree_sum` : the fibre sum is the degree of the extension.
-/

namespace RHTower

open NumberField IsDedekindDomain Module

section LocalDegree

/-- The local degree of a prime `P` of `S` over a prime `p` of `R`: the product of the
ramification index and the inertia degree. -/
noncomputable def deningerLocalDegree {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (P : Ideal S) : ℕ :=
  p.ramificationIdx' P * p.inertiaDeg' P

/-- **The local degree is multiplicative in a tower.** -/
theorem deningerLocalDegree_tower {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsDedekindDomain S] [IsDedekindDomain T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] {p : Ideal R} {P : Ideal S} {Q : Ideal T} [p.IsMaximal] [P.IsMaximal]
    [hQ : Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hg0 : Ideal.map (algebraMap S T) P ≠ ⊥)
    (hfg : Ideal.map (algebraMap R T) p ≠ ⊥) :
    deningerLocalDegree p Q = deningerLocalDegree p P * deningerLocalDegree P Q := by
  have hle : Ideal.map (algebraMap S T) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Q.over_def P)
  have he := Ideal.ramificationIdx'_algebra_tower (p := p) (P := P) (Q := Q)
    hg0 hfg hle
  have hf := Ideal.inertiaDeg'_algebra_tower p P Q
  unfold deningerLocalDegree
  rw [he, hf]
  ring

end LocalDegree

section NumberFieldTower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The fibre sum of local degrees is the degree of the extension.** -/
theorem deningerLocalDegree_sum (v : HeightOneSpectrum (𝓞 K)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L),
        deningerLocalDegree v.asIdeal P = finrank K L := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  exact Ideal.sum_ramification_inertia (𝓞 L) K L v.ne_bot

end NumberFieldTower

end RHTower
