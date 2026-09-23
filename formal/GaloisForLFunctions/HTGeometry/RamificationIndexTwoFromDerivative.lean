import GaloisForLFunctions.HTGeometry.KummerDedekindDifferentOrder
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Ramification index two from a derivative of divisorial order one

`KummerDedekindDifferentOrder.not_mem_pow_aeval_derivative` gives the upper bound
`p'(x) ∉ Q^e` for a monogenic order, and mathlib's `pow_sub_one_dvd_differentIdeal` gives the lower
bound `Q^(e-1) ∣ 𝔇`.  Since `p'(x) ∈ 𝔇` needs only that `x` generates the field extension
(`aeval_derivative_mem_differentIdeal`), the two bounds sandwich the order of `p'(x)` at `Q` at
exactly `e - 1` — **without** ever needing `𝔇 = span {p'(x)}`, i.e. without global monogenicity of
the integral closure.

```text
mem_pow_sub_one_aeval_derivative              p'(x) ∈ Q^(e-1)
ramificationIdx_eq_two_of_derivative_uniformizer
    ** p'(x) ∈ Q, p'(x) ∉ Q², p'(x) ∉ Q^e  ⟹  e = 2 **
```

This is the local half of the simple-fold statement `(R)` of the projective-horizon card, in the
form that avoids both of the routes previously contemplated: no localisation of the different
(mathlib carries none) and no proof that the conductor is the unit ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1600000

attribute [local instance] FractionRing.liftAlgebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
variable [Module.IsTorsionFree A B] [FaithfulSMul A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- The derivative of the minimal polynomial lies in the `(e-1)`-st power of a prime of
ramification index `e`. -/
theorem mem_pow_sub_one_aeval_derivative
    {x : B} {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) {Q : Ideal B} {e : ℕ}
    (hQ : Q ^ e ∣ p.map (algebraMap A B))
    (hx : Algebra.adjoin (FractionRing A)
      ({algebraMap B (FractionRing B) x} : Set (FractionRing B)) = ⊤) :
    Polynomial.aeval x (derivative (minpoly A x)) ∈ Q ^ (e - 1) := by
  have hd : Q ^ (e - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal A Q e hp hQ
  have hmem : Polynomial.aeval x (derivative (minpoly A x)) ∈ differentIdeal A B :=
    aeval_derivative_mem_differentIdeal A (FractionRing A) (FractionRing B) x hx
  exact (Ideal.dvd_iff_le.mp hd) hmem


/-- **A derivative of divisorial order exactly one forces ramification index two.**  Combining the
lower bound `Q^(e-1) ∣ 𝔇` with the Kummer–Dedekind upper bound `p'(x) ∉ Q^e`, an element of order
one pins `e = 2`: a simple fold. -/
theorem ramificationIdx_eq_two_of_derivative_uniformizer
    {x : B} {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) {Q : Ideal B} {e : ℕ}
    (hQdvd : Q ^ e ∣ p.map (algebraMap A B))
    (hxK : Algebra.adjoin (FractionRing A)
      ({algebraMap B (FractionRing B) x} : Set (FractionRing B)) = ⊤)
    (hnot : Polynomial.aeval x (derivative (minpoly A x)) ∉ Q ^ e)
    (hmemQ : Polynomial.aeval x (derivative (minpoly A x)) ∈ Q)
    (hnotsq : Polynomial.aeval x (derivative (minpoly A x)) ∉ Q ^ (2 : ℕ)) :
    e = 2 := by
  have hin : Polynomial.aeval x (derivative (minpoly A x)) ∈ Q ^ (e - 1) :=
    mem_pow_sub_one_aeval_derivative hp hQdvd hxK
  rcases Nat.lt_or_ge e 2 with hlt | hge
  · interval_cases e
    · exact absurd (by simp) hnot
    · exact absurd hmemQ (by simpa using hnot)
  · rcases eq_or_lt_of_le hge with heq | hgt
    · exact heq.symm
    · exfalso
      have h2 : (2 : ℕ) ≤ e - 1 := by omega
      exact hnotsq (Ideal.pow_le_pow_right h2 hin)

end GaloisForLFunctions.HTGeometry
