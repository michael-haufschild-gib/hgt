import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Hyperbolic localization forces the Gamma rank channel

For an involutive quadratic orientation class `epsilon`, the hyperbolic element is
`1 + epsilon`.  If that element becomes invertible, the signature component vanishes:
`epsilon = 1`.  Hence every Milnor--Witt quadratic degree becomes ordinary rank.

These are universal algebraic consequences of a Gamma boundary that inverts the
hyperbolic class.  Construction and positivity of that boundary are separate.
-/

namespace RHTower

section HyperbolicLocalization

variable {A : Type*} [CommRing A]

/--
Inverting the hyperbolic class `1 + epsilon` forces an involutive orientation
class to equal its rank value.
-/
theorem deningerHyperbolicLocalization_epsilon_eq_one
    (epsilon hyperbolicInv : A)
    (hsquare : epsilon ^ 2 = 1)
    (hinverse : (1 + epsilon) * hyperbolicInv = 1) :
    epsilon = 1 := by
  have hfactor : (1 - epsilon) * (1 + epsilon) = 0 := by
    calc
      (1 - epsilon) * (1 + epsilon) = 1 - epsilon ^ 2 := by ring
      _ = 0 := by rw [hsquare, sub_self]
  have hcollapse : 1 - epsilon = 0 := by
    calc
      1 - epsilon = (1 - epsilon) * 1 := by simp
      _ = (1 - epsilon) * ((1 + epsilon) * hyperbolicInv) := by
        rw [hinverse]
      _ = ((1 - epsilon) * (1 + epsilon)) * hyperbolicInv := by
        rw [← mul_assoc]
      _ = 0 := by rw [hfactor, zero_mul]
  exact (sub_eq_zero.mp hcollapse).symm

/--
After hyperbolic localization, a Milnor--Witt quadratic integer is ordinary
finite-syntomic degree.
-/
theorem deningerHyperbolicLocalization_quadraticInteger_eq_degree
    (epsilon hyperbolicInv : A)
    (hsquare : epsilon ^ 2 = 1)
    (hinverse : (1 + epsilon) * hyperbolicInv = 1)
    (n : ℕ) :
    (∑ j ∈ Finset.range n, epsilon ^ j) = n • (1 : A) := by
  have hepsilon :
      epsilon = 1 :=
    deningerHyperbolicLocalization_epsilon_eq_one
      epsilon hyperbolicInv hsquare hinverse
  simp [hepsilon]

end HyperbolicLocalization

end RHTower
