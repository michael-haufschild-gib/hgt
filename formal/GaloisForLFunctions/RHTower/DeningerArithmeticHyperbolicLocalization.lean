import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

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
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hinverse : (1 + epsilon) * hyperbolicInv = 1) :
    epsilon = 1 := by
  have hfactor : (1 - epsilon) * (1 + epsilon) = 0 := by
    calc
      (1 - epsilon) * (1 + epsilon) = 1 - epsilon ^ (2 : ℕ) := by ring
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
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hinverse : (1 + epsilon) * hyperbolicInv = 1)
    (n : ℕ) :
    (∑ j ∈ Finset.range n, epsilon ^ j) = n • (1 : A) := by
  have hepsilon :
      epsilon = 1 :=
    deningerHyperbolicLocalization_epsilon_eq_one
      epsilon hyperbolicInv hsquare hinverse
  simp [hepsilon]

end HyperbolicLocalization

section HyperbolicPushPull

variable {A V : Type*}
variable [CommRing A] [AddCommGroup V] [Module A V]

/--
The Milnor--Witt push--pull formula becomes ordinary degree after passage to
the hyperbolically localized coefficient channel.
-/
theorem deningerHyperbolicLocalization_push_pull_eq_degree
    (epsilon hyperbolicInv : A)
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hinverse : (1 + epsilon) * hyperbolicInv = 1)
    (pull push : V → V)
    (n : ℕ)
    (hquadraticDegree :
      ∀ v, push (pull v) =
        (∑ j ∈ Finset.range n, epsilon ^ j) • v)
    (v : V) :
    push (pull v) = (n : A) • v := by
  rw [hquadraticDegree,
    deningerHyperbolicLocalization_quadraticInteger_eq_degree
      epsilon hyperbolicInv hsquare hinverse n]
  simp

end HyperbolicPushPull

end RHTower
