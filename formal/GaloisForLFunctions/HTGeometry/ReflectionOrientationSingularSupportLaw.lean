import Mathlib.Algebra.Regular.Basic
import Mathlib.Tactic

/-!
# Reflection orientation is supported on the singular hyperbolic locus

Let `ε` be an involutive orientation class and let `h = 1 + ε` be its
reflection-symmetric (hyperbolic) channel.  The factorization

`(1 - ε) (1 + ε) = 0`

has a sharp consequence: if `h` is a non-zero-divisor, then `ε = 1` and the
orientation is trivial.  Conversely, when `2` is a non-zero-divisor, a
nontrivial orientation is equivalent to singularity of `h`.

This is stronger than a localization or positivity statement.  Invertibility
is unnecessary; mere regularity already erases orientation.  The module form
requires even less structure: every anti-invariant vector is annihilated by
`h`, so an injective hyperbolic action has no nonzero orientation sector.
-/

namespace GaloisForLFunctions.HTGeometry

section Ring

variable {A : Type*} [CommRing A]

/-- The anti-invariant and invariant reflection factors annihilate each other. -/
theorem reflectionOrientation_mul_hyperbolic_eq_zero
    (epsilon : A) (hsquare : epsilon ^ 2 = 1) :
    (1 - epsilon) * (1 + epsilon) = 0 := by
  calc
    (1 - epsilon) * (1 + epsilon) = 1 - epsilon ^ 2 := by ring
    _ = 0 := by rw [hsquare, sub_self]

/-- **Orientation--regularity law.**  A regular hyperbolic channel forces an involutive
orientation to be trivial.  No positivity or inverse is assumed. -/
theorem reflectionOrientation_eq_one_of_hyperbolic_regular
    (epsilon : A) (hsquare : epsilon ^ 2 = 1)
    (hregular : IsRegular (1 + epsilon)) :
    epsilon = 1 := by
  have hfactor := reflectionOrientation_mul_hyperbolic_eq_zero epsilon hsquare
  have hcancel : (1 - epsilon) * (1 + epsilon) = 0 * (1 + epsilon) := by
    simpa using hfactor
  have hsub : 1 - epsilon = 0 := hregular.right hcancel
  exact (sub_eq_zero.mp hsub).symm

/-- **Singular-support classification.**  If `2` is regular, nontrivial reflection
orientation is equivalent to failure of regularity of the hyperbolic channel. -/
theorem reflectionOrientation_ne_one_iff_hyperbolic_not_regular
    (epsilon : A) (hsquare : epsilon ^ 2 = 1)
    (htwo : IsRegular (2 : A)) :
    epsilon ≠ 1 ↔ ¬ IsRegular (1 + epsilon) := by
  constructor
  · intro hne hregular
    exact hne (reflectionOrientation_eq_one_of_hyperbolic_regular
      epsilon hsquare hregular)
  · intro hnot heq
    subst epsilon
    apply hnot
    rw [show (1 + 1 : A) = 2 by norm_num]
    exact htwo

/-- Every scalar consumer whose image of the hyperbolic class is regular forgets
the orientation class. -/
theorem map_reflectionOrientation_eq_one_of_hyperbolic_regular
    {B : Type*} [CommRing B] (f : A →+* B)
    (epsilon : A) (hsquare : epsilon ^ 2 = 1)
    (hregular : IsRegular (f (1 + epsilon))) :
    f epsilon = 1 := by
  apply reflectionOrientation_eq_one_of_hyperbolic_regular (f epsilon)
  · rw [← map_pow, hsquare, map_one]
  · simpa using hregular

end Ring

section Module

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- Every anti-invariant vector is torsion for the hyperbolic channel. -/
theorem hyperbolic_smul_antiInvariant_eq_zero
    (epsilon : A) (v : M) (hanti : epsilon • v = -v) :
    (1 + epsilon) • v = 0 := by
  rw [add_smul, one_smul, hanti, add_neg_cancel]

/-- An injective hyperbolic action has no nonzero anti-invariant orientation sector. -/
theorem antiInvariant_eq_zero_of_hyperbolic_smul_injective
    (epsilon : A) (v : M) (hanti : epsilon • v = -v)
    (hinjective : Function.Injective (fun w : M => (1 + epsilon) • w)) :
    v = 0 := by
  apply hinjective
  change (1 + epsilon) • v = (1 + epsilon) • (0 : M)
  rw [hyperbolic_smul_antiInvariant_eq_zero epsilon v hanti, smul_zero]

end Module

end GaloisForLFunctions.HTGeometry
