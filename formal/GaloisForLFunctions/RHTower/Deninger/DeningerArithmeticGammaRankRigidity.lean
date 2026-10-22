import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Gamma rank-character rigidity for Deninger's arithmetic cohomology

The real Grothendieck--Witt algebra has an involutive class
`epsilon = <-1>` and hyperbolic class `1 + epsilon`.  A real ring character
that is strictly positive on the hyperbolic class cannot be the signature
character: it must send `epsilon` to `1`.  Consequently it sends the
Milnor--Witt quadratic integer

`1 + epsilon + ... + epsilon^(n-1)`

to the ordinary degree `n`.

This is the scalar rigidity input required by the polarized-transfer
half-density law.  It does not construct the Gamma realization itself.
-/

namespace RHTower

/--
An involutive real scalar whose hyperbolic sum is strictly positive is the
rank value `1`, not the signature value `-1`.
-/
theorem deningerGammaRank_of_sq_eq_one_of_one_add_pos
    {epsilon : ℝ}
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hhyperbolic : 0 < 1 + epsilon) :
    epsilon = 1 := by
  have hfactor : (epsilon - 1) * (epsilon + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · linarith
  · linarith

/--
Universal character form: positivity on the hyperbolic class forces every
unital real character to take the rank value on an involutive orientation
class.
-/
theorem deningerGammaCharacter_maps_epsilon_to_rank
    {A : Type*} [Ring A]
    (character : A →+* ℝ) (epsilon : A)
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hhyperbolic : 0 < character (1 + epsilon)) :
    character epsilon = 1 := by
  apply deningerGammaRank_of_sq_eq_one_of_one_add_pos
  · rw [← map_pow, hsquare, map_one]
  · simpa using hhyperbolic

/--
Once the positive character is forced to be rank, every Milnor--Witt
quadratic integer maps to its ordinary finite-syntomic degree.
-/
theorem deningerGammaCharacter_maps_quadraticInteger_to_degree
    {A : Type*} [Ring A]
    (character : A →+* ℝ) (epsilon : A)
    (hsquare : epsilon ^ (2 : ℕ) = 1)
    (hhyperbolic : 0 < character (1 + epsilon))
    (n : ℕ) :
    character (∑ j ∈ Finset.range n, epsilon ^ j) = (n : ℝ) := by
  have hepsilon :
      character epsilon = 1 :=
    deningerGammaCharacter_maps_epsilon_to_rank
      character epsilon hsquare hhyperbolic
  simp [hepsilon]

end RHTower
