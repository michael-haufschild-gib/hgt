import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

/-!
# Squares in a quadratic extension, and multiquadratic independence

The first brick of the elementary route to the generic Galois group of a parametrised
characteristic polynomial: over a field of characteristic `≠ 2`, adjoining `√a` creates exactly
one new square class, namely `a`.  Iterating, an element is a square in `F(√d₁, …, √d_k)` exactly
when some `d_S`-twist of it is a square in `F`, which is what makes a family of discriminants with
pairwise distinct irreducible factorisations Kummer-independent.

## Main results

* `isSquare_or_isSquare_mul_of_isSquare_algebraMap` — a base element that becomes a square in a
  quadratic extension is, up to the twist by the adjoined radicand, already a square.
* `not_isSquare_algebraMap` — hence a base non-square whose twist is also a non-square stays a
  non-square upstairs.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- In a quadratic extension `K(r)` with `r² = a` and `r` outside the base field, an element of
`K` that becomes a square is either a square in `K` or `a` times a square in `K`.  Only the
elements in the image of `r` need to be spanned, so this applies to any single element of a
`K`-span `{x + y r}`. -/
theorem isSquare_or_isSquare_mul_of_notMem
    [CharZero K] {a : K} {r : L} (hr : r * r = algebraMap K L a)
    (hrK : ∀ t : K, r ≠ algebraMap K L t)
    {c : K} {x y : K} (hz : algebraMap K L c =
      (algebraMap K L x + algebraMap K L y * r) * (algebraMap K L x + algebraMap K L y * r)) :
    IsSquare c ∨ IsSquare (a * c) := by
  have hexp : algebraMap K L c =
      algebraMap K L (x * x + a * (y * y)) + algebraMap K L (2 * (x * y)) * r := by
    rw [hz]
    simp only [map_add, map_mul, map_ofNat]
    linear_combination (algebraMap K L y * algebraMap K L y) * hr
  have hzero : algebraMap K L (2 * (x * y)) = 0 := by
    by_contra hne
    have hsolve : r = algebraMap K L ((c - (x * x + a * (y * y))) / (2 * (x * y))) := by
      have hne' : (2 * (x * y)) ≠ 0 := by
        intro h
        exact hne (by rw [h, map_zero])
      have hstep : algebraMap K L (2 * (x * y)) * r =
          algebraMap K L (c - (x * x + a * (y * y))) := by
        rw [map_sub]
        linear_combination -hexp
      rw [map_div₀, eq_div_iff hne, mul_comm]
      exact hstep
    exact hrK _ hsolve
  have hxy : x * y = 0 := by
    have h2 : (2 : K) * (x * y) = 0 := by
      have := hzero
      rwa [map_eq_zero] at this
    have h2ne : (2 : K) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp h2).resolve_left h2ne
  have hc' : c = x * x + a * (y * y) := by
    have hstep : algebraMap K L c = algebraMap K L (x * x + a * (y * y)) := by
      rw [hexp, hzero, zero_mul, add_zero]
    exact FaithfulSMul.algebraMap_injective K L hstep
  rcases mul_eq_zero.mp hxy with hx | hy
  · right
    refine ⟨a * y, ?_⟩
    rw [hc', hx]
    ring
  · left
    refine ⟨x, ?_⟩
    rw [hc', hy]
    ring

/-- The same with the base-field membership deduced from `a` being a non-square. -/
theorem isSquare_or_isSquare_mul_of_isSquare_algebraMap
    [CharZero K] {a : K} {r : L} (hr : r * r = algebraMap K L a) (ha : ¬ IsSquare a)
    (hspan : ∀ z : L, ∃ x y : K, z = algebraMap K L x + algebraMap K L y * r)
    {c : K} (hc : IsSquare (algebraMap K L c)) :
    IsSquare c ∨ IsSquare (a * c) := by
  obtain ⟨z, hz⟩ := hc
  obtain ⟨x, y, rfl⟩ := hspan z
  refine isSquare_or_isSquare_mul_of_notMem hr ?_ hz
  intro t hrt
  refine ha ⟨t, ?_⟩
  have hrr := hr
  rw [hrt, ← map_mul] at hrr
  exact (FaithfulSMul.algebraMap_injective K L hrr).symm

/-- A base element stays a non-square in the quadratic extension as soon as it and its
`a`-twist are non-squares downstairs. -/
theorem not_isSquare_algebraMap
    [CharZero K] {a : K} {r : L} (hr : r * r = algebraMap K L a) (ha : ¬ IsSquare a)
    (hspan : ∀ z : L, ∃ x y : K, z = algebraMap K L x + algebraMap K L y * r)
    {c : K} (hc : ¬ IsSquare c) (hac : ¬ IsSquare (a * c)) :
    ¬ IsSquare (algebraMap K L c) := by
  intro hsq
  rcases isSquare_or_isSquare_mul_of_isSquare_algebraMap hr ha hspan hsq with h | h
  · exact hc h
  · exact hac h

end GaloisForLFunctions.HTGeometry
