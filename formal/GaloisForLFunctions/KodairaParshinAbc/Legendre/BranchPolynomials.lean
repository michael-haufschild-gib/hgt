import GaloisForLFunctions.Bottcher.FixedPointSeparable
import Mathlib.Tactic

/-!
# Polynomial fibers and ramification of the Legendre invariant

The identity `4 L³ - M² = 27 D` separates the two elliptic fibers of the degree-six
Legendre map. Its derivative numerator factors as `256 L² M X (X-1)`. Consequently,
every repeated root of a fiber lies over `0` or `1728`.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

variable {R : Type*} [CommRing R]

def quadratic : R[X] := X ^ 2 - X + 1
def cubic : R[X] := (X + 1) * (X - 2) * (2 * X - 1)
def denominator : R[X] := X ^ 2 * (X - 1) ^ 2
def numerator : R[X] := 256 * quadratic ^ 3
def fiber (a : R) : R[X] := numerator - C a * denominator

/-- The elliptic branch identity, valid over every commutative ring. -/
theorem elliptic_identity :
    4 * (quadratic : R[X]) ^ 3 - cubic ^ 2 = 27 * denominator := by
  simp only [quadratic, cubic, denominator]
  ring

/-- The fiber over `1728` is the square of the cubic branch polynomial. -/
theorem fiber_1728 : fiber (1728 : R) = 64 * cubic ^ 2 := by
  simp only [fiber, numerator, quadratic, denominator, cubic, map_ofNat]
  ring

/-- The fiber over zero is the cube of the quadratic branch polynomial. -/
theorem fiber_zero : fiber (0 : R) = 256 * quadratic ^ 3 := by
  simp only [fiber, map_zero, zero_mul, sub_zero, numerator]

/-- Clearing the derivative of `N/D` exposes exactly the elliptic branch factors. -/
theorem derivative_cross_product :
    (numerator : R[X]).derivative * denominator - numerator * denominator.derivative =
      256 * quadratic ^ 2 * cubic * X * (X - 1) := by
  simp only [numerator, quadratic, denominator, cubic, derivative_mul, derivative_pow,
    derivative_sub, derivative_add, derivative_X, derivative_one, derivative_ofNat,
    Nat.cast_ofNat, map_ofNat, Nat.reduceSub]
  ring

/-- The derivative cross-product does not depend on the chosen fiber value. -/
theorem fiber_derivative_cross_product (a : R) :
    (fiber a).derivative * denominator - fiber a * denominator.derivative =
      256 * quadratic ^ 2 * cubic * X * (X - 1) := by
  rw [fiber, derivative_sub, derivative_mul, derivative_C]
  linear_combination derivative_cross_product (R := R)

@[simp] theorem fiber_eval_zero (a : R) : (fiber a).eval 0 = 256 := by
  simp [fiber, numerator, quadratic, denominator]

@[simp] theorem fiber_eval_one (a : R) : (fiber a).eval 1 = 256 := by
  simp [fiber, numerator, quadratic, denominator]

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- All multiple roots of a Legendre fiber lie above the two elliptic values. -/
theorem fiber_multiple_root_values (a z : K) :
    (fiber a).eval z ≠ 0 ∨ (fiber a).derivative.eval z ≠ 0 ∨ a = 0 ∨ a = 1728 := by
  by_contra h
  push Not at h
  obtain ⟨hf, hd, ha0, ha1728⟩ := h
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, fiber_eval_zero] at hf
    norm_num at hf
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz, fiber_eval_one] at hf
    norm_num at hf
  have hden : (denominator : K[X]).eval z ≠ 0 := by
    simpa only [denominator, eval_mul, eval_pow, eval_sub, eval_X, eval_one] using
      mul_ne_zero (pow_ne_zero 2 hz0) (pow_ne_zero 2 (sub_ne_zero.mpr hz1))
  have hcross := congrArg (Polynomial.eval z) (fiber_derivative_cross_product a)
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one, hf, hd,
    zero_mul, sub_zero] at hcross
  have hbranches : (quadratic : K[X]).eval z = 0 ∨ (cubic : K[X]).eval z = 0 := by
    have hprod := hcross.symm
    rcases mul_eq_zero.mp hprod with hprod | hlast
    · rcases mul_eq_zero.mp hprod with hprod | hz
      · rcases mul_eq_zero.mp hprod with hprod | hm
        · rcases mul_eq_zero.mp hprod with hconst | hl
          · norm_num at hconst
          · exact Or.inl (sq_eq_zero_iff.mp hl)
        · exact Or.inr hm
      · exact (hz0 hz).elim
    · exact (sub_ne_zero.mpr hz1 hlast).elim
  rcases hbranches with hl | hm
  · have hfe : -(a * (denominator : K[X]).eval z) = 0 := by
      simpa [fiber, numerator, hl] using hf
    exact ha0 ((mul_eq_zero.mp (neg_eq_zero.mp hfe)).resolve_right hden)
  · have h1728 : (numerator : K[X]).eval z = 1728 * (denominator : K[X]).eval z := by
      have he := congrArg (Polynomial.eval z) (fiber_1728 (R := K))
      simp only [fiber, eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow, hm] at he
      norm_num at he
      exact sub_eq_zero.mp he
    have hfe : (1728 - a) * (denominator : K[X]).eval z = 0 := by
      simpa only [fiber, eval_sub, eval_mul, eval_C, h1728, ← sub_mul] using hf
    exact ha1728 ((sub_eq_zero.mp ((mul_eq_zero.mp hfe).resolve_right hden)).symm)

end Field

/-- Away from the elliptic values the complex fiber polynomial has no repeated roots. -/
theorem fiber_separable {a : ℂ} (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    (fiber a).Separable := by
  apply Bottcher.separable_of_derivative_ne_zero_at_roots
  · intro h
    have he := congrArg (Polynomial.eval 0) h
    rw [fiber_eval_zero, eval_zero] at he
    norm_num at he
  · intro z hz
    rcases fiber_multiple_root_values a z with h | h | h | h
    · exact (h hz).elim
    · exact h
    · exact (ha0 h).elim
    · exact (ha1728 h).elim

end GaloisForLFunctions.KodairaParshinAbc.Legendre
