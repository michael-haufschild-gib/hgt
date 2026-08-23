import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Algebra.ZMod

/-!
# A field with torsion unit group is algebraic over a finite field

If every unit of a field has finite order then the characteristic cannot be zero, because `2` has
infinite multiplicative order in a field of characteristic zero; and in characteristic `p` every
element is a root of some `X^n - 1`, hence algebraic over the prime field.
-/

namespace HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- In characteristic zero the unit `2` has infinite order, so a field whose units are all torsion
has positive characteristic. -/
theorem not_charZero_of_torsion_units (h : ∀ y : Kˣ, IsOfFinOrder y) : ¬ CharZero K := by
  intro hchar
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (h (Units.mk0 (2 : K) h2))
  have hval : (2 : K) ^ n = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hpow
    simpa using this
  have hnat : ((2 ^ n : ℕ) : K) = ((1 : ℕ) : K) := by
    push_cast
    exact hval
  have hn1 : (2 : ℕ) ^ n = 1 := Nat.cast_injective hnat
  have hlt : 1 < (2 : ℕ) ^ n := Nat.one_lt_pow (by omega) (by omega)
  omega

/-- **A field all of whose units are torsion is algebraic over its prime field.**  Every element is
a root of `X ^ n - 1` for some `n ≥ 1`, or is zero. -/
theorem isAlgebraic_of_torsion_units {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (h : ∀ y : Kˣ, IsOfFinOrder y) : Algebra.IsAlgebraic (ZMod p) K := by
  refine ⟨fun a => ?_⟩
  by_cases ha : a = 0
  · rw [ha]
    exact isAlgebraic_zero
  · obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (h (Units.mk0 a ha))
    have hval : a ^ n = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hpow
      simpa using this
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · have hne := Polynomial.X_pow_sub_C_ne_zero (R := ZMod p) hn 1
      simpa using hne
    · simp [hval]

end HTGeometry
