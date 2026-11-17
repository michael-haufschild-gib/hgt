import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Polynomial vector fields preserving a fat point

The constant coefficient is the only obstruction, and it disappears exactly when the characteristic divides the multiplicity.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Differential
open Polynomial
variable {K : Type*} [Field K]

/-- Preservation of the full multiplicity ideal by the polynomial vector field `g d/dX`. -/
def PreservesPowerIdeal (m : ℕ) (g : K[X]) : Prop :=
  ∀ P : K[X], X ^ m ∣ P → X ^ m ∣ g * derivative P

/-- A polynomial vector field preserves a fat point exactly when its constant term is killed by the multiplicity. -/
theorem preservesPowerIdeal_iff (m : ℕ) (g : K[X]) :
    PreservesPowerIdeal m g ↔ (m : K) = 0 ∨ g.coeff 0 = 0 := by
  by_cases hm : m = 0
  · subst m
    simp only [PreservesPowerIdeal, pow_zero, one_dvd, implies_true,
      Nat.cast_zero, true_or]
  have hpos : 0 < m := Nat.pos_of_ne_zero hm
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h (X ^ m) (dvd_refl _)
    have hc := congrArg (fun P : K[X] => P.coeff (m - 1)) hq
    rw [derivative_X_pow,
      show g * (C (m : K) * X ^ (m - 1)) = C (m : K) * (X ^ (m - 1) * g) by ring,
      coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul'] at hc
    have he : (m : K) * g.coeff 0 = 0 := by
      simpa only [if_pos (le_refl (m - 1)), Nat.sub_self,
        if_neg (by omega : ¬ m ≤ m - 1)] using hc
    exact mul_eq_zero.mp he
  · rintro (hcast | hg) P ⟨q, rfl⟩
    · refine ⟨g * derivative q, ?_⟩
      rw [derivative_mul, derivative_X_pow, hcast, C_0, zero_mul, zero_mul, zero_add]
      ring
    · obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hg
      refine ⟨C (m : K) * h * q + X * h * derivative q, ?_⟩
      rw [derivative_mul, derivative_X_pow]
      have hx : (X : K[X]) ^ m = X * X ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hx]
      ring

/-- Ordinary differentiation descends through `X^m` exactly at characteristic-divisible multiplicity. -/
theorem ordinary_derivative_preserves_iff (m : ℕ) :
    (∀ P : K[X], X ^ m ∣ P → X ^ m ∣ derivative P) ↔ (m : K) = 0 := by
  simpa only [PreservesPowerIdeal, one_mul, coeff_one_zero, one_ne_zero, or_false] using
    preservesPowerIdeal_iff m (1 : K[X])

/-- The logarithmic Euler field preserves every multiplicity, in every characteristic. -/
theorem euler_preserves_power_ideal (m : ℕ) : PreservesPowerIdeal m (X : K[X]) :=
  (preservesPowerIdeal_iff m X).mpr (Or.inr coeff_X_zero)

/-- In characteristic zero, all descending polynomial vector fields vanish at the thickening's support. -/
theorem preservesPowerIdeal_iff_constant_zero [CharZero K] (m : ℕ) (hm : 0 < m) (g : K[X]) :
    PreservesPowerIdeal m g ↔ g.coeff 0 = 0 := by
  rw [preservesPowerIdeal_iff, or_iff_right (Nat.cast_ne_zero.mpr hm.ne')]

#print axioms preservesPowerIdeal_iff
#print axioms ordinary_derivative_preserves_iff
#print axioms euler_preserves_power_ideal
end GaloisForLFunctions.RepresentationLifting.Differential
