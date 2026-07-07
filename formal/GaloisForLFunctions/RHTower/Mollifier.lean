/-
The Möbius mollifier and its defining cancellation.

The mollifier `M_y(t) = ∑_{m≤y} μ(m) m^{-it}` (a Dirichlet polynomial with Möbius coefficients) is the
device that detects ζ-zeros: `ζ·M ≈ 1` on the strip, so at a zero `ρ` the value `1 − ζ(ρ)M(ρ) = 1` is
large, and the built large-values inequality (`LargeValuesDpoly.large_values_dpoly`) bounds the number
of such large values by the mollifier's small second moment.

The algebraic heart is the Möbius cancellation `∑_{d∣n} μ(d) = [n = 1]` (`sum_moebius_divisors`, from
mathlib's `μ * ζ = 1`): it makes the Dirichlet convolution coefficients of `ζ·M` vanish for
`1 < n ≤ min(N, y)`, so through the built Euler–Maclaurin AFE the detection polynomial `1 − (∑_{n≤N}
n^{-it})·M` is supported on `n > min(N,y)` and has small `L²` mass — the input Carlson's optimization
turns into `N(σ,T) = o(T)`.

This file banks the cancellation identity and the mollifier as a `SecondMoment.dpoly`, so its second
moment is a Montgomery–Vaughan instance with `‖coefficients‖ = |μ(m)| ≤ 1`.
-/
import GaloisForLFunctions.RHTower.SecondMoment
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Nat ArithmeticFunction Finset

namespace RHTower

/-- **The Möbius cancellation.**  `∑_{d ∣ n} μ(d) = 1` if `n = 1` and `0` otherwise — the divisor sum
of the Möbius function, from `ζ * μ = 1`.  This is what makes the mollified Dirichlet convolution
collapse to its constant term. -/
theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) coe_zeta_mul_moebius
  simp only at h
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at h
  rw [← h]

/-- The Möbius mollifier coefficients `a_m = μ(m)` (as reals). -/
noncomputable def moebiusCoeff (m : ℕ) : ℝ := (ArithmeticFunction.moebius m : ℝ)

/-- The coefficients are bounded by `1` in absolute value: `|μ(m)| ≤ 1`. -/
theorem abs_moebiusCoeff_le_one (m : ℕ) : |moebiusCoeff m| ≤ 1 := by
  rw [moebiusCoeff, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The **Möbius mollifier** `M_y(t) = ∑_{m≤y} μ(m) m^{-it}` as a Dirichlet polynomial. -/
noncomputable def mollifier (y : ℕ) (t : ℝ) : ℂ := dpoly moebiusCoeff (Finset.Icc 1 y) t

theorem mollifier_eq_dpoly (y : ℕ) (t : ℝ) :
    mollifier y t = dpoly moebiusCoeff (Finset.Icc 1 y) t := rfl

/-- **The mollifier's second moment** over a window `[T, T+U]` is the Montgomery–Vaughan mean value
with squarefree-supported diagonal `∑_{m≤y} μ(m)² m^{0}` plus the explicit off-diagonal remainder. -/
theorem mollifier_secondMoment (y : ℕ) (T U : ℝ) :
    (∫ t in T..T + U, ‖mollifier y t‖ ^ 2)
      = U * (∑ m ∈ Finset.Icc 1 y, (moebiusCoeff m) ^ 2)
        + ∑ m ∈ Finset.Icc 1 y, ∑ n ∈ (Finset.Icc 1 y).erase m,
            moebiusCoeff m * moebiusCoeff n * cosInt (Real.log n - Real.log m) T U := by
  simp only [mollifier]
  exact secondMoment_meanValue moebiusCoeff (Finset.Icc 1 y) T U

end RHTower
