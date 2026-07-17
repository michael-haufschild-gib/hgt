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
import Mathlib.NumberTheory.Harmonic.Bounds

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

private theorem sum_inv_multiples_eq_harmonic (N d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (n : ℚ)⁻¹) =
      (d : ℚ)⁻¹ * harmonic (N / d) := by
  rw [harmonic_eq_sum_Icc, Finset.mul_sum]
  refine (Finset.sum_bij' (fun k _ => d * k) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk ⊢
    refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega),
      Nat.div_le_div_right hnN⟩
  · intro k _hk
    exact Nat.mul_div_cancel_left k (by omega)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k _hk
    simp [Nat.cast_mul]
    ring

/-- Finite Dirichlet-hyperbola swap with the reciprocal kernel.  Summing a divisor transform
against `1 / n` is the same as pairing each coefficient with the harmonic floor `H_(N / d) / d`.
This is the abstract finite convolution law behind the polar source normalization. -/
theorem divisorSummatory_reciprocal_harmonic (N : ℕ) (a : ℕ → ℚ) :
    (∑ d ∈ Finset.Icc 1 N, a d * (d : ℚ)⁻¹ * harmonic (N / d)) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℚ)⁻¹ * ∑ d ∈ n.divisors, a d := by
  symm
  calc
    (∑ n ∈ Finset.Icc 1 N, (n : ℚ)⁻¹ * ∑ d ∈ n.divisors, a d) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (n : ℚ)⁻¹ * a d := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [Finset.mul_sum]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (n : ℚ)⁻¹ * a d := by
      rw [Finset.sum_comm']
      intro n d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
        exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdn) hnN⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _⟩
        exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩
    _ = ∑ d ∈ Finset.Icc 1 N, a d * (d : ℚ)⁻¹ * harmonic (N / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      calc
        (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (n : ℚ)⁻¹ * a d) =
            (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (n : ℚ)⁻¹) * a d := by
              rw [Finset.sum_mul]
        _ = a d * (d : ℚ)⁻¹ * harmonic (N / d) := by
          rw [sum_inv_multiples_eq_harmonic N d hd1]
          ring

/-- The harmonic floor source is the exact Möbius inverse of the polar unit:
`∑_{d ≤ N} μ(d) H_{⌊N/d⌋} / d = 1` for every `N ≥ 1`. -/
theorem harmonicFloorMoebiusSum_eq_one (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) / (d : ℚ) * harmonic (N / d)) = 1 := by
  rw [show (∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℤ) : ℚ) / (d : ℚ) * harmonic (N / d)) =
      ∑ d ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (d : ℚ)⁻¹) *
          harmonic (N / d) by
    apply Finset.sum_congr rfl
    intro d _hd
    rw [div_eq_mul_inv]]
  rw [divisorSummatory_reciprocal_harmonic]
  have hmu (n : ℕ) :
      (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℚ)) =
        if n = 1 then 1 else 0 := by
    exact_mod_cast sum_moebius_divisors n
  simp_rw [hmu]
  simp [hN]

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
