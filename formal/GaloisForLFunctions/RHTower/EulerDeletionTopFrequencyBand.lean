import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The isolated top-denominator Fourier band

The open frequency band `(1/N, 2/N)` contains no harmonic of order two or
higher from any residue modulus at most `N`. Its only frequencies are the
first harmonics `1/m` of moduli strictly between `N/2` and `N`.
This exact separation is the geometric reason that the top-denominator
coefficients cannot be cancelled by lower-order harmonics in a complete
period. No assertion about a time-windowed Fourier transform is made here.
-/

namespace RHTower

/-- Exact classification of residue harmonics in the top-denominator band. -/
theorem reciprocal_frequency_mem_top_band {N m t : ℕ}
    (hmN : m ≤ N) (hm : 0 < m) (ht : 0 < t) :
    ((1 : ℝ) / N < (t : ℝ) / m ∧
      (t : ℝ) / m < 2 / N) ↔
      t = 1 ∧ m < N ∧ N < 2 * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hm hmN
  have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
  constructor
  · rintro ⟨hlo, hhi⟩
    have hhi' : (t : ℝ) * N < 2 * m :=
      (div_lt_div_iff₀ hmR hNR).mp hhi
    have ht1 : t = 1 := by
      have htlt : t < 2 := by
        by_contra h
        have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (Nat.le_of_not_gt h)
        nlinarith
      omega
    subst t
    have hlo' : (m : ℝ) < N := by
      have h := (div_lt_div_iff₀ hNR hmR).mp hlo
      simpa using h
    refine ⟨rfl, ?_, ?_⟩
    · exact_mod_cast hlo'
    · have hhiR : (N : ℝ) < 2 * m := by simpa using hhi'
      exact_mod_cast hhiR
  · rintro ⟨rfl, hmN', hN2m⟩
    have hmN'R : (m : ℝ) < N := by exact_mod_cast hmN'
    have hN2mR : (N : ℝ) < 2 * m := by exact_mod_cast hN2m
    constructor
    · apply (div_lt_div_iff₀ hNR hmR).mpr
      simpa using hmN'R
    · apply (div_lt_div_iff₀ hmR hNR).mpr
      simpa using hN2mR

end RHTower
