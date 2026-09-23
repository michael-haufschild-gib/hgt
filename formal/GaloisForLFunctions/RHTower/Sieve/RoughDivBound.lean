import Mathlib

/-!
# Normalising the discarded-part bound

The discarded part of the fibre mean square comes out as `(2h+1)·2·(A + ⌊h⌋·B)`, and the mean square
is normalised by `h²·√x`.  Since `2h+1 ≤ 3h` and `⌊h⌋ ≤ h`, that quotient splits into a term with an
extra factor `1/h` and a term without — the two orders the parameter choice has to compare against.
-/

namespace RHTower.Sieve

open Finset

/-- **The normalised discarded-part bound.** -/
theorem rough_div_bound {h s A B : ℝ} (hh1 : 1 ≤ h) (hs : 0 < s) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B))) / (h ^ (2 : ℕ) * s)
      ≤ 6 * A / (h * s) + 6 * B / s := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hden : (0 : ℝ) < h ^ (2 : ℕ) * s := by positivity
  have hfl : ((⌊h⌋₊ : ℕ) : ℝ) ≤ h := Nat.floor_le (by linarith)
  have hnum : (2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B)) ≤ 6 * h * A + 6 * h ^ (2 : ℕ) * B := by
    have h3 : 2 * h + 1 ≤ 3 * h := by linarith
    have hinner : A + ((⌊h⌋₊ : ℕ) : ℝ) * B ≤ A + h * B := by nlinarith [hB, hfl]
    have hpos : (0 : ℝ) ≤ A + ((⌊h⌋₊ : ℕ) : ℝ) * B := by
      have : (0 : ℝ) ≤ ((⌊h⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hA, hB, this]
    nlinarith [h3, hinner, hpos, hA, hB, hh0]
  have hval : (6 * h * A + 6 * h ^ (2 : ℕ) * B) / (h ^ (2 : ℕ) * s) = 6 * A / (h * s) + 6 * B / s := by
    field_simp
  calc ((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B))) / (h ^ (2 : ℕ) * s)
      ≤ (6 * h * A + 6 * h ^ (2 : ℕ) * B) / (h ^ (2 : ℕ) * s) :=
        (div_le_div_iff_of_pos_right hden).mpr hnum
    _ = 6 * A / (h * s) + 6 * B / s := hval

end RHTower.Sieve
