import GaloisForLFunctions.HTGeometry.CircuitCountingCollisionBound

/-!
# The replica budget follows from a small spectral collision

`(43)` of the arithmetic hardness–recurrence card.  The corpus already owns the two halves —
`factorial_mul_pow_le_two_pow_neg` (the replica factor below the reciprocal collision scale) and
`card_mul_two_pow_le_rpow` (a dictionary whose logarithm is below half the replica order).  What is
added here is the arithmetic that produces the reciprocal-collision-scale hypothesis from the card's
own constants: a collision below `4(2/3)ⁿ` together with `r ≤ (a₀²/128)(3/2)ⁿ`.

## Main results

* `collision_scale_le_of_small_collision` — `16C/a₀² ≤ 1/(2r)`.
* `replica_budget_of_small_collision` — **`(42)`–`(43)`: the budget `(22)` is below one.**
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- **The reciprocal collision scale from the card's constants.** -/
theorem collision_scale_le_of_small_collision {a₀ Cn : ℝ} (ha₀ : 0 < a₀) (hCnn : 0 ≤ Cn)
    {n r : ℕ} (hr1 : 1 ≤ r) (hC : Cn < 4 * (2 / 3 : ℝ) ^ n)
    (hrle : (r : ℝ) ≤ (a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) :
    16 * Cn / a₀ ^ 2 ≤ 1 / (2 * (r : ℝ)) := by
  have ha2 : (0 : ℝ) < a₀ ^ 2 := by positivity
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hprod : (3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hkey : (r : ℝ) * (16 * Cn / a₀ ^ 2) ≤ 1 / 2 := by
    have h1 : 16 * Cn / a₀ ^ 2 ≤ 64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2 := by
      rw [div_le_div_iff_of_pos_right ha2]
      linarith
    have h2 : (r : ℝ) * (16 * Cn / a₀ ^ 2) ≤ (r : ℝ) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hrpos)
    have hqnn : (0 : ℝ) ≤ 64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2 := by positivity
    have h3 : (r : ℝ) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2)
        ≤ ((a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hrle hqnn
    have h4 : ((a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) = 1 / 2 := by
      field_simp
      nlinarith [hprod]
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **`(42)`–`(43)`.**  A dictionary of at most `M^{s+1}` targets whose logarithm is below half the
replica order satisfies the replica budget `(22)` as soon as the spectral collision is below
`4(2/3)ⁿ` and `r ≤ (a₀²/128)(3/2)ⁿ`. -/
theorem replica_budget_of_small_collision {a₀ Cn M N : ℝ} (ha₀ : 0 < a₀) (hCnn : 0 ≤ Cn)
    {n r s : ℕ} (hr1 : 1 ≤ r) (hC : Cn < 4 * (2 / 3 : ℝ) ^ n)
    (hrle : (r : ℝ) ≤ (a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n)
    (hN0 : 0 ≤ N) (hM : 1 < M) (hNle : N ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    N * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r < 1 := by
  have hX : (0 : ℝ) ≤ 16 * Cn / a₀ ^ 2 := by positivity
  have hscale := collision_scale_le_of_small_collision ha₀ hCnn hr1 hC hrle
  have hmom : (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r ≤ (1 / 2 : ℝ) ^ r :=
    factorial_mul_pow_le_two_pow_neg r hr1 hX hscale
  have hdict : N * (1 / 2 : ℝ) ^ r ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) :=
    card_mul_two_pow_le_rpow hN0 hM hNle hs
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hlast : (2 : ℝ) ^ (-((r : ℝ) / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc N * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r
      = N * ((r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r) := by ring
    _ ≤ N * (1 / 2 : ℝ) ^ r := mul_le_mul_of_nonneg_left hmom hN0
    _ ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := hdict
    _ < 1 := hlast

end GaloisForLFunctions.HTGeometry
