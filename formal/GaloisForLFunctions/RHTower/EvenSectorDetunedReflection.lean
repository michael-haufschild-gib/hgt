import GaloisForLFunctions.RHTower.EvenSectorNegPartAbelRigidity

/-!
# Arithmetic separation of reflected logarithmic packets

A common rational shift preserves every ratio of integer nodes and moves every
reflected product off the integer lattice. The separation is uniform over a
finite packet and has polynomial inverse width.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section
namespace RHTower.EvenSector.Detuned

def denominator (N : ℕ) : ℕ := 2 * N ^ 2 + 2
def height (N : ℕ) : ℕ := (denominator N + 1) * N ^ 2
def width (N : ℕ) : ℝ := 1 / ((height N : ℝ) + 1)
def shift (N : ℕ) : ℝ :=
  (Real.log (denominator N + 1 : ℕ) - Real.log (denominator N)) / 2
def center (N m : ℕ) : ℝ := Real.log m + shift N

theorem denominator_pos (N : ℕ) : 0 < denominator N := by
  unfold denominator
  omega

theorem width_pos (N : ℕ) : 0 < width N := by
  unfold width
  positivity

theorem shift_pos (N : ℕ) : 0 < shift N := by
  have hM : (0 : ℝ) < denominator N := by exact_mod_cast denominator_pos N
  have h := Real.log_lt_log hM (show (denominator N : ℝ) < (denominator N + 1 : ℕ) by
    push_cast
    linarith)
  unfold shift
  linarith

theorem center_pos (N m : ℕ) : 0 < center N m := by
  unfold center
  linarith [Real.log_natCast_nonneg m, shift_pos N]

theorem le_height {N : ℕ} (hN : 1 ≤ N) : N ≤ height N := by
  have hsq : N ≤ N ^ 2 := by nlinarith
  unfold height
  nlinarith [denominator_pos N]

theorem width_le_integer_gap {N : ℕ} (hN : 1 ≤ N) :
    width N ≤ 1 / ((N : ℝ) + 1) := by
  unfold width
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right (le_height hN) 1

theorem cleared_product_ne {N m k n : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N) :
    denominator N * n ≠ (denominator N + 1) * (m * k) := by
  have hmk : 0 < m * k := by positivity
  have hmkN : m * k ≤ N ^ 2 := by nlinarith [Nat.mul_le_mul hmN hkN]
  have hmkM : m * k < denominator N := by unfold denominator; omega
  intro heq
  by_cases hn : n ≤ m * k
  · have hmul := Nat.mul_le_mul_left (denominator N) hn
    nlinarith
  · have hn' : m * k + 1 ≤ n := by omega
    have hmul := Nat.mul_le_mul_left (denominator N) hn'
    nlinarith

/-- Every reflected product misses every integer logarithmic node. -/
theorem reflected_log_gap {N m k n : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N) (hn : 1 ≤ n) :
    width N ≤ |Real.log n - (center N m + center N k)| := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hM0 : (denominator N : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos N).ne'
  have hM1 : ((denominator N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : 1 ≤ (denominator N + 1) * (m * k) := by
    have : 0 < (denominator N + 1) * (m * k) := by positivity
    omega
  have hpD : (denominator N + 1) * (m * k) ≤ height N := by
    unfold height
    exact Nat.mul_le_mul_left _ (by nlinarith [Nat.mul_le_mul hmN hkN])
  have hq : 1 ≤ denominator N * n := by
    have := denominator_pos N
    nlinarith
  have h := RHTower.log_gap hp hpD hq (cleared_product_ne hm hmN hk hkN)
  have heq : Real.log ((denominator N * n : ℕ) : ℝ) -
      Real.log (((denominator N + 1) * (m * k) : ℕ) : ℝ) =
      Real.log n - (center N m + center N k) := by
    simp only [Nat.cast_mul, Real.log_mul hM0 hn0,
      Real.log_mul hM1 (mul_ne_zero hm0 hk0), Real.log_mul hm0 hk0,
      center, shift]
    ring
  rwa [heq] at h

theorem reflected_sum_gap {N m k n : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N) :
    width N ≤ |Real.log n + (center N m + center N k)| := by
  have h := reflected_log_gap hm hmN hk hkN (show 1 ≤ 1 by omega)
  simp only [Nat.cast_one, Real.log_one, zero_sub, abs_neg] at h
  rw [abs_of_pos (by linarith [center_pos N m, center_pos N k])] at h
  rw [abs_of_pos (by linarith [Real.log_natCast_nonneg n, center_pos N m, center_pos N k])]
  linarith [Real.log_natCast_nonneg n]

theorem log_height_le {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((height N : ℝ) + 1) ≤ 4 * Real.log N + Real.log 6 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpoly : (height N : ℝ) + 1 ≤ 6 * (N : ℝ) ^ 4 := by
    simp only [height, denominator, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one]
    have hs : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 1)]
  calc Real.log ((height N : ℝ) + 1) ≤ Real.log (6 * (N : ℝ) ^ 4) :=
      Real.log_le_log (by positivity) hpoly
    _ = 4 * Real.log N + Real.log 6 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring

end RHTower.EvenSector.Detuned
end
