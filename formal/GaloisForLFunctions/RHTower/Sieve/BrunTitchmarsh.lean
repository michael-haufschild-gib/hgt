import GaloisForLFunctions.RHTower.Sieve.IntervalSelberg
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Brun–Titchmarsh shape from the Selberg sieve

Chaining the three lower bounds

`S_Y ≥ ∑_{l ≤ Y sqfree} 1/l ≥ ½ ∑_{n ≤ Y} 1/n ≥ ½ log Y`

turns the Selberg main term `(b-a)/S_Y` into `2(b-a)/log Y`.  Since the `Λ²` coefficients vanish
above `Y²` and are bounded by one, the level of the sieve is `Y²`, which may be taken as large as
the interval allows — so `log Y ≍ log(b-a)` with no `log log` penalty.

This is the Brun–Titchmarsh shape: the number of integers of an interval free of prime factors
below `z` is `≪ (b-a)/log Y` plus a divisor-counting error confined to `d ≤ Y²`.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- The harmonic sum dominates the logarithm. -/
theorem log_le_sum_inv (Y : ℕ) : Real.log Y ≤ ∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / n := by
  have hmono : Real.log Y ≤ Real.log ((Y : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · simp
    · have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY
      exact Real.log_le_log hYpos (by linarith)
  have hharm := log_add_one_le_harmonic Y
  have hcast : ((harmonic Y : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / n := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun n _ => by rw [one_div]
  have hpush : Real.log ((Y : ℝ) + 1) ≤ ((harmonic Y : ℚ) : ℝ) := by
    have : ((Y + 1 : ℕ) : ℝ) = (Y : ℝ) + 1 := by push_cast; ring
    rwa [this] at hharm
  rw [← hcast]
  linarith

/-- **Selberg mass lower bound in logarithmic form.** -/
theorem half_log_le_selbergMassLE (a b z Y : ℕ) (hYz : Y ≤ z) :
    Real.log Y / 2 ≤ selbergMassLE (intervalSieve a b z) Y := by
  have h1 := sum_inv_squarefree_le_selbergMassLE a b z Y hYz
  have h2 := sum_inv_le_two_mul_sum_inv_squarefree Y
  have h3 := log_le_sum_inv Y
  have hcong : ∑ l ∈ {l ∈ Finset.Icc 1 Y | Squarefree l}, (l : ℝ)⁻¹
      = ∑ l ∈ {l ∈ Finset.Icc 1 Y | Squarefree l}, (1 : ℝ) / l :=
    Finset.sum_congr rfl fun l _ => by rw [one_div]
  rw [hcong] at h1
  linarith

/-- **Brun–Titchmarsh shape.**  The rough-integer count of an interval has main term
`2(b-a)/log Y`, with the error carried by divisors up to `Y²`. -/
theorem card_coprime_Ioc_le_log (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hlog : 0 < Real.log Y) :
    ((#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y
        + ∑ d ∈ (primorial z).divisors,
            |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| := by
  have hbase := card_coprime_Ioc_le_selberg a b z hab hY
  have hmass := half_log_le_selbergMassLE a b z Y hYz
  have hSpos : 0 < selbergMassLE (intervalSieve a b z) Y := selbergMassLE_pos _ hY
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hmain : ((b : ℝ) - a) / selbergMassLE (intervalSieve a b z) Y
      ≤ 2 * ((b : ℝ) - a) / Real.log Y := by
    rw [div_le_div_iff₀ hSpos hlog]
    nlinarith [hmass, hlen, hlog, hSpos]
  linarith

end RHTower.Sieve
