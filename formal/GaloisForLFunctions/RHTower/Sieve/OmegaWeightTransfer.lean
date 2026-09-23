import GaloisForLFunctions.RHTower.Sieve.WeightRemovalFibre
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# Transferring the fibre mean square to the `ω_P`-weighted one

Combining the abstract weight-removal inequality with Turán--Kubilius for a range of primes gives
the step the short-interval argument opens with: the fibre mean square of a unit-bounded weight is
controlled by the fibre mean square of the *same weight multiplied by the designated prime count*,
divided by the square of the harmonic mass of the designated range, plus an explicit variance cost.

The variance cost is what forces the harmonic mass `mertensS z − mertensS z₀` to grow: it is the
`1/W(P)` loss of the classical arrangement of the argument.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The dyadic block carrying every fibre, written as a half-open interval. -/
theorem fibreDyadicIndex_eq_Ioc {x h : ℝ} (hx : 4 ≤ x) :
    fibreDyadicIndex x h = Finset.Ioc (⌈Real.sqrt x / 2⌉₊ - 1) ⌊Real.sqrt x + h⌋₊ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have h1 : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  rw [fibreDyadicIndex]
  ext b
  rw [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **The variance of the designated prime count over the fibre block.** -/
theorem sum_variance_fibreDyadicIndex_le {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) {z₀ z : ℕ}
    (hz : z₀ ≤ z) :
    (∑ b ∈ fibreDyadicIndex x h,
        (((primeFactorsIn (primesRange z₀ z) b).card : ℝ) - (mertensS z - mertensS z₀)) ^ (2 : ℕ))
      ≤ 4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
        + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  set a₀ : ℕ := ⌈Real.sqrt x / 2⌉₊ - 1 with ha₀
  set b₀ : ℕ := ⌊Real.sqrt x + h⌋₊ with hb₀
  have hceil1 : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  have hab : a₀ ≤ b₀ := by
    have hcf : ⌈Real.sqrt x / 2⌉₊ ≤ ⌊Real.sqrt x / 2⌋₊ + 1 := Nat.ceil_le_floor_add_one _
    have hmono : ⌊Real.sqrt x / 2⌋₊ ≤ ⌊Real.sqrt x + h⌋₊ :=
      Nat.floor_le_floor (by linarith)
    omega
  rw [fibreDyadicIndex_eq_Ioc hx, ← ha₀, ← hb₀]
  refine (sum_variance_primesRange_le hz a₀ b₀ hab).trans ?_
  have hb0R : ((b₀ : ℕ) : ℝ) ≤ Real.sqrt x + h := Nat.floor_le (by positivity)
  have ha0R : Real.sqrt x / 2 - 1 ≤ ((a₀ : ℕ) : ℝ) := by
    have hcast : ((a₀ : ℕ) : ℝ) = ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) - 1 := by
      rw [ha₀, Nat.cast_sub hceil1]
      push_cast
      ring
    have hce : Real.sqrt x / 2 ≤ ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [hcast]
    linarith
  have hmert0 : 0 ≤ mertensS z := by
    rw [mertensS]
    refine Finset.sum_nonneg fun p hp => ?_
    have hp0 : 0 < p := by
      rw [mem_primesLE] at hp
      exact hp.2.pos
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    positivity
  have hlen : ((b₀ : ℕ) : ℝ) - ((a₀ : ℕ) : ℝ) ≤ Real.sqrt x / 2 + h + 1 := by linarith
  nlinarith [hlen, hmert0]

/-- **The Turán--Kubilius transfer.**  The fibre mean square of a unit-bounded weight is at most
twice that of its designated-prime-count multiple, plus the variance of that count over the block. -/
theorem sum_sq_fibreSum_le_omegaWeighted {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 4 ≤ x) (hh0 : 0 ≤ h) {z₀ z : ℕ} (hz : z₀ ≤ z) :
    (mertensS z - mertensS z₀) ^ (2 : ℕ)
        * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)
      ≤ 2 * ∑ a ∈ outerBlock x h,
            (∑ b ∈ innerFibre x h a,
              f b * ((primeFactorsIn (primesRange z₀ z) b).card : ℝ)) ^ (2 : ℕ)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  classical
  have hbase := sum_sq_fibreSum_le_weighted (f := f)
    (g := fun b => ((primeFactorsIn (primesRange z₀ z) b).card : ℝ)) hf hx hh0
    (mertensS z - mertensS z₀)
  have hvar := sum_variance_fibreDyadicIndex_le hx hh0 hz
  have hfac : (0 : ℝ) ≤ 2 * (h + 1) * (2 * h + 1) := by nlinarith [hh0]
  linarith [hbase, mul_le_mul_of_nonneg_left hvar hfac]

end

end RHTower.Sieve
