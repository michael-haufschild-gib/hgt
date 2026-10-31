import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.AMarginNeedsHarmonicCorrelation
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The Wirsing bound for flip twins

For a completely multiplicative `ω` with `|ω| ≤ 1` the logarithmic sum
`L(N) = Σ_{n ≤ N} ω(n)/n` (`gaugeHarmonicSum`) obeys a Levin–Fainleib integral equation. With the
**polar moment** `M(N) = Σ_{n ≤ N} (ω(n)/n) log(N/n)` (`polarMoment`):

* `Σ_{n ≤ N} ω(n) log n / n = L(N) log N − M(N)` (`logMoment_eq`), and
  `M(N + 1) = M(N) + L(N) log((N + 1)/N)` (`polarMoment_succ`);
* the Chebyshev identity `log n = Σ_{d ∣ n} Λ(d)` gives
  `Σ_{n ≤ N} ω(n) log n / n = Σ_{d ≤ N} Λ(d) ω(d)/d · L(N/d)` (`logMoment_eq_vonMangoldt`).

If the primes carry the mean `Σ_{p ≤ N} ω(p) log p/p = β log N + O(1)`, the prime terms average `L`
against `β d log t`, the prime powers cost `O(log N)`, and the equation becomes
`L(N) log N = (1 + β) M(N) + O(log N)` (`exists_abs_wirsing_equation_le`). A discrete Gronwall argument
then gives `|L(N)| ≪ (log N)^{b − 1}` for every `b > 1` with `b ≥ |1 + β|`
(`exists_abs_gaugeHarmonicSum_le_rpow`). For `β < 1/2` this is `L(N)² = o(log N)`.

For the flip of a set of primes of relative logarithmic density `κ`, `β = 1 − 2κ`
(`TheWirsingBoundSeparatesTheDenseFlips`).
-/

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The **polar moment** `M(N) = Σ_{n ≤ N} (ω(n)/n) log(N/n)`. -/
def polarMoment (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ω m / m * Real.log ((N : ℝ) / m)

/-- The **logarithmic moment** `Σ_{n ≤ N} ω(n) log n / n`. -/
def logMoment (ω : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ω m / m * Real.log m

section Identities

variable (ω : ℕ → ℝ)

theorem logMoment_eq (N : ℕ) :
    logMoment ω N = gaugeHarmonicSum ω N * Real.log N - polarMoment ω N := by
  unfold logMoment polarMoment gaugeHarmonicSum
  rw [sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℝ) ≠ 0 := by have := (mem_Icc.mp hm).1; positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have := (mem_Icc.mp hm).1.trans (mem_Icc.mp hm).2; positivity
  rw [Real.log_div hN0 hm0]
  ring

theorem polarMoment_succ {N : ℕ} (hN : 1 ≤ N) :
    polarMoment ω (N + 1) =
      polarMoment ω N + gaugeHarmonicSum ω N * Real.log (((N : ℝ) + 1) / N) := by
  unfold polarMoment gaugeHarmonicSum
  rw [sum_Icc_succ_top (by omega), sum_mul, ← sum_add_distrib]
  have hlast : ω (N + 1) / ((N + 1 : ℕ) : ℝ) * Real.log (((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) = 0 := by
    rw [div_self (by positivity), Real.log_one, mul_zero]
  rw [hlast, add_zero]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by have := (mem_Icc.mp hm).1; exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (((N + 1 : ℕ) : ℝ) / m) = ((N : ℝ) / m) * (((N : ℝ) + 1) / N) by
    push_cast; field_simp,
    Real.log_mul (by positivity) (by positivity)]
  ring

/-- **The Chebyshev identity for the logarithmic moment.** -/
theorem logMoment_eq_vonMangoldt (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b) (N : ℕ) :
    logMoment ω N = ∑ d ∈ Icc 1 N, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d) := by
  set f : ℕ → ℂ := fun m => ((ω m / m : ℝ) : ℂ)
  have hf : ∀ a b : ℕ, f (a * b) = f a * f b := by
    intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [f]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [f]
    simp only [f, hmul a b ha.ne' hb.ne', Nat.cast_mul]
    push_cast
    field_simp
  have h := RHTower.Sieve.sum_mul_log_eq_vonMangoldt hf N
  simp only [f, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h
  unfold logMoment gaugeHarmonicSum
  exact_mod_cast h

/-- `|L(N)| ≤ 1 + log N`. -/
theorem abs_gaugeHarmonicSum_le (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    |gaugeHarmonicSum ω N| ≤ 1 + Real.log N := by
  unfold gaugeHarmonicSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∑ m ∈ Icc 1 N, |ω m / m| ≤ ∑ m ∈ Icc 1 N, ((m : ℝ))⁻¹ := by
    refine sum_le_sum fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by have := (mem_Icc.mp hm).1; exact_mod_cast this
    rw [abs_div, abs_of_pos hm0, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (hbd m)
  refine h.trans ?_
  have hh := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at hh
  exact_mod_cast hh

end Identities

end GaloisForLFunctions.RenormalizedIntersectionTheory
