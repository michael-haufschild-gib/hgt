import GaloisForLFunctions.RHTower.Sieve.MoebiusSignCount

/-!
# The squarefree indicator as a divisor sum, at squarefree arguments

On a squarefree `n` the only `d` with `d² ∣ n` is `d = 1`, so

`∑_{d² ∣ n} μ(d) = μ(1) = 1 = μ²(n)`.

This is the squarefree half of the identity `μ²(n) = ∑_{d² ∣ n} μ(d)`.  The complementary half — that
the sum vanishes at non-squarefree `n` — requires identifying `{d : d² ∣ n}` with the divisors of the
square part of `n`, and is not proved here.

Note that the corpus's short-interval squarefree count works throughout with the *truncated* sum
`∑_{d ≤ R, d² ∣ n} μ(d)` and never with the predicate `Squarefree`; this module is the first link
between the two.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- At a squarefree argument only `d = 1` has `d² ∣ n`. -/
theorem filter_sq_dvd_eq_singleton {n : ℕ} (hn : 0 < n) (hsf : Squarefree n) :
    (Finset.Icc 1 n).filter (fun d => d ^ (2 : ℕ) ∣ n) = {1} := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, _⟩, hdvd⟩
    have hmul : d * d ∣ n := by rwa [← pow_two]
    exact Nat.isUnit_iff.mp (hsf d hmul)
  · rintro rfl
    exact ⟨⟨le_refl 1, hn⟩, by simp⟩

/-- **The divisor sum is `1` at a squarefree argument.** -/
theorem sum_moebius_sq_dvd_of_squarefree {n : ℕ} (hn : 0 < n) (hsf : Squarefree n) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ) = 1 := by
  rw [filter_sq_dvd_eq_singleton hn hsf, Finset.sum_singleton]
  simp

/-- **`μ²` is the squarefree indicator.** -/
theorem moebius_sq_eq_indicator (n : ℕ) :
    ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) = if Squarefree n then 1 else 0 := by
  classical
  by_cases hsf : Squarefree n
  · rw [if_pos hsf]
    have hne : moebius n ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;> rw [hm] <;> norm_num
  · rw [if_neg hsf]
    have hz : moebius n = 0 := by
      by_contra hne
      exact hsf (moebius_ne_zero_iff_squarefree.mp hne)
    rw [hz]
    norm_num

/-- The squarefree count of a window is the sum of `μ²`. -/
theorem sum_moebius_sq_eq_card (t L : ℕ) :
    ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
      = (((Finset.Ioc t (t + L)).filter (fun n => Squarefree n)).card : ℝ) := by
  classical
  rw [Finset.sum_congr rfl fun n _ => moebius_sq_eq_indicator n, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

end RHTower.Sieve
