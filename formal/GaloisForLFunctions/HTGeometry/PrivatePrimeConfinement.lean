import Mathlib

/-!
# The private-denominator criterion for bounded-relation confinement

A rational sequence `b` has **eventual private-prime exposure** when there are primes
`pₙ → ∞` such that `pₙ` divides the reduced denominator of `bₙ` and of no other `bₘ`
— equivalently `padicNorm (pₙ) (bₙ) > 1` while `padicNorm (pₙ) (bₘ) ≤ 1` for `m ≠ n`.

The criterion (`private_prime_bounded_relation_confinement`) is that such a sequence has
**bounded-relation confinement**: for every height bound `D` there is an index `M` beyond
which no coefficient of any height-`≤ D` integer relation `∑ dₘ bₘ = 0` is nonzero.  The
mechanism is the ultrametric: if `pₙ` exceeds `D` and `dₙ ≠ 0`, then `pₙ ∤ dₙ`, so the `pₙ`-adic
norm of the term `dₙ bₙ` strictly dominates every other term, forcing the sum nonzero
(`sum_ne_zero_of_private_prime`).  Since `pₙ → ∞`, only a finite prefix survives.
-/

open Finset

namespace GaloisForLFunctions

/-- **Private-prime domination.**  If a prime `q` divides the reduced denominator of `b n`
but not of any other `b m` in the support, and `q ∤ d n` with `d n ≠ 0`, then the `q`-adic
norm of the `n`-th term strictly dominates, so the whole integer combination is nonzero. -/
theorem sum_ne_zero_of_private_prime {q : ℕ} (hq : q.Prime) {b : ℕ → ℚ} {d : ℕ →₀ ℤ}
    {n : ℕ} (hn : n ∈ d.support) (hqd : ¬ (q : ℤ) ∣ d n)
    (hbn : 1 < padicNorm q (b n))
    (hbm : ∀ m ∈ d.support, m ≠ n → padicNorm q (b m) ≤ 1) :
    ∑ m ∈ d.support, (d m : ℚ) * b m ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  classical
  have hdn1 : padicNorm q (d n : ℚ) = 1 :=
    le_antisymm (padicNorm.of_int _)
      (not_lt.mp (fun h => hqd ((padicNorm.int_lt_one_iff (d n)).mp h)))
  have hFn : 1 < padicNorm q ((d n : ℚ) * b n) := by
    rw [padicNorm.mul, hdn1, one_mul]; exact hbn
  have hR : padicNorm q (∑ m ∈ d.support.erase n, (d m : ℚ) * b m) ≤ 1 := by
    rcases (d.support.erase n).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, padicNorm.zero]; exact zero_le_one
    · refine padicNorm.sum_le hne fun m hm => ?_
      rw [Finset.mem_erase] at hm
      rw [padicNorm.mul]
      calc padicNorm q (d m : ℚ) * padicNorm q (b m)
          ≤ 1 * 1 := mul_le_mul (padicNorm.of_int _) (hbm m hm.2 hm.1)
            (padicNorm.nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hne_norm : padicNorm q ((d n : ℚ) * b n)
      ≠ padicNorm q (∑ m ∈ d.support.erase n, (d m : ℚ) * b m) := by
    intro heq; rw [heq] at hFn; linarith
  have hsplit : (∑ m ∈ d.support, (d m : ℚ) * b m)
      = (d n : ℚ) * b n + ∑ m ∈ d.support.erase n, (d m : ℚ) * b m :=
    (Finset.add_sum_erase _ (fun m => (d m : ℚ) * b m) hn).symm
  have hSnorm : padicNorm q (∑ m ∈ d.support, (d m : ℚ) * b m)
      = padicNorm q ((d n : ℚ) * b n) := by
    rw [hsplit, padicNorm.add_eq_max_of_ne hne_norm, max_eq_left (by linarith)]
  intro hzero
  rw [hzero, padicNorm.zero] at hSnorm
  linarith

/-- **The private-denominator criterion.**  A rational sequence with eventual private-prime
exposure (`pₙ → ∞` a prime dividing the reduced denominator of `bₙ` alone) has bounded-relation
confinement: for every height `D` there is a threshold `M` past which every height-`≤ D`
integer relation `∑ dₘ bₘ = 0` has all its support below `M`. -/
theorem private_prime_bounded_relation_confinement {b : ℕ → ℚ} {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime)
    (hpinf : Filter.Tendsto p Filter.atTop Filter.atTop)
    (hbn : ∀ n, 1 < padicNorm (p n) (b n))
    (hbm : ∀ n m, m ≠ n → padicNorm (p n) (b m) ≤ 1)
    (D : ℕ) :
    ∃ M : ℕ, ∀ d : ℕ →₀ ℤ, (∀ n, |d n| ≤ (D : ℤ)) →
      (∑ m ∈ d.support, (d m : ℚ) * b m = 0) → ∀ n ∈ d.support, n < M := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hpinf.eventually_gt_atTop D)
  refine ⟨M, fun d hd hrel n hn => ?_⟩
  by_contra hnM
  push Not at hnM
  have hDp : D < p n := hM n hnM
  have hdn0 : d n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hqd : ¬ (p n : ℤ) ∣ d n := by
    intro hdvd
    have h1 : (p n : ℤ) ≤ |d n| := Int.le_of_dvd (abs_pos.mpr hdn0) ((dvd_abs _ _).mpr hdvd)
    have h2 : |d n| ≤ (D : ℤ) := hd n
    have h3 : (D : ℤ) < (p n : ℤ) := by exact_mod_cast hDp
    linarith
  exact sum_ne_zero_of_private_prime (hp n) hn hqd (hbn n)
    (fun m _ hmn => hbm n m hmn) hrel

end GaloisForLFunctions
