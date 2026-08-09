import GaloisForLFunctions.RHTower.MoebiusApproximantResidual

/-!
# The residual off the range, and the truncated Möbius divisor sum

`MoebiusApproximantResidual` computed the residual of the Möbius approximant on `[1,N]`, where the corpus's
`moebius_floor_summatory` evaluates the floor sum to `1`.  Off that range the floor sum is a genuine
arithmetic object, and this file identifies it.

Dropping the evaluation step from the previous proof gives the identity for *every* `n`:

`∑_{d ≤ N} μ(d)·g_d(n) = n·M₁(N) − F_N(n)`,  `F_N(n) = ∑_{d ≤ N} μ(d)⌊n/d⌋`,

so the residual of the coefficients `−μ(d)` is `1 − F_N(n) + n·M₁(N)` at every `n ≥ 1`
(`moebius_residual_eq_general`).  Counting the multiples of `d` in `[1,n]` and swapping the order of
summation expresses `F_N` as a partial sum of the **truncated Möbius divisor sum**

`truncMoebiusDivisorSum N k = ∑_{d ∣ k, d ≤ N} μ(d)`,

namely `F_N(n) = ∑_{k ≤ n} truncMoebiusDivisorSum N k` (`sum_moebius_floor_eq_sum_trunc`).  For `k ≤ N` the
truncation is inactive and the sum is `[k = 1]` (`truncMoebiusDivisorSum_of_le`), which recovers
`F_N(n) = 1` for `n ≤ N` and hence the previous card's residual.

So the whole convergence question for a Möbius-type approximant is: how large is
`∑_{k ≤ n} truncMoebiusDivisorSum N k` for `n > N`?  That is the Selberg-sieve truncation object, and naming
it is as far as this file goes — the crude bound `|truncMoebiusDivisorSum N k| ≤ d(k)` is far too weak to be
useful, and no estimate is attempted here.
-/

open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- **The truncated Möbius divisor sum** `∑_{d ∣ k, d ≤ N} μ(d)`. -/
def truncMoebiusDivisorSum (N k : ℕ) : ℝ :=
  ∑ d ∈ Finset.filter (fun d => d ∣ k) (Finset.Icc 1 N), ((moebius d : ℤ) : ℝ)

/-- Below the truncation the sum is the Möbius divisor sum, hence `[k = 1]`. -/
theorem truncMoebiusDivisorSum_of_le {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    truncMoebiusDivisorSum N k = if k = 1 then 1 else 0 := by
  classical
  have hsub : Finset.filter (fun d => d ∣ k) (Finset.Icc 1 N) = k.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun ⟨⟨hd1, _⟩, hdvd⟩ => ⟨hdvd, by omega⟩
    · refine fun ⟨hdvd, hk0⟩ => ⟨⟨?_, ?_⟩, hdvd⟩
      · exact Nat.one_le_iff_ne_zero.mpr (by
          intro h
          rw [h] at hdvd
          exact hk0 (Nat.eq_zero_of_zero_dvd hdvd))
      · exact le_trans (Nat.le_of_dvd (by omega) hdvd) hkN
  rw [truncMoebiusDivisorSum, hsub, ← Int.cast_sum, sum_moebius_divisors k]
  by_cases h : k = 1 <;> simp [h]

/-- Counting multiples: the floor sum is a partial sum of truncated Möbius divisor sums. -/
theorem sum_moebius_floor_eq_sum_trunc (n N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 n, truncMoebiusDivisorSum N k := by
  classical
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcount : ∀ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ)
        = ∑ k ∈ Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n), ((moebius d : ℤ) : ℝ) := by
    intro d _
    rw [Finset.sum_const, hIcc, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hcount]
  simp only [truncMoebiusDivisorSum]
  refine Finset.sum_comm' ?_
  intro d k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- **The residual identity, at every point.** -/
theorem moebius_residual_eq_general (n N : ℕ) :
    1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = 1 - (∑ k ∈ Finset.Icc 1 n, truncMoebiusDivisorSum N k)
        + (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) := by
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ))
        = (n : ℝ) * (((moebius d : ℤ) : ℝ) / (d : ℝ))
          - ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [modSeq_eq_sub_floor hd1]
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    field_simp
  have hneg : ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = -∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hneg, Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_moebius_floor_eq_sum_trunc n N]
  ring

/-- The previous card's residual, recovered: below the truncation the partial sum is `1`. -/
theorem sum_trunc_eq_one_of_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, truncMoebiusDivisorSum N k = 1 := by
  have hterm : ∀ k ∈ Finset.Icc 1 n, truncMoebiusDivisorSum N k = if k = 1 then 1 else 0 := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact truncMoebiusDivisorSum_of_le hk1 (le_trans hkn hnN)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun _ => (1 : ℝ))]
  rw [if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)]

end RHTower

end
