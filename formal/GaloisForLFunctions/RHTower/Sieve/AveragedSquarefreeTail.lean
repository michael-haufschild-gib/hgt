import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# The truncation tail on average over starting points

For a single start `t` the divisors omitted by the truncation cannot be controlled: a square
divisor `d² ∣ n` with `d` near `√t` costs a full unit.  Averaged over a range of starts the tail is
harmless, because each integer `n` lies in at most `L` of the windows `(t, t+L]`.

Double counting therefore gives, for every fixed modulus,

`∑_{A ≤ t < B} #{n ∈ (t, t+L] : m ∣ n} ≤ L · #{n ∈ (A, B+L] : m ∣ n}`,

and summing over the omitted moduli `d² > R²` turns the omitted mass into

`L · ((B + L - A)/R + M)`,

with `M` the largest relevant `d`.  Taking `R ≍ √L` and `M ≍ √(B+L)` this is the estimate that makes
all but a vanishing proportion of starts carry a positive squarefree density.
-/

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- Every integer lies in at most `L` of the windows `(t, t+L]`. -/
theorem card_start_window_le (n L A B : ℕ) :
    (#{t ∈ Finset.Ico A B | t < n ∧ n ≤ t + L}) ≤ L := by
  classical
  have hsub : {t ∈ Finset.Ico A B | t < n ∧ n ≤ t + L} ⊆ Finset.Ico (n - L) n := by
    intro t ht
    obtain ⟨-, htn, hnt⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_Ico.2 ⟨by omega, htn⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Ico]
  omega

/-- **Double counting over starts.**  The windowed multiple counts average to a single count. -/
theorem sum_card_filter_dvd_le (m A B L : ℕ) :
    ∑ t ∈ Finset.Ico A B, (#{n ∈ Finset.Ioc t (t + L) | m ∣ n})
      ≤ L * (#{n ∈ Finset.Ioc A (B + L) | m ∣ n}) := by
  classical
  have hstep : ∀ t ∈ Finset.Ico A B,
      (#{n ∈ Finset.Ioc t (t + L) | m ∣ n})
        = ∑ n ∈ {n ∈ Finset.Ioc A (B + L) | m ∣ n},
            (if t < n ∧ n ≤ t + L then 1 else 0) := by
    intro t ht
    obtain ⟨hAt, htB⟩ := Finset.mem_Ico.1 ht
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨by omega, by omega⟩, h3⟩, h1, h2⟩
    · rintro ⟨⟨-, h3⟩, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ n ∈ {n ∈ Finset.Ioc A (B + L) | m ∣ n},
      ∑ t ∈ Finset.Ico A B, (if t < n ∧ n ≤ t + L then 1 else 0) ≤ L := by
    intro n _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    exact card_start_window_le n L A B
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The inverse-square sum beyond the truncation level. -/
theorem sum_Icc_inv_sq_le {R : ℕ} (hR : 1 ≤ R) (M : ℕ) :
    ∑ d ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (d : ℝ) ^ (2 : ℕ) ≤ 1 / (R : ℝ) := by
  classical
  have hIcc : Finset.Icc (R + 1) M = Finset.Ico (R + 1) (M + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hcong : ∀ i ∈ Finset.range (M + 1 - (R + 1)),
      (1 : ℝ) / ((R + 1 + i : ℕ) : ℝ) ^ (2 : ℕ) = (1 : ℝ) / ((i : ℝ) + R + 1) ^ (2 : ℕ) := by
    intro i _
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hcong]
  have hbase := sum_range_inv_sq_shift_le R (M + 1 - (R + 1)) hR
  have hpos : (0 : ℝ) < ((M + 1 - (R + 1) : ℕ) : ℝ) + R := by
    have h1 : (0 : ℝ) ≤ ((M + 1 - (R + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have : (0 : ℝ) < 1 / (((M + 1 - (R + 1) : ℕ) : ℝ) + R) := by positivity
  linarith

/-- **Averaged truncation tail.**  Summed over starts, the divisors omitted by a truncation at `R`
contribute at most `L·((B+L-A)/R + M)`. -/
theorem sum_tail_divisor_count_le (A B L R M : ℕ) (hR : 1 ≤ R) (hAB : A ≤ B + L) :
    (∑ t ∈ Finset.Ico A B,
        ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ))
      ≤ (L : ℝ) * (((B : ℝ) + L - A) / (R : ℝ) + (M : ℝ)) := by
  classical
  have hlen : (0 : ℝ) ≤ (B : ℝ) + L - A := by
    have : ((A : ℕ) : ℝ) ≤ ((B + L : ℕ) : ℝ) := by exact_mod_cast hAB
    push_cast at this
    linarith
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hswap : ∑ t ∈ Finset.Ico A B,
      ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M,
          ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) :=
    Finset.sum_comm
  rw [hswap]
  have hper : ∀ d ∈ Finset.Icc (R + 1) M,
      ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ (L : ℝ) * (((B : ℝ) + L - A) / (d : ℝ) ^ (2 : ℕ) + 1) := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.1 hd
    have hdsq : 0 < d ^ (2 : ℕ) := pow_pos (by omega) 2
    have hnat := sum_card_filter_dvd_le (d ^ (2 : ℕ)) A B L
    have hcast : ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ (L : ℝ) * ((#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) := by
      have : ((∑ t ∈ Finset.Ico A B, (#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n}) : ℕ) : ℝ)
          ≤ ((L * (#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n}) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this
      exact this
    have hcount := abs_card_filter_dvd_Ioc_sub_lt (d ^ (2 : ℕ)) A (B + L) hdsq hAB
    have hc1 : (((B + L : ℕ)) : ℝ) - (A : ℝ) = (B : ℝ) + L - A := by push_cast; ring
    have hc2 : (((d ^ (2 : ℕ) : ℕ)) : ℝ) = (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
    rw [hc1, hc2] at hcount
    have hub : ((#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ ((B : ℝ) + L - A) / (d : ℝ) ^ (2 : ℕ) + 1 := by
      have := (abs_lt.1 hcount).2
      linarith
    exact le_trans hcast (mul_le_mul_of_nonneg_left hub hLnn)
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ hLnn
  have hsq : ∑ d ∈ Finset.Icc (R + 1) M, ((B : ℝ) + L - A) / (d : ℝ) ^ (2 : ℕ)
      ≤ ((B : ℝ) + L - A) / (R : ℝ) := by
    have hfac : ∑ d ∈ Finset.Icc (R + 1) M, ((B : ℝ) + L - A) / (d : ℝ) ^ (2 : ℕ)
        = ((B : ℝ) + L - A) * ∑ d ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (d : ℝ) ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hfac]
    calc ((B : ℝ) + L - A) * ∑ d ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (d : ℝ) ^ (2 : ℕ)
        ≤ ((B : ℝ) + L - A) * (1 / (R : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le hR M) hlen
      _ = ((B : ℝ) + L - A) / (R : ℝ) := by ring
  have hcard : ((#(Finset.Icc (R + 1) M) : ℕ) : ℝ) ≤ (M : ℝ) := by
    have : (#(Finset.Icc (R + 1) M)) ≤ M := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast this
  linarith

end RHTower.Sieve
