import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The averaged truncation tail without the per-divisor defect

Counting the multiples of `m` in an interval anchored at the origin is exact: there are `⌊N/m⌋` of
them, with no `+1`.  Averaging the windowed counts over their starts turns every window count into
one anchored count, so the truncated tail is bounded by `L(B+L)/R` alone — the term linear in the
truncation level `M`, which the unanchored estimate pays once per divisor, disappears.
-/

namespace RHTower.Sieve

open Finset

/-- **The anchored multiple count carries no defect.** -/
theorem card_filter_dvd_Ioc_zero_le (m N : ℕ) :
    ((#{n ∈ Finset.Ioc 0 N | m ∣ n} : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

/-- **Averaged truncation tail, sharp form.**  Summed over starts, the divisors omitted by a
truncation at `R` contribute at most `L(B+L)/R`, with no dependence on the truncation level `M`. -/
theorem sum_tail_divisor_count_le_sharp (A B L R M : ℕ) (hR : 1 ≤ R) :
    (∑ t ∈ Finset.Ico A B,
        ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ))
      ≤ (L : ℝ) * (((B : ℝ) + L) / (R : ℝ)) := by
  classical
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hBL : (0 : ℝ) ≤ (B : ℝ) + L := by positivity
  have hswap : ∑ t ∈ Finset.Ico A B,
      ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M,
          ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) :=
    Finset.sum_comm
  rw [hswap]
  have hper : ∀ d ∈ Finset.Icc (R + 1) M,
      ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ (L : ℝ) * (((B : ℝ) + L) / (d : ℝ) ^ (2 : ℕ)) := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.1 hd
    have hnat := sum_card_filter_dvd_le (d ^ (2 : ℕ)) A B L
    have hcast : ∑ t ∈ Finset.Ico A B, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ (L : ℝ) * ((#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) := by
      have : ((∑ t ∈ Finset.Ico A B, (#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n}) : ℕ) : ℝ)
          ≤ ((L * (#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n}) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this
      exact this
    have hsub : (#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n})
        ≤ (#{n ∈ Finset.Ioc 0 (B + L) | d ^ (2 : ℕ) ∣ n}) :=
      Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.Ioc_subset_Ioc_left (Nat.zero_le A)))
    have hsubR : ((#{n ∈ Finset.Ioc A (B + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
        ≤ ((#{n ∈ Finset.Ioc 0 (B + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) := by exact_mod_cast hsub
    have hanch := card_filter_dvd_Ioc_zero_le (d ^ (2 : ℕ)) (B + L)
    have hnum : (((B + L : ℕ)) : ℝ) = (B : ℝ) + L := by push_cast; ring
    have hden : (((d ^ (2 : ℕ) : ℕ)) : ℝ) = (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
    rw [hnum, hden] at hanch
    exact le_trans hcast (mul_le_mul_of_nonneg_left (le_trans hsubR hanch) hLnn)
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hLnn
  have hfac : ∑ d ∈ Finset.Icc (R + 1) M, ((B : ℝ) + L) / (d : ℝ) ^ (2 : ℕ)
      = ((B : ℝ) + L) * ∑ d ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (d : ℝ) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hfac]
  calc ((B : ℝ) + L) * ∑ d ∈ Finset.Icc (R + 1) M, (1 : ℝ) / (d : ℝ) ^ (2 : ℕ)
      ≤ ((B : ℝ) + L) * (1 / (R : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le hR M) hBL
    _ = ((B : ℝ) + L) / (R : ℝ) := by ring

end RHTower.Sieve
