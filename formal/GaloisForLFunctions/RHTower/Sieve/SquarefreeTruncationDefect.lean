import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicatorZero

/-!
# The defect of truncating the squarefree identity

Truncating `μ²(n) = ∑_{d² ∣ n} μ(d)` at `R` omits the divisors `d > R`, and each omitted term has
modulus at most one, so

`|μ²(n) - ∑_{d ≤ R, d² ∣ n} μ(d)| ≤ #{d ∈ (R, M] : d² ∣ n}`  for `n ≤ M`.

Summing over a window and exchanging the order of summation gives the defect in the form the averaged
tail bound of `Sieve/AveragedSquarefreeTail` consumes.

Note `d² ∣ n` with `n ≥ 1` already forces `d ≤ n`, so the truncated sum is a genuine subsum of the
full one with no side condition relating `R` to `n`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A square divisor is at most its argument. -/
theorem le_of_sq_dvd {d n : ℕ} (hd : 1 ≤ d) (hn : 0 < n) (hdvd : d ^ (2 : ℕ) ∣ n) : d ≤ n := by
  have h1 : d ≤ d ^ (2 : ℕ) := by nlinarith
  exact le_trans h1 (Nat.le_of_dvd hn hdvd)

/-- **The pointwise truncation defect.** -/
theorem abs_moebius_sq_sub_trunc_le {n R M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    |((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        - ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ)|
      ≤ ((((Finset.Icc (R + 1) M).filter (fun d => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) := by
  classical
  set A := (Finset.Icc 1 n).filter (fun d => d ^ (2 : ℕ) ∣ n) with hA
  set B := (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n) with hB
  have hBA : B ⊆ A := by
    intro d hd
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hd
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd.1.1, le_of_sq_dvd hd.1.1 hn hd.2⟩, hd.2⟩
  have hsplit : ∑ d ∈ A, ((moebius d : ℤ) : ℝ)
      = ∑ d ∈ A \ B, ((moebius d : ℤ) : ℝ) + ∑ d ∈ B, ((moebius d : ℤ) : ℝ) :=
    (Finset.sum_sdiff hBA).symm
  rw [moebius_sq_eq_sum_sq_dvd hn, ← hA, hsplit]
  have hsub : A \ B ⊆ (Finset.Icc (R + 1) M).filter (fun d => d ^ (2 : ℕ) ∣ n) := by
    intro d hd
    rw [Finset.mem_sdiff, hA, hB, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_Icc] at hd
    obtain ⟨⟨⟨hd1, hdn⟩, hdvd⟩, hnotB⟩ := hd
    have hdR : R < d := by
      by_contra hc
      exact hnotB ⟨⟨hd1, by omega⟩, hdvd⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, le_trans hdn hnM⟩, hdvd⟩
  have habs : |∑ d ∈ A \ B, ((moebius d : ℤ) : ℝ)| ≤ ((A \ B).card : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ A \ B, |((moebius d : ℤ) : ℝ)| ≤ 1 := by
      intro d _
      rcases moebius_trichotomy d with hm | hm | hm <;> rw [hm] <;> norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((A \ B).card : ℝ)
      ≤ ((((Finset.Icc (R + 1) M).filter (fun d => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc |∑ d ∈ A \ B, ((moebius d : ℤ) : ℝ) + ∑ d ∈ B, ((moebius d : ℤ) : ℝ)
        - ∑ d ∈ B, ((moebius d : ℤ) : ℝ)|
      = |∑ d ∈ A \ B, ((moebius d : ℤ) : ℝ)| := by ring_nf
    _ ≤ ((A \ B).card : ℝ) := habs
    _ ≤ _ := hcard

/-- **The window truncation defect**, in the form the averaged tail bound consumes. -/
theorem abs_window_squarefree_sub_trunc_le (t L R M : ℕ) (hM : t + L ≤ M) :
    |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        - ∑ n ∈ Finset.Ioc t (t + L),
            ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ Finset.Icc (R + 1) M,
          ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ n ∈ Finset.Ioc t (t + L),
      |((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        - ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ)|
        ≤ ((((Finset.Icc (R + 1) M).filter (fun d => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact abs_moebius_sq_sub_trunc_le (by omega) (by omega)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hcount : ∀ n : ℕ,
      ((((Finset.Icc (R + 1) M).filter (fun d => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc (R + 1) M, (if d ^ (2 : ℕ) ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcount2 : ∀ d : ℕ,
      ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ)
        = ∑ n ∈ Finset.Ioc t (t + L), (if d ^ (2 : ℕ) ∣ n then (1 : ℝ) else 0) := by
    intro d
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun n _ => hcount n, Finset.sum_comm,
    Finset.sum_congr rfl fun d _ => (hcount2 d).symm]

/-- **Lower bound for the true squarefree count of a window.**  The truncated main term, its sieve
error, and the truncation defect combine. -/
theorem squarefree_count_ge (t L R M : ℕ) (hR : 1 ≤ R) (hM : t + L ≤ M) :
    (L : ℝ) * squarefreeDensity - ((R : ℝ) + (L : ℝ) / (R : ℝ))
        - ∑ d ∈ Finset.Icc (R + 1) M,
            ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) := by
  have htrunc := abs_truncated_squarefree_sub_le t L R hR
  have hdefect := abs_window_squarefree_sub_trunc_le t L R M hM
  have h1 := (abs_le.mp htrunc).1
  have h2 := (abs_le.mp hdefect).1
  linarith

end RHTower.Sieve
