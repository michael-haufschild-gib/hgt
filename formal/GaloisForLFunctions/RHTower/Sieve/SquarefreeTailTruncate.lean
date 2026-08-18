import GaloisForLFunctions.RHTower.Sieve.SquarefreeTruncationDefect
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# Truncating the squarefree tail at the square root of the window top
-/

namespace RHTower.Sieve

open Finset

/-- **A square larger than the window top divides nothing in the window.** -/
theorem card_filter_dvd_sq_eq_zero {t L d : ℕ} (hd : t + L < d ^ 2) :
    #{n ∈ Finset.Ioc t (t + L) | d ^ 2 ∣ n} = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn hdvd
  rw [Finset.mem_Ioc] at hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le t) hn.1
  have hle : d ^ 2 ≤ n := Nat.le_of_dvd hn0 hdvd
  omega

/-- **The truncation tail is carried by the divisors below the square root of the window top.**
Every `d` above `M'` with `(M'+1)² > t+L` contributes nothing, so the range `[R+1, M]` may be cut
down to `[R+1, M']`. -/
theorem tail_trunc_eq {t L R M M' : ℕ} (hMM : M' ≤ M) (hsq : t + L < (M' + 1) ^ 2) :
    ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ 2 ∣ n} : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M', ((#{n ∈ Finset.Ioc t (t + L) | d ^ 2 ∣ n} : ℕ) : ℝ) := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 hMM⟩
  · intro d hd hnot
    rw [Finset.mem_Icc] at hd
    have hdM : M' < d := by
      by_contra hcon
      exact hnot (Finset.mem_Icc.2 ⟨hd.1, not_lt.mp hcon⟩)
    have hgt : t + L < d ^ 2 := by
      have h1 : (M' + 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    rw [card_filter_dvd_sq_eq_zero hgt]
    norm_num

/-- **The squarefree count of a window, with the tail truncated at the square root.**  For any
window and any `M'` with `(M'+1)² > t+L`, the sieve remainder only involves `d ≤ M'`. -/
theorem squarefree_count_ge_trunc (t L R M M' : ℕ) (hR : 1 ≤ R) (hM : t + L ≤ M)
    (hMM : M' ≤ M) (hsq : t + L < (M' + 1) ^ 2) :
    (L : ℝ) * squarefreeDensity - ((R : ℝ) + (L : ℝ) / (R : ℝ))
        - ∑ d ∈ Finset.Icc (R + 1) M',
            ((#{n ∈ Finset.Ioc t (t + L) | d ^ 2 ∣ n} : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 := by
  have hbase := squarefree_count_ge t L R M hR hM
  rwa [tail_trunc_eq hMM hsq] at hbase

end RHTower.Sieve
