import GaloisForLFunctions.HTGeometry.SmoothWeight
import Mathlib.Algebra.Order.Chebyshev

/-!
# The smoothing error without a boundedness hypothesis

Replacing the sharp cutoff `n ≤ K` by the smooth weight changes a sum only inside the transition window
`(K, K+H)`, where the weight lies in `[0,1]`; above `K+H` the weight vanishes and the sharp sum omits the
term as well.  So the difference is at most the `ℓ¹` mass of the coefficients in the window:

`‖∑_{n < m} a(n) w(n) − ∑_{n ≤ K} a(n)‖ ≤ ∑_{K < n ≤ ⌊K+H⌋} ‖a(n)‖`   whenever `K + H ≤ m`.

The corpus's `norm_weighted_sub_partialSum_le` is the case of unit-bounded coefficients, where the window
mass is at most `H + 1`.  The general form is what a convolution needs: the coefficients of a threefold
Dirichlet convolution are not bounded, and the window mass has to be estimated arithmetically instead.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Finset

/-- **The smoothing error, with no boundedness hypothesis.**  Replacing the sharp cutoff `n ≤ K` by the
smooth one changes the sum only inside the transition window `(K, K+H)`, so the difference is at most the
`ℓ¹` mass of the coefficients there. -/
theorem norm_weighted_sub_partialSum_le_window {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (K m : ℕ)
    (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), a n‖
      ≤ ∑ n ∈ Finset.Ioc K ⌊(K : ℝ) + H⌋₊, ‖a n‖ := by
  classical
  have hKm : K + 1 ≤ m := by
    have hlt : (K : ℝ) < (m : ℝ) := by linarith
    have : K < m := by exact_mod_cast hlt
    omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n : ℕ => a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)) hKm
  have hone : (∑ n ∈ Finset.range (K + 1), a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      = ∑ n ∈ Finset.range (K + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hnK : (n : ℝ) ≤ (K : ℝ) := by
      have : n ≤ K := by omega
      exact_mod_cast this
    rw [smoothWeight_eq_one hH hnK]
    simp
  have hdiff : (∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      - (∑ n ∈ Finset.range (K + 1), a n)
      = ∑ n ∈ Finset.Ico (K + 1) m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hsplit, hone]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ico (K + 1) m,
      ‖a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        ≤ (if n ≤ ⌊(K : ℝ) + H⌋₊ then ‖a n‖ else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothWeight_nonneg _ _ _)]
    by_cases hle : n ≤ ⌊(K : ℝ) + H⌋₊
    · rw [if_pos hle]
      calc ‖a n‖ * smoothWeight (K : ℝ) H (n : ℝ) ≤ ‖a n‖ * 1 :=
            mul_le_mul_of_nonneg_left (smoothWeight_le_one _ _ _) (norm_nonneg _)
        _ = ‖a n‖ := mul_one _
    · rw [if_neg hle]
      have hge : (K : ℝ) + H ≤ (n : ℝ) := by
        rw [not_le] at hle
        have h1 : ⌊(K : ℝ) + H⌋₊ + 1 ≤ n := by omega
        have h2 : (K : ℝ) + H < (⌊(K : ℝ) + H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h3 : ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
        linarith
      rw [smoothWeight_eq_zero hH hge, mul_zero]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => norm_nonneg _)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ico] at hn
  rw [Finset.mem_Ioc]
  exact ⟨by omega, hn.2⟩


/-- Cauchy–Schwarz for a finite `ℓ¹` mass against the `ℓ²` mass. -/
theorem sum_norm_le_sqrt_card_mul_sqrt_sum_normSq (s : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ s, ‖a n‖) ≤ Real.sqrt (s.card) * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) := by
  have hcs : (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) ≤ (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) :=
    sq_sum_le_card_mul_sum_sq
  have hnn : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ := Finset.sum_nonneg fun n _ => norm_nonneg _
  have hsq : (∑ n ∈ s, ‖a n‖) = Real.sqrt ((∑ n ∈ s, ‖a n‖) ^ (2 : ℕ)) := (Real.sqrt_sq hnn).symm
  rw [hsq, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt hcs

/-- **The smoothing error against the window's `ℓ²` mass.**  Cauchy–Schwarz turns the window's `ℓ¹`
mass into `√H` times its `ℓ²` mass, so a mean-square bound for the coefficients suffices: no
short-interval mean value theorem for the coefficients themselves is needed. -/
theorem norm_weighted_sub_partialSum_le_sqrt {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (K m : ℕ)
    (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), a n‖
      ≤ Real.sqrt H
          * Real.sqrt (∑ n ∈ Finset.Ioc K ⌊(K : ℝ) + H⌋₊, ‖a n‖ ^ (2 : ℕ)) := by
  refine le_trans (norm_weighted_sub_partialSum_le_window hH K m hm) ?_
  refine le_trans (sum_norm_le_sqrt_card_mul_sqrt_sum_normSq _ a) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine Real.sqrt_le_sqrt ?_
  rw [Nat.card_Ioc]
  have hfl : ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) ≤ (K : ℝ) + H :=
    Nat.floor_le (by positivity)
  have hKle : K ≤ ⌊(K : ℝ) + H⌋₊ := by
    refine Nat.le_floor ?_
    linarith
  have hcast : ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) = ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) - (K : ℝ) := by
    rw [Nat.cast_sub hKle]
  rw [hcast]
  linarith

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Finset

/-- The smooth cutoff vanishes past `N + H`, so its weighted series is a finite sum. -/
theorem tsum_mul_smoothWeight_eq_sum_range_real {a : ℕ → ℂ} {N H : ℝ} (hH : 0 < H) (m : ℕ)
    (hm : N + H ≤ (m : ℝ)) :
    ∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range m, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  have hnm : m ≤ n := by
    by_contra hlt
    exact hn (Finset.mem_range.2 (by omega))
  have hnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
  rw [smoothWeight_eq_zero hH (by linarith)]
  simp

/-- **The smoothing error at a real cutoff.**  Replacing the sharp cutoff `n ≤ N` by the smooth one
changes the sum only inside the transition window `(⌊N⌋, ⌊N+H⌋]`. -/
theorem norm_weighted_sub_partialSum_le_window_real {a : ℕ → ℂ} {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H)
    (m : ℕ) (hm : N + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n‖
      ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊N + H⌋₊, ‖a n‖ := by
  classical
  have hfl : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le hN
  have hKm : ⌊N⌋₊ + 1 ≤ m := by
    have hlt : ((⌊N⌋₊ : ℕ) : ℝ) < (m : ℝ) := by linarith
    have : ⌊N⌋₊ < m := by exact_mod_cast hlt
    omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n : ℕ => a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) hKm
  have hone : (∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hnK : (n : ℝ) ≤ N := by
      have hle : n ≤ ⌊N⌋₊ := by omega
      have : (n : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    rw [smoothWeight_eq_one hH hnK]
    simp
  have hdiff : (∑ n ∈ Finset.range m, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      - (∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n)
      = ∑ n ∈ Finset.Ico (⌊N⌋₊ + 1) m, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hsplit, hone]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ico (⌊N⌋₊ + 1) m,
      ‖a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        ≤ (if n ≤ ⌊N + H⌋₊ then ‖a n‖ else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothWeight_nonneg _ _ _)]
    by_cases hle : n ≤ ⌊N + H⌋₊
    · rw [if_pos hle]
      calc ‖a n‖ * smoothWeight N H (n : ℝ) ≤ ‖a n‖ * 1 :=
            mul_le_mul_of_nonneg_left (smoothWeight_le_one _ _ _) (norm_nonneg _)
        _ = ‖a n‖ := mul_one _
    · rw [if_neg hle]
      have hge : N + H ≤ (n : ℝ) := by
        rw [not_le] at hle
        have h1 : ⌊N + H⌋₊ + 1 ≤ n := by omega
        have h2 : N + H < (⌊N + H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h3 : ((⌊N + H⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
        linarith
      rw [smoothWeight_eq_zero hH hge, mul_zero]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => norm_nonneg _)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ico] at hn
  rw [Finset.mem_Ioc]
  exact ⟨by omega, hn.2⟩

/-- The transition window at a real cutoff holds at most `H + 1` integers. -/
theorem card_window_real_le {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    ((⌊N + H⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) ≤ H + 1 := by
  rcases le_or_gt ⌊N⌋₊ ⌊N + H⌋₊ with h | h
  · rw [Nat.cast_sub h]
    have h1 : ((⌊N + H⌋₊ : ℕ) : ℝ) ≤ N + H := Nat.floor_le (by linarith)
    have h2 : N < ((⌊N⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one N
    linarith
  · rw [Nat.sub_eq_zero_of_le h.le]
    have : (0 : ℝ) ≤ H := hH.le
    simpa using by linarith

/-- **The smoothed series against the sharp partial sum, at a real cutoff.**  The two differ only on the
transition window, so any uniform bound `C` on the coefficients there bounds the difference by the window
length times `C`. -/
theorem norm_tsum_mul_smoothWeight_sub_partialSum_le_window {a : ℕ → ℂ} {N H C : ℝ}
    (hN : 0 ≤ N) (hH : 0 < H)
    (hC : ∀ n : ℕ, ⌊N⌋₊ < n → n ≤ ⌊N + H⌋₊ → ‖a n‖ ≤ C) :
    ‖(∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n‖
      ≤ ((⌊N + H⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) * C := by
  classical
  have hm : N + H ≤ ((⌊N + H⌋₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (N + H)
    push_cast
    linarith
  rw [tsum_mul_smoothWeight_eq_sum_range_real hH (⌊N + H⌋₊ + 1) hm]
  refine le_trans (norm_weighted_sub_partialSum_le_window_real hN hH (⌊N + H⌋₊ + 1) hm) ?_
  have hterm : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊N + H⌋₊, ‖a n‖ ≤ C := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact hC n hn.1 hn.2
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

/-- The width form: the smoothing costs at most `(H+1)·C`. -/
theorem norm_tsum_mul_smoothWeight_sub_partialSum_le_width {a : ℕ → ℂ} {N H C : ℝ}
    (hN : 0 ≤ N) (hH : 0 < H) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, ⌊N⌋₊ < n → n ≤ ⌊N + H⌋₊ → ‖a n‖ ≤ C) :
    ‖(∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n‖
      ≤ (H + 1) * C :=
  le_trans (norm_tsum_mul_smoothWeight_sub_partialSum_le_window hN hH hC)
    (mul_le_mul_of_nonneg_right (card_window_real_le hN hH) hC0)

end GaloisForLFunctions.HTGeometry
end
