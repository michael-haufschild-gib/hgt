import GaloisForLFunctions.RHTower.PrimeSmallDeviationArithmetic

/-!
# A square-root tail from a logarithmic mass envelope

Finite partial summation retains the unused envelope mass at the last
cutoff. No pointwise decay or uniform square-root mass bound is needed.
-/

noncomputable section
open Finset

namespace RHTower.WeilSingularArithmetic
open PrimeSmallDeviation

private theorem log_nat_step_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log n - Real.log (n - 1 : ℕ) ≤ 2 / n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hp : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ n by omega))
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hp0)
  rw [Real.log_div hn0.ne' hp0.ne'] at h
  have he : (n : ℝ) / (n - 1 : ℕ) - 1 = 1 / (n - 1 : ℕ) := by
    rw [hp]
    have hp' : (n : ℝ) - 1 ≠ 0 := by rw [← hp]; exact hp0.ne'
    field_simp [hp']
    ring
  rw [he] at h
  apply h.trans
  apply (div_le_div_iff₀ hp0 hn0).mpr
  rw [hp]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- A logarithmic cumulative bound controls every square-root weighted tail. -/
theorem sum_Ioc_div_sqrt_le_of_log_envelope {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {A η : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hb : ∀ k : ℕ, 1 ≤ k → (∑ n ∈ range (k + 1), a n) ≤ A + η * Real.log k)
    {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    (∑ n ∈ Ioc N M, a n / Real.sqrt n) ≤
      (A + η * (Real.log N + 4)) * (Real.sqrt N)⁻¹ := by
  let p (k : ℕ) := ∑ n ∈ range (k + 1), a n
  let q (k : ℕ) := (Real.sqrt (k : ℝ))⁻¹
  let G (k : ℕ) := A + η * Real.log k
  have hq (k : ℕ) : 0 ≤ q k := by dsimp [q]; positivity
  have hgap (k : ℕ) (hk : 1 ≤ k) : 0 ≤ G k - p k := sub_nonneg.mpr (hb k hk)
  have haux : ∀ M : ℕ, N ≤ M →
      (∑ n ∈ Ioc N M, a n * q n) + (G M - p M) * q M ≤
        (G N - p N) * q N +
          η * ∑ n ∈ Ioc N M, (Real.log n - Real.log (n - 1 : ℕ)) * q n := by
    intro M hNM
    induction M, hNM using Nat.le_induction with
    | base => simp
    | succ M hNM ih =>
      have hM : 1 ≤ M := hN.trans hNM
      have hM0 : 0 < (M : ℝ) := by exact_mod_cast hM
      have hqle : q (M + 1) ≤ q M := by
        dsimp [q]
        simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hM0)
          (Real.sqrt_le_sqrt (by push_cast; linarith))
      have hdec := mul_le_mul_of_nonneg_left hqle (hgap M hM)
      have he : (∑ n ∈ Ioc N (M + 1), a n * q n) +
          (G (M + 1) - p (M + 1)) * q (M + 1) =
          (∑ n ∈ Ioc N M, a n * q n) + (G M - p M) * q (M + 1) +
            η * (Real.log (M + 1 : ℕ) - Real.log M) * q (M + 1) := by
        dsimp [p, G]
        rw [Finset.sum_Ioc_succ_top hNM, Finset.sum_range_succ]
        ring
      rw [he, Finset.sum_Ioc_succ_top hNM]
      simp only [Nat.add_sub_cancel]
      linarith
  have hlogsum : (∑ n ∈ Ioc N M,
      (Real.log n - Real.log (n - 1 : ℕ)) * q n) ≤ 4 * q N := by
    calc
      _ ≤ ∑ n ∈ Ioc N M, 2 * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_Ioc.mp hn).1
        have hn2 : 2 ≤ n := by omega
        have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        calc
          _ ≤ (2 / n) * q n := mul_le_mul_of_nonneg_right (log_nat_step_le hn2) (hq n)
          _ = _ := by
            rw [rpow_neg_one_add_half_eq_inv hn0]
            dsimp [q]
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ = 2 * ∑ n ∈ Ioc N M, (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 2 * (2 * q N) := mul_le_mul_of_nonneg_left (sum_Ioc_rpow_three_halves_le hN M) (by norm_num)
      _ = 4 * q N := by ring
  rcases le_or_gt N M with hNM | hMN
  · have hmain := haux M hNM
    have hlast := mul_nonneg (hgap M (hN.trans hNM)) (hq M)
    have hhead := mul_nonneg (Finset.sum_nonneg (s := range (N + 1)) fun n _ => ha n) (hq N)
    have hlog := mul_le_mul_of_nonneg_left hlogsum hη
    change (∑ n ∈ Ioc N M, a n * q n) ≤ (A + η * (Real.log N + 4)) * q N
    dsimp [G] at hmain
    change 0 ≤ p N * q N at hhead
    nlinarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity

/-- The same cumulative envelope controls the actual infinite shifted tail. -/
theorem tsum_shift_div_sqrt_le_of_log_envelope {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {A η : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hb : ∀ k : ℕ, 1 ≤ k → (∑ n ∈ range (k + 1), a n) ≤ A + η * Real.log k)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑' i : ℕ, a (i + (N + 1)) / Real.sqrt (i + (N + 1) : ℕ)) ≤
      (A + η * (Real.log N + 4)) * (Real.sqrt N)⁻¹ := by
  refine Real.tsum_le_of_sum_range_le
    (fun i => div_nonneg (ha _) (Real.sqrt_nonneg _)) fun m => ?_
  have he : (∑ i ∈ range m, a (i + (N + 1)) / Real.sqrt (i + (N + 1) : ℕ)) =
      ∑ n ∈ Ioc N (N + m), a n / Real.sqrt n := by
    have hI : Ioc N (N + m) = Ico (N + 1) (N + 1 + m) := by
      ext n
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hI, Finset.sum_Ico_eq_sum_range, show N + 1 + m - (N + 1) = m by omega]
    exact Finset.sum_congr rfl fun i _ => by rw [show N + 1 + i = i + (N + 1) by omega]
  rw [he]
  exact sum_Ioc_div_sqrt_le_of_log_envelope ha hA hη hb hN (N + m)

end RHTower.WeilSingularArithmetic
