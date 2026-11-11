import Mathlib

/-!
# Logarithmic averages

`A_x(f) = (1/log x) Σ_{1 ≤ n ≤ x} f(n)/n` (`logAvg`). For `|f| ≤ B`:

* `|Σ_{n ≤ N} f(n)/n| ≤ B(1 + log N)` (`abs_logSum_le`);
* a unit shift costs `3B` before normalisation (`abs_logSum_shift_sub_le`): the sum of
  `f(n+1)/n` and the sum of `f(n)/n` differ by a telescoping boundary term and by
  `Σ f(n+1)(1/n − 1/(n+1))`;
* a dilation by `d` turns into the weight `d·1_{d|m}` at cost `dB` (`abs_logSum_dilate_sub_le`):
  `Σ_{m ≤ N, d|m} d f(m)/m = Σ_{n ≤ N/d} f(dn)/n`, and the terms `N/d < n ≤ N` of the dilated sum
  are at most `N/(⌊N/d⌋ + 1) ≤ d` in number times `1/(⌊N/d⌋+1)`;
* `A_x(1) → 1` (`tendsto_logAvg_one`), from `log x ≤ H_{⌊x⌋} ≤ 1 + log x`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology

noncomputable section

/-- `Σ_{1 ≤ n ≤ N} f(n)/n`. -/
def logSum (f : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, f (n + 1) / ((n : ℝ) + 1)

/-- The logarithmic average `A_x(f) = (1/log x) Σ_{1 ≤ n ≤ x} f(n)/n`. -/
def logAvg (f : ℕ → ℝ) (x : ℝ) : ℝ := logSum f ⌊x⌋₊ / Real.log x

theorem logSum_add (f g : ℕ → ℝ) (N : ℕ) :
    logSum (fun n => f n + g n) N = logSum f N + logSum g N := by
  simp only [logSum, add_div, sum_add_distrib]

theorem logSum_smul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    logSum (fun n => c * f n) N = c * logSum f N := by
  simp only [logSum, mul_div_assoc, mul_sum]

theorem logSum_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (N : ℕ) :
    logSum (fun n => ∑ i ∈ s, f i n) N = ∑ i ∈ s, logSum (f i) N := by
  simp only [logSum, sum_div]
  exact sum_comm

theorem logSum_mono {f g : ℕ → ℝ} (h : ∀ n, f n ≤ g n) (N : ℕ) : logSum f N ≤ logSum g N :=
  sum_le_sum fun n _ => div_le_div_of_nonneg_right (h _) (by positivity)

theorem logSum_one (N : ℕ) : logSum (fun _ => 1) N = (harmonic N : ℝ) := by
  simp only [logSum, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  refine sum_congr rfl fun n _ => ?_
  push_cast
  ring

theorem harmonic_le_one_add_log' (N : ℕ) : (harmonic N : ℝ) ≤ 1 + Real.log N :=
  harmonic_le_one_add_log N

/-- `|Σ_{n ≤ N} f(n)/n| ≤ B (1 + log N)`. -/
theorem abs_logSum_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) (N : ℕ) :
    |logSum f N| ≤ B * (1 + Real.log N) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  have h1 : |logSum f N| ≤ logSum (fun _ => B) N := by
    unfold logSum
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    exact div_le_div_of_nonneg_right (hf _) (by positivity)
  have h2 : logSum (fun _ => B) N = B * (harmonic N : ℝ) := by
    rw [← logSum_one, ← logSum_smul]
    simp
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log' N) hB)

/-- **Unit shift.** `|Σ_{n≤N} f(n+1)/n − Σ_{n≤N} f(n)/n| ≤ 3B`. -/
theorem abs_logSum_shift_sub_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) (N : ℕ) :
    |logSum (fun n => f (n + 1)) N - logSum f N| ≤ 3 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  set g : ℕ → ℝ := fun n => f (n + 1) / ((n : ℝ) + 1) with hg
  set e : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1)) with he
  have hsplit : logSum (fun n => f (n + 1)) N - logSum f N
      = (∑ n ∈ range N, (g (n + 1) - g n))
        + ∑ n ∈ range N, f (n + 2) * (e (n + 1) - e n) := by
    unfold logSum
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [hg, he]
    push_cast
    field_simp
    ring
  rw [hsplit, sum_range_sub]
  have hg0 : |g 0| ≤ B := by simpa [hg] using hf 1
  have hgN : |g N| ≤ B := by
    simp only [hg]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N + 1)]
    calc |f (N + 1)| / ((N : ℝ) + 1) ≤ |f (N + 1)| :=
          div_le_self (abs_nonneg _) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      _ ≤ B := hf _
  have hstep : ∀ n : ℕ, 0 ≤ e (n + 1) - e n := by
    intro n
    simp only [he]
    push_cast
    have h1 : (0 : ℝ) < n + 1 := by positivity
    have h2 : (0 : ℝ) < n + 1 + 1 := by positivity
    rw [neg_sub_neg, sub_nonneg]
    exact div_le_div_of_nonneg_left zero_le_one h1 (by linarith)
  have htel : |∑ n ∈ range N, f (n + 2) * (e (n + 1) - e n)| ≤ B := by
    calc |∑ n ∈ range N, f (n + 2) * (e (n + 1) - e n)|
        ≤ ∑ n ∈ range N, |f (n + 2) * (e (n + 1) - e n)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range N, B * (e (n + 1) - e n) := by
          refine sum_le_sum fun n _ => ?_
          rw [abs_mul, abs_of_nonneg (hstep n)]
          exact mul_le_mul_of_nonneg_right (hf _) (hstep n)
      _ = B * (e N - e 0) := by rw [← mul_sum, sum_range_sub]
      _ ≤ B * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hB
          simp only [he]
          have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          have : 0 < 1 / ((N : ℝ) + 1) := by positivity
          norm_num
          linarith
      _ = B := mul_one B
  calc |g N - g 0 + ∑ n ∈ range N, f (n + 2) * (e (n + 1) - e n)|
      ≤ |g N - g 0| + |∑ n ∈ range N, f (n + 2) * (e (n + 1) - e n)| := abs_add_le _ _
    _ ≤ (|g N| + |g 0|) + B := add_le_add (abs_sub _ _) htel
    _ ≤ 3 * B := by linarith

/-- `Σ_{m ≤ N, d | m} d f(m)/m = Σ_{n ≤ N/d} f(dn)/n`. -/
theorem logSum_dvd_weight (f : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    logSum (fun m => if d ∣ m then (d : ℝ) * f m else 0) N
      = logSum (fun n => f (d * n)) (N / d) := by
  induction N with
  | zero => simp [logSum]
  | succ N ih =>
    have hs : logSum (fun m => if d ∣ m then (d : ℝ) * f m else 0) (N + 1)
        = logSum (fun m => if d ∣ m then (d : ℝ) * f m else 0) N
          + (if d ∣ N + 1 then (d : ℝ) * f (N + 1) else 0) / ((N : ℝ) + 1) := by
      simp [logSum, sum_range_succ]
    rw [hs, ih, Nat.succ_div]
    by_cases hdv : d ∣ N + 1
    · rw [if_pos hdv, if_pos hdv]
      obtain ⟨k, hk⟩ := hdv
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · omega
        · exact h
      have hNd : N / d = k - 1 := by
        have h1 : N = d * (k - 1) + (d - 1) := by
          obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hkpos
          simp only [Nat.zero_add] at hk ⊢
          rw [Nat.add_sub_cancel]
          have : d * (j + 1) = d * j + d := by ring
          omega
        rw [h1, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hd,
          Nat.div_eq_of_lt (by omega)]
        simp
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      rw [hNd]
      simp only [logSum, sum_range_succ]
      congr 1
      rw [hk', hk]
      have hkR : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hk'
      have hNR : (N : ℝ) + 1 = (d : ℝ) * k := by exact_mod_cast hk
      rw [hkR, hNR]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hkR' : (0 : ℝ) < k := by exact_mod_cast hkpos
      field_simp
    · rw [if_neg hdv, if_neg hdv]
      simp

/-- **Dilation.** `|Σ_{n ≤ N} f(dn)/n − Σ_{m ≤ N} d·1_{d|m} f(m)/m| ≤ dB`. -/
theorem abs_logSum_dilate_sub_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) {d : ℕ} (hd : 0 < d)
    (N : ℕ) :
    |logSum (fun n => f (d * n)) N - logSum (fun m => if d ∣ m then (d : ℝ) * f m else 0) N|
      ≤ d * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  rw [logSum_dvd_weight f hd N]
  have hK : N / d ≤ N := Nat.div_le_self N d
  have hsplit : logSum (fun n => f (d * n)) N - logSum (fun n => f (d * n)) (N / d)
      = ∑ n ∈ Ico (N / d) N, f (d * (n + 1)) / ((n : ℝ) + 1) := by
    unfold logSum
    rw [← sum_range_add_sum_Ico _ hK]
    ring
  rw [hsplit]
  have hKd : (N : ℝ) ≤ d * ((N / d : ℕ) + 1 : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) hd
    have : N ≤ d * (N / d + 1) := by nlinarith
    exact_mod_cast this
  have hKpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by positivity
  calc |∑ n ∈ Ico (N / d) N, f (d * (n + 1)) / ((n : ℝ) + 1)|
      ≤ ∑ n ∈ Ico (N / d) N, |f (d * (n + 1)) / ((n : ℝ) + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ico (N / d) N, B / (((N / d : ℕ) : ℝ) + 1) := by
        refine sum_le_sum fun n hn => ?_
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
        have hn' : ((N / d : ℕ) : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
        calc |f (d * (n + 1))| / ((n : ℝ) + 1) ≤ B / ((n : ℝ) + 1) :=
              div_le_div_of_nonneg_right (hf _) (by positivity)
          _ ≤ B / (((N / d : ℕ) : ℝ) + 1) :=
              div_le_div_of_nonneg_left hB hKpos (by linarith)
    _ = ((N - N / d : ℕ) : ℝ) * (B / (((N / d : ℕ) : ℝ) + 1)) := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (B / (((N / d : ℕ) : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.sub_le N (N / d)
    _ ≤ d * B := by
        rw [mul_div_assoc', div_le_iff₀ hKpos]
        nlinarith

/-- `A_x(1) → 1`. -/
theorem tendsto_logAvg_one : Tendsto (logAvg fun _ => 1) atTop (𝓝 1) := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hinv : Tendsto (fun x => 1 + 1 / Real.log x) atTop (𝓝 1) := by
    have := (hlog.inv_tendsto_atTop).const_add 1
    simpa [one_div] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    rw [logAvg, logSum_one, le_div_iff₀ hl, one_mul]
    exact log_le_harmonic_floor x (by linarith)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    rw [logAvg, logSum_one, div_le_iff₀ hl, add_mul, one_mul, div_mul_cancel₀ _ hl.ne']
    linarith [harmonic_floor_le_one_add_log x hx.le]

/-- A bounded sequence has bounded logarithmic averages: `|A_x(f)| ≤ 2B` for `x ≥ e`. -/
theorem abs_logAvg_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) {x : ℝ}
    (hx : Real.exp 1 ≤ x) : |logAvg f x| ≤ 2 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hfl : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast h) (Nat.floor_le hx0.le)
  have hl0 : 0 < Real.log x := by linarith
  rw [logAvg, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
  calc |logSum f ⌊x⌋₊| ≤ B * (1 + Real.log ⌊x⌋₊) := abs_logSum_le hf _
    _ ≤ B * (1 + Real.log x) := by gcongr
    _ ≤ 2 * B * Real.log x := by nlinarith

/-- Unit shift after normalisation: `|A_x(f(·+1)) − A_x(f)| ≤ 3B/log x`. -/
theorem abs_logAvg_shift_sub_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) {x : ℝ}
    (hx : 1 < x) : |logAvg (fun n => f (n + 1)) x - logAvg f x| ≤ 3 * B / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [logAvg, logAvg, ← sub_div, abs_div, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (abs_logSum_shift_sub_le hf _) hl.le

/-- Dilation after normalisation: `|A_x(f(d·)) − A_x(d·1_{d|·} f)| ≤ dB/log x`. -/
theorem abs_logAvg_dilate_sub_le {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx : 1 < x) :
    |logAvg (fun n => f (d * n)) x - logAvg (fun m => if d ∣ m then (d : ℝ) * f m else 0) x|
      ≤ d * B / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [logAvg, logAvg, ← sub_div, abs_div, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (abs_logSum_dilate_sub_le hf hd _) hl.le

end

end GaloisForLFunctions.LogarithmicChowla
