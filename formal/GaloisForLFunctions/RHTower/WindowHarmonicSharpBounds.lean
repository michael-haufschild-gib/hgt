import GaloisForLFunctions.RHTower.PsiRemainderOneSidedWindowAverage

/-!
# Sharp window harmonic bounds

Two-sided evaluations of the window harmonic sums with error `O(1/y)` —
not `O(1)` — so that summed over a geometric ladder of windows the total
error stays bounded:

`|∑_{y < n ≤ z} 1/(n+1) − log(z/y)| ≤ 2/y`,
`|∑_{y < n ≤ z} 1/n − log(z/y)| ≤ 1/y`.

Both directions come from the increment sandwich
`log(n+1) − log n ∈ [1/(n+1), 1/n]` and telescoping; the `O(1/y)` losses
are the boundary shifts `log(y+2) − log y ≤ 2/y` and `1/(z+1) ≤ 1/y`.
-/

noncomputable section

namespace RHTower

open Finset

/-- Telescoped log increments over a window. -/
theorem sum_log_inc_window (y z : ℕ) (hyz : y ≤ z) :
    ∑ n ∈ Finset.Ioc y z, (Real.log ((n : ℝ) + 1) - Real.log n)
      = Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1) := by
  have hIco : Finset.Ioc y z = Finset.Ico (y + 1) (z + 1) := by
    ext x
    rw [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hcongr : ∑ n ∈ Finset.Ioc y z,
      (Real.log ((n : ℝ) + 1) - Real.log n)
      = ∑ n ∈ Finset.Ioc y z,
          (Real.log (((n + 1 : ℕ)) : ℝ) - Real.log ((n : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hcongr, hIco, Finset.sum_Ico_eq_sub _ (show y + 1 ≤ z + 1 by omega),
    Finset.sum_range_sub (fun n => Real.log ((n : ℕ) : ℝ)) (z + 1),
    Finset.sum_range_sub (fun n => Real.log ((n : ℕ) : ℝ)) (y + 1)]
  push_cast
  ring

/-- **Sharp shifted harmonic window**:
`|∑_{y < n ≤ z} 1/(n+1) − (log z − log y)| ≤ 2/y`. -/
theorem abs_sum_inv_succ_window_sub_le {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    |(∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1))
        - (Real.log z - Real.log y)| ≤ 2 / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  -- upper: `1/(n+1) ≤ log(n+1) − log n`
  have hup : ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1)
      ≤ Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1) := by
    rw [← sum_log_inc_window y z hyz]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact inv_succ_le_log_succ_sub (by omega)
  -- lower: `1/(n+1) ≥ log(n+2) − log(n+1)`
  have hlo : Real.log ((z : ℝ) + 2) - Real.log ((y : ℝ) + 2)
      ≤ ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
    have hterm : ∀ n ∈ Finset.Ioc y z,
        Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1)
          ≤ 1 / ((n : ℝ) + 1) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have h := log_succ_sub_log_le (j := n + 1) (by omega)
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hc] at h
      linarith
    have htel : ∑ n ∈ Finset.Ioc y z,
        (Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1))
        = Real.log ((z : ℝ) + 2) - Real.log ((y : ℝ) + 2) := by
      have hshift : ∑ n ∈ Finset.Ioc y z,
          (Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1))
          = ∑ n ∈ Finset.Ioc (y + 1) (z + 1),
              (Real.log ((n : ℝ) + 1) - Real.log n) := by
        apply Finset.sum_nbij' (i := fun n => n + 1) (j := fun n => n - 1)
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro n _
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          omega
        · intro n _
          push_cast
          ring_nf
      rw [hshift, sum_log_inc_window (y + 1) (z + 1) (by omega)]
      push_cast
      rw [show (z : ℝ) + 1 + 1 = (z : ℝ) + 2 from by ring,
        show (y : ℝ) + 1 + 1 = (y : ℝ) + 2 from by ring]
    rw [← htel]
    exact Finset.sum_le_sum hterm
  -- boundary reconciliation
  have hb1 : Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1)
      ≤ Real.log z - Real.log y + 1 / y := by
    have h1 : Real.log ((z : ℝ) + 1) ≤ Real.log z + 1 / z := by
      have := log_succ_sub_log_le (le_trans hy hyz)
      linarith
    have h2 : Real.log y ≤ Real.log ((y : ℝ) + 1) := by
      apply Real.log_le_log hy0
      linarith
    have h3 : 1 / (z : ℝ) ≤ 1 / y :=
      div_le_div_of_nonneg_left one_pos.le hy0 (by exact_mod_cast hyz)
    linarith
  have hb2 : Real.log z - Real.log y - 2 / y
      ≤ Real.log ((z : ℝ) + 2) - Real.log ((y : ℝ) + 2) := by
    have h1 : Real.log z ≤ Real.log ((z : ℝ) + 2) := by
      apply Real.log_le_log hz0
      linarith
    have h2 : Real.log ((y : ℝ) + 1) ≤ Real.log y + 1 / y := by
      have := log_succ_sub_log_le hy
      linarith
    have h3 : Real.log ((y : ℝ) + 2) ≤ Real.log ((y : ℝ) + 1)
        + 1 / ((y : ℝ) + 1) := by
      have h4 := log_succ_sub_log_le (j := y + 1) (by omega)
      have hc : ((y + 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
      rw [hc] at h4
      have h5 : (y : ℝ) + 1 + 1 = (y : ℝ) + 2 := by ring
      rw [h5] at h4
      linarith
    have h6 : 1 / ((y : ℝ) + 1) ≤ 1 / y :=
      div_le_div_of_nonneg_left one_pos.le hy0 (by linarith)
    have h7 : 2 / (y : ℝ) = 1 / y + 1 / y := by ring
    linarith
  have h7 : 2 / (y : ℝ) = 1 / y + 1 / y := by ring
  have h8 : 0 ≤ 1 / (y : ℝ) := by positivity
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Sharp harmonic window**:
`|∑_{y < n ≤ z} 1/n − (log z − log y)| ≤ 1/y`. -/
theorem abs_sum_inv_window_sub_le {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    |(∑ n ∈ Finset.Ioc y z, 1 / (n : ℝ))
        - (Real.log z - Real.log y)| ≤ 1 / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  -- lower: `1/n ≥ log(n+1) − log n` since `log(1+x) ≤ x`
  have hlo : Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1)
      ≤ ∑ n ∈ Finset.Ioc y z, 1 / (n : ℝ) := by
    rw [← sum_log_inc_window y z hyz]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have := log_succ_sub_log_le (j := n) (by omega)
    linarith
  -- upper: `1/n ≤ log n − log(n−1)`
  have hup : ∑ n ∈ Finset.Ioc y z, 1 / (n : ℝ)
      ≤ Real.log z - Real.log y := by
    have hterm : ∀ n ∈ Finset.Ioc y z,
        1 / (n : ℝ) ≤ Real.log n - Real.log ((n : ℝ) - 1) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn2 : 2 ≤ n := by omega
      have hn1R : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        linarith
      have h := inv_succ_le_log_succ_sub (n := n - 1) (by omega)
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc] at h
      have h5 : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
      rw [h5] at h
      linarith
    have htel : ∑ n ∈ Finset.Ioc y z,
        (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1))
        = Real.log z - Real.log y := by
      have hshift : ∑ n ∈ Finset.Ioc y z,
          (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1))
          = ∑ n ∈ Finset.Ioc (y - 1) (z - 1),
              (Real.log ((n : ℝ) + 1) - Real.log n) := by
        apply Finset.sum_nbij' (i := fun n => n - 1) (j := fun n => n + 1)
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          omega
        · intro n _
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          rw [hc]
          have h5 : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
          rw [h5]
      rw [hshift, sum_log_inc_window (y - 1) (z - 1) (by omega)]
      have hc1 : (((z - 1 : ℕ)) : ℝ) + 1 = (z : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        ring
      have hc2 : (((y - 1 : ℕ)) : ℝ) + 1 = (y : ℝ) := by
        rw [Nat.cast_sub hy, Nat.cast_one]
        ring
      rw [hc1, hc2]
    rw [← htel]
    exact Finset.sum_le_sum hterm
  -- boundary reconciliation for the lower side
  have hb : Real.log z - Real.log y - 1 / y
      ≤ Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1) := by
    have h1 : Real.log z ≤ Real.log ((z : ℝ) + 1) := by
      apply Real.log_le_log hz0
      linarith
    have h2 : Real.log ((y : ℝ) + 1) ≤ Real.log y + 1 / y := by
      have := log_succ_sub_log_le hy
      linarith
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

end RHTower
