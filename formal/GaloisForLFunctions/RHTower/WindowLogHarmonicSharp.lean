import GaloisForLFunctions.RHTower.FiberVariationBound

/-!
# Sharp window bounds for the log-harmonic weight

The m-space ladder weight `(2 log m + 2)/m` has antiderivative
`G(t) = log²t + 2 log t`, and on any window the sum tracks the increment
with error `O(log y / y)`:

`|∑_{y < m ≤ z} (2 log m + 2)/m − (log²z + 2 log z − log²y − 2 log y)|
   ≤ (2 log(y+1) + 6)/y`  for `2 ≤ y ≤ z`.

Both directions come from the exact identities
`(2 log m + 2)·Δ = ΔG ± Δ²` for the left/right log increments `Δ`, the
`G`-telescope, and the reciprocal-square tail.  The error is geometric-
ladder-summable, so the m-space contraction pays it only at the base.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The `G = log² + 2log` telescope over a window. -/
theorem sum_G_inc_window (y z : ℕ) (hyz : y ≤ z) :
    ∑ m ∈ Finset.Ioc y z,
        ((Real.log ((m : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ) + 1))
          - (Real.log m ^ (2 : ℕ) + 2 * Real.log m))
      = (Real.log ((z : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((z : ℝ) + 1))
        - (Real.log ((y : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((y : ℝ) + 1)) := by
  have hcongr : ∑ m ∈ Finset.Ioc y z,
      ((Real.log ((m : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ) + 1))
        - (Real.log m ^ (2 : ℕ) + 2 * Real.log m))
      = ∑ m ∈ Finset.Ioc y z,
          ((Real.log (((m + 1 : ℕ)) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log (((m + 1 : ℕ)) : ℝ))
            - (Real.log ((m : ℕ) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log ((m : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    ring
  have hIco : Finset.Ioc y z = Finset.Ico (y + 1) (z + 1) := by
    ext x
    rw [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hcongr, hIco, Finset.sum_Ico_eq_sub _ (show y + 1 ≤ z + 1 by omega),
    Finset.sum_range_sub (fun m => Real.log ((m : ℕ) : ℝ) ^ (2 : ℕ)
      + 2 * Real.log ((m : ℕ) : ℝ)) (z + 1),
    Finset.sum_range_sub (fun m => Real.log ((m : ℕ) : ℝ) ^ (2 : ℕ)
      + 2 * Real.log ((m : ℕ) : ℝ)) (y + 1)]
  push_cast
  ring

/-- **Sharp log-harmonic window (upper)**: for `2 ≤ y ≤ z`,
`∑_{y < m ≤ z} (2 log m + 2)/m
   ≤ log²z + 2 log z − log²y − 2 log y + (2 log(y+1) + 6)/y`. -/
theorem sum_log_harmonic_window_le {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) :
    ∑ m ∈ Finset.Ioc y z, (2 * Real.log m + 2) / m
      ≤ (Real.log z ^ (2 : ℕ) + 2 * Real.log z)
        - (Real.log y ^ (2 : ℕ) + 2 * Real.log y)
        + (2 * Real.log ((y : ℝ) + 1) + 6) / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  -- per-term: `(2logm+2)/m ≤ ΔG(m−1→m) + Δ²`
  have hterm : ∀ m ∈ Finset.Ioc y z,
      (2 * Real.log m + 2) / m
        ≤ ((Real.log ((m : ℝ)) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ)))
            - (Real.log ((m - 1 : ℕ) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log ((m - 1 : ℕ) : ℝ)))
          + (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hm1R : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < m - 1)
    have hlog0 : 0 ≤ Real.log m :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hinc := inv_succ_le_log_succ_sub (n := m - 1) (by omega)
    have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    rw [hc] at hinc
    -- `1/m ≤ Δ` where `Δ = log m − log(m−1)`
    have hΔ0 : 0 ≤ Real.log m - Real.log ((m - 1 : ℕ) : ℝ) := by
      have := Real.log_le_log hm1R (show ((m - 1 : ℕ) : ℝ) ≤ m by linarith)
      linarith
    have hkey : (2 * Real.log m + 2)
        * (Real.log m - Real.log ((m - 1 : ℕ) : ℝ))
        = ((Real.log ((m : ℝ)) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ)))
            - (Real.log ((m - 1 : ℕ) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log ((m - 1 : ℕ) : ℝ)))
          + (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
      ring
    calc (2 * Real.log m + 2) / m
        = (2 * Real.log m + 2) * (1 / m) := by ring
      _ ≤ (2 * Real.log m + 2)
          * (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hinc (by linarith)
      _ = _ := hkey
  -- telescope + tail
  have hteles : ∑ m ∈ Finset.Ioc y z,
      ((Real.log ((m : ℝ)) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ)))
        - (Real.log ((m - 1 : ℕ) : ℝ) ^ (2 : ℕ)
          + 2 * Real.log ((m - 1 : ℕ) : ℝ)))
      = (Real.log z ^ (2 : ℕ) + 2 * Real.log z)
        - (Real.log y ^ (2 : ℕ) + 2 * Real.log y) := by
    have hre : ∑ m ∈ Finset.Ioc y z,
        ((Real.log ((m : ℝ)) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ)))
          - (Real.log ((m - 1 : ℕ) : ℝ) ^ (2 : ℕ)
            + 2 * Real.log ((m - 1 : ℕ) : ℝ)))
        = ∑ n ∈ Finset.Ioc (y - 1) (z - 1),
            ((Real.log ((n : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((n : ℝ) + 1))
              - (Real.log n ^ (2 : ℕ) + 2 * Real.log n)) := by
      apply Finset.sum_nbij' (i := fun m => m - 1) (j := fun n => n + 1)
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Ioc]
        omega
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [Finset.mem_Ioc]
        omega
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        omega
      · intro n _
        omega
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        rw [hc]
    rw [hre, sum_G_inc_window (y - 1) (z - 1) (by omega)]
    have hc1 : (((z - 1 : ℕ)) : ℝ) + 1 = (z : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    have hc2 : (((y - 1 : ℕ)) : ℝ) + 1 = (y : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    rw [hc1, hc2]
  have htail : ∑ m ∈ Finset.Ioc y z,
      (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
      ≤ 2 / (y : ℝ) := by
    have hle : ∀ m ∈ Finset.Ioc y z,
        (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ 1 / ((m - 2 : ℕ) : ℝ) - 1 / ((m - 1 : ℕ) : ℝ) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2R : (0 : ℝ) < ((m - 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < m - 2)
      have hm1R : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < m - 1)
      have hinc := log_succ_sub_log_le (j := m - 1) (by omega)
      have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        linarith
      rw [hc] at hinc
      have hΔ0 : 0 ≤ Real.log m - Real.log ((m - 1 : ℕ) : ℝ) := by
        have := Real.log_le_log hm1R
          (show ((m - 1 : ℕ) : ℝ) ≤ m by linarith)
        linarith
      have h1 : (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ (1 / ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hΔ0 hinc 2
      have hgap : ((m - 1 : ℕ) : ℝ) - ((m - 2 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      have heq : 1 / ((m - 2 : ℕ) : ℝ) - 1 / ((m - 1 : ℕ) : ℝ)
          = 1 / (((m - 2 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) := by
        rw [div_sub_div _ _ hm2R.ne' hm1R.ne']
        rw [show (1 : ℝ) * ((m - 1 : ℕ) : ℝ) - ((m - 2 : ℕ) : ℝ) * 1
          = ((m - 1 : ℕ) : ℝ) - ((m - 2 : ℕ) : ℝ) from by ring, hgap]
      have h2 : (1 / ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ 1 / (((m - 2 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) := by
        rw [div_pow, one_pow]
        apply div_le_div_of_nonneg_left one_pos.le (by positivity)
        have h3 : ((m - 2 : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : m - 2 ≤ m - 1)
        nlinarith [mul_le_mul_of_nonneg_right h3 hm1R.le]
      linarith [h1, h2, heq.ge, heq.le]
    have hre : ∑ m ∈ Finset.Ioc y z,
        (1 / ((m - 2 : ℕ) : ℝ) - 1 / ((m - 1 : ℕ) : ℝ))
        = ∑ n ∈ Finset.Icc (y - 1) (z - 2),
            (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_nbij' (i := fun m => m - 2) (j := fun n => n + 2)
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        omega
      · intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc]
        omega
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        omega
      · intro n _
        omega
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        have hc1 : ((m - 1 : ℕ) : ℝ) = ((m - 2 : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hc1]
    rcases Nat.lt_or_ge z (y + 1) with hzy | hzy
    · have hempty : Finset.Ioc y z = ∅ := by
        apply Finset.Ioc_eq_empty
        omega
      rw [hempty, Finset.sum_empty]
      positivity
    · have htel := sum_reciprocal_telescope
        (k := y - 1) (N := z - 2) (by omega) (by omega)
      rw [Finset.sum_congr rfl (fun m hm => rfl)] at hre
      have hy1R : (0 : ℝ) < ((y - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < y - 1)
      have hfinal : 1 / ((y - 1 : ℕ) : ℝ) ≤ 2 / y := by
        have hc2 : ((y - 1 : ℕ) : ℝ) = (y : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hc2, div_le_div_iff₀ (by rw [← hc2]; exact hy1R) hy0]
        have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
        nlinarith
      have hnn : (0 : ℝ) ≤ 1 / ((((z - 2 : ℕ)) : ℝ) + 1) := by
        positivity
      calc ∑ m ∈ Finset.Ioc y z,
            (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ ∑ m ∈ Finset.Ioc y z,
              (1 / ((m - 2 : ℕ) : ℝ) - 1 / ((m - 1 : ℕ) : ℝ)) :=
            Finset.sum_le_sum hle
        _ = ∑ n ∈ Finset.Icc (y - 1) (z - 2),
              (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := hre
        _ = 1 / ((y - 1 : ℕ) : ℝ) - 1 / ((((z - 2 : ℕ)) : ℝ) + 1) := htel
        _ ≤ 2 / y := by linarith [hfinal]
  -- combine
  have hlogy1 : Real.log ((y : ℝ) + 1) ≥ 0 := by
    apply Real.log_nonneg
    linarith
  calc ∑ m ∈ Finset.Ioc y z, (2 * Real.log m + 2) / m
      ≤ ∑ m ∈ Finset.Ioc y z,
          (((Real.log ((m : ℝ)) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ)))
            - (Real.log ((m - 1 : ℕ) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log ((m - 1 : ℕ) : ℝ)))
          + (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ)) :=
        Finset.sum_le_sum hterm
    _ = ((Real.log z ^ (2 : ℕ) + 2 * Real.log z)
          - (Real.log y ^ (2 : ℕ) + 2 * Real.log y))
        + ∑ m ∈ Finset.Ioc y z,
            (Real.log m - Real.log ((m - 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
        rw [Finset.sum_add_distrib, hteles]
    _ ≤ (Real.log z ^ (2 : ℕ) + 2 * Real.log z)
        - (Real.log y ^ (2 : ℕ) + 2 * Real.log y)
        + (2 * Real.log ((y : ℝ) + 1) + 6) / y := by
        have h1 : (2 : ℝ) / y ≤ (2 * Real.log ((y : ℝ) + 1) + 6) / y := by
          gcongr
          linarith
        linarith [htail]

/-- **Sharp log-harmonic window (lower)**: for `1 ≤ y ≤ z`,
`∑_{y < m ≤ z} (2 log m + 2)/m
   ≥ log²z + 2 log z − log²y − 2 log y − (2 log(y+1) + 3)/y`. -/
theorem sum_log_harmonic_window_ge {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    (Real.log z ^ (2 : ℕ) + 2 * Real.log z)
      - (Real.log y ^ (2 : ℕ) + 2 * Real.log y)
      - (2 * Real.log ((y : ℝ) + 1) + 3) / y
    ≤ ∑ m ∈ Finset.Ioc y z, (2 * Real.log m + 2) / m := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  -- per-term lower: `(2logm+2)/m ≥ ΔG(m→m+1) − (Δ⁺)²`
  have hterm : ∀ m ∈ Finset.Ioc y z,
      ((Real.log ((m : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ) + 1))
          - (Real.log m ^ (2 : ℕ) + 2 * Real.log m))
        - (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ)
      ≤ (2 * Real.log m + 2) / m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlog0 : 0 ≤ Real.log m :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hinc := log_succ_sub_log_le (j := m) (by omega)
    have hkey : (2 * Real.log m + 2)
        * (Real.log ((m : ℝ) + 1) - Real.log m)
        = ((Real.log ((m : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ) + 1))
            - (Real.log m ^ (2 : ℕ) + 2 * Real.log m))
          - (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ) := by
      ring
    calc ((Real.log ((m : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((m : ℝ) + 1))
            - (Real.log m ^ (2 : ℕ) + 2 * Real.log m))
          - (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ)
        = (2 * Real.log m + 2)
          * (Real.log ((m : ℝ) + 1) - Real.log m) := hkey.symm
      _ ≤ (2 * Real.log m + 2) * (1 / m) := by
          apply mul_le_mul_of_nonneg_left hinc (by linarith)
      _ = (2 * Real.log m + 2) / m := by ring
  -- telescoped main part
  have hG := sum_G_inc_window y z hyz
  -- squared-increment tail
  have htail2 : ∑ m ∈ Finset.Ioc y z,
      (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ) ≤ 1 / y := by
    rcases Nat.lt_or_ge y z with hyz' | hyz'
    · have hle : ∀ m ∈ Finset.Ioc y z,
          (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ)
            ≤ 1 / ((m - 1 : ℕ) : ℝ) - 1 / ((m : ℕ) : ℝ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        have hm1R : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < m - 1)
        have hmR : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast (by omega : 0 < m)
        have hinc := log_succ_sub_log_le (j := m) (by omega)
        have hΔ0 : 0 ≤ Real.log ((m : ℝ) + 1) - Real.log m := by
          have := Real.log_le_log hmR
            (show (m : ℝ) ≤ (m : ℝ) + 1 by linarith)
          linarith
        have h1 : (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ)
            ≤ (1 / (m : ℝ)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hΔ0 hinc 2
        have hgap : (m : ℝ) - ((m - 1 : ℕ) : ℝ) = 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          ring
        have heq : 1 / ((m - 1 : ℕ) : ℝ) - 1 / ((m : ℕ) : ℝ)
            = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
          rw [div_sub_div _ _ hm1R.ne' hmR.ne']
          rw [show (1 : ℝ) * (m : ℝ) - ((m - 1 : ℕ) : ℝ) * 1
            = (m : ℝ) - ((m - 1 : ℕ) : ℝ) from by ring, hgap]
        have h2 : (1 / (m : ℝ)) ^ (2 : ℕ)
            ≤ 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
          rw [div_pow, one_pow]
          apply div_le_div_of_nonneg_left one_pos.le (by positivity)
          have h3 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast (by omega : m - 1 ≤ m)
          nlinarith [mul_le_mul_of_nonneg_right h3 hmR.le]
        linarith [h1, h2, heq.ge, heq.le]
      have hre : ∑ m ∈ Finset.Ioc y z,
          (1 / ((m - 1 : ℕ) : ℝ) - 1 / ((m : ℕ) : ℝ))
          = ∑ n ∈ Finset.Icc y (z - 1),
              (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
        apply Finset.sum_nbij' (i := fun m => m - 1) (j := fun n => n + 1)
        · intro m hm
          rw [Finset.mem_Ioc] at hm
          rw [Finset.mem_Icc]
          omega
        · intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro m hm
          rw [Finset.mem_Ioc] at hm
          omega
        · intro n _
          omega
        · intro m hm
          rw [Finset.mem_Ioc] at hm
          have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
            linarith
          rw [hc]
      have htel := sum_reciprocal_telescope
        (k := y) (N := z - 1) hy (by omega)
      have hnn : (0 : ℝ) ≤ 1 / ((((z - 1 : ℕ)) : ℝ) + 1) := by
        positivity
      calc ∑ m ∈ Finset.Ioc y z,
            (Real.log ((m : ℝ) + 1) - Real.log m) ^ (2 : ℕ)
          ≤ ∑ m ∈ Finset.Ioc y z,
              (1 / ((m - 1 : ℕ) : ℝ) - 1 / ((m : ℕ) : ℝ)) :=
            Finset.sum_le_sum hle
        _ = ∑ n ∈ Finset.Icc y (z - 1),
              (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := hre
        _ = 1 / (y : ℝ) - 1 / ((((z - 1 : ℕ)) : ℝ) + 1) := htel
        _ ≤ 1 / y := by linarith
    · have hzy : z = y := by omega
      rw [hzy, Finset.Ioc_self, Finset.sum_empty]
      positivity
  -- boundary reconciliation
  have hb1 : Real.log ((z : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((z : ℝ) + 1)
      ≥ Real.log z ^ (2 : ℕ) + 2 * Real.log z := by
    have h1 : Real.log z ≤ Real.log ((z : ℝ) + 1) :=
      Real.log_le_log hz0 (by linarith)
    have h2 : 0 ≤ Real.log z :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
    nlinarith [h1, h2]
  have hb2 : Real.log ((y : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((y : ℝ) + 1)
      ≤ Real.log y ^ (2 : ℕ) + 2 * Real.log y
        + (2 * Real.log ((y : ℝ) + 1) + 2) / y := by
    have h1 := log_succ_sub_log_le hy
    have h2 : 0 ≤ Real.log y :=
      Real.log_nonneg (by exact_mod_cast hy)
    have h3 : Real.log y ≤ Real.log ((y : ℝ) + 1) :=
      Real.log_le_log hy0 (by linarith)
    have hkey : Real.log ((y : ℝ) + 1) ^ (2 : ℕ) + 2 * Real.log ((y : ℝ) + 1)
        - (Real.log y ^ (2 : ℕ) + 2 * Real.log y)
        = (Real.log ((y : ℝ) + 1) - Real.log y)
          * (Real.log ((y : ℝ) + 1) + Real.log y + 2) := by
      ring
    have h4 : (Real.log ((y : ℝ) + 1) - Real.log y)
        * (Real.log ((y : ℝ) + 1) + Real.log y + 2)
        ≤ (1 / y) * (2 * Real.log ((y : ℝ) + 1) + 2) := by
      apply mul_le_mul h1 (by linarith) (by linarith) (by positivity)
    have h5 : (1 / (y : ℝ)) * (2 * Real.log ((y : ℝ) + 1) + 2)
        = (2 * Real.log ((y : ℝ) + 1) + 2) / y := by
      ring
    linarith [hkey.le, hkey.ge, h4, h5.le, h5.ge]
  -- combine
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, hG] at hsum
  have h1y : (1 : ℝ) / y ≤ (2 * Real.log ((y : ℝ) + 1) + 3) / y
      - (2 * Real.log ((y : ℝ) + 1) + 2) / y := by
    have : (2 * Real.log ((y : ℝ) + 1) + 3) / y
        - (2 * Real.log ((y : ℝ) + 1) + 2) / y = 1 / y := by
      ring
    linarith [this.ge]
  linarith [hsum, htail2, hb1, hb2, h1y]


end RHTower
