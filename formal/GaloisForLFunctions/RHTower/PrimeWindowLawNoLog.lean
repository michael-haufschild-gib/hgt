import GaloisForLFunctions.RHTower.PrimeWindowLaw

/-!
# The prime window law without the logarithmic weight

The prime measure carries the logarithmic weight `log p`; removing it costs exactly one factor of
`log Y`:

```text
(log Y) · Y^(-a) ∑_{2 < p ≤ Y} p^(a-1) (log Y - log p)^j  →  j!/a^(j+1).
```

The exact identity `log p = log Y - (log Y - log p)` gives
`S_j = (log Y) N_j - N_{j+1}` for the weighted sum `S_j` and the unweighted sum `N_j`, so the
statement reduces to `N_j = o(Y^a)`.  That is proved by splitting the primes at `√Y`: above the
split `1 ≤ (2/log Y) log p`, so the block is `O(Y^a/log Y)`; below the split the window power is
at most `(log Y)^j` and the prime mass is `O(Y^(a/2))`.
-/

open Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

/-- The prime window sum without the logarithmic weight. -/
def primeWindowSumNoLog (a : ℝ) (j : ℕ) (Y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
    (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j else 0)

/-- Removing the logarithmic weight: `S_j = (log Y) N_j - N_{j+1}`. -/
theorem primeWindowSum_eq (a : ℝ) (j : ℕ) (Y : ℝ) :
    primeWindowSum a j Y
      = Real.log Y * primeWindowSumNoLog a j Y - primeWindowSumNoLog a (j + 1) Y := by
  unfold primeWindowSum primeWindowSumNoLog
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp, if_pos hp]
    have hw : (Real.log Y - Real.log k) ^ (j + 1)
        = (Real.log Y - Real.log k) ^ j * (Real.log Y - Real.log k) := by ring
    rw [hw]
    ring
  · rw [if_neg hp, if_neg hp, if_neg hp]
    ring

theorem primeWindowSumNoLog_nonneg (a : ℝ) (j : ℕ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ primeWindowSumNoLog a j Y := by
  refine Finset.sum_nonneg fun k hk => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp]
    rw [Finset.mem_Ioc] at hk
    have hk2 : 2 < k := hk.1
    have hkY : (k : ℝ) ≤ Y := by
      have h := hk.2
      have := Nat.floor_le hY.le
      calc (k : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h
        _ ≤ Y := this
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := by omega
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) := Real.rpow_nonneg hk0.le _
    have h2 : (0 : ℝ) ≤ Real.log Y - Real.log k := by
      have := Real.log_le_log hk0 hkY
      linarith
    exact mul_nonneg h1 (pow_nonneg h2 j)
  · rw [if_neg hp]

/-- The unweighted window sum is `o(Y^a)`: the primes above `√Y` gain a factor `2/log Y`, the
primes below contribute the mass of a square-root window. -/
theorem tendsto_primeWindowSumNoLog {a : ℝ} (ha0 : 0 < a) (j : ℕ) :
    Tendsto (fun Y : ℝ => primeWindowSumNoLog a j Y / Y ^ a) atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the two majorants
  have hS := tendsto_primeWindowSum ha0 j
  have hsqrtTop : Tendsto (fun Y : ℝ => Real.sqrt Y) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨b ^ 2 + 1, fun Y hY => ?_⟩
    have hb : b ≤ Real.sqrt (b ^ 2 + 1) := by
      have h1 : b ≤ |b| := le_abs_self b
      have h2 : |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      have h3 : Real.sqrt (b ^ 2) ≤ Real.sqrt (b ^ 2 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith [h2 ▸ h3]
    exact le_trans hb (Real.sqrt_le_sqrt hY)
  have hP : Tendsto (fun Y : ℝ => primeRpowLogSumIoc a (Real.sqrt Y) / Real.sqrt Y ^ a) atTop
      (nhds (1 / a)) := (tendsto_primeRpowLogSumIoc ha0).comp hsqrtTop
  have hhalf : Tendsto (fun Y : ℝ => (Real.log Y) ^ j / Y ^ (a / 2)) atTop (nhds 0) :=
    HTGeometry.tendsto_logPow_div_rpow (by positivity) j
  have hmajor : Tendsto (fun Y : ℝ =>
      2 / Real.log Y * (primeWindowSum a j Y / Y ^ a)
        + 1 / Real.log 2 * ((Real.log Y) ^ j / Y ^ (a / 2)) *
          (primeRpowLogSumIoc a (Real.sqrt Y) / Real.sqrt Y ^ a)) atTop (nhds 0) := by
    have h1 : Tendsto (fun Y : ℝ => 2 / Real.log Y) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 := h1.mul hS
    rw [zero_mul] at h2
    have h3 := (hhalf.const_mul (1 / Real.log 2)).mul hP
    rw [mul_zero, zero_mul] at h3
    have h4 := h2.add h3
    rwa [add_zero] at h4
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY a
    exact div_nonneg (primeWindowSumNoLog_nonneg a j hY) hYa.le
  · filter_upwards [eventually_ge_atTop (16 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hY1 : (1 : ℝ) ≤ Y := by linarith
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    have hlogY : Real.log 16 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    have hlogY0 : (0 : ℝ) < Real.log Y := by
      have : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
      linarith
    set m : ℕ := ⌊Real.sqrt Y⌋₊ with hm
    have hsq4 : (4 : ℝ) ≤ Real.sqrt Y := by
      have h := Real.sqrt_le_sqrt hY
      rwa [show Real.sqrt 16 = 4 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have hsqY : Real.sqrt Y ≤ Y := by
      have h := Real.sqrt_le_sqrt (show Y ≤ Y * Y by nlinarith)
      rwa [Real.sqrt_mul_self hY0.le] at h
    have hm4 : 4 ≤ m := by
      have : (4 : ℕ) ≤ ⌊Real.sqrt Y⌋₊ := Nat.le_floor (by exact_mod_cast hsq4)
      exact this
    have hmfloor : m ≤ ⌊Y⌋₊ := Nat.floor_le_floor hsqY
    have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 := Real.log_sqrt hY0.le
    -- split the prime window at the square root
    have hsplit := Finset.sum_Ioc_consecutive
      (fun k : ℕ => (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j
        else 0)) (show 2 ≤ m by omega) hmfloor
    -- upper block
    have hupper : ∑ k ∈ Finset.Ioc m ⌊Y⌋₊,
        (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j else 0)
        ≤ 2 / Real.log Y * primeWindowSum a j Y := by
      rw [primeWindowSum, Finset.mul_sum]
      have hsub : Finset.Ioc m ⌊Y⌋₊ ⊆ Finset.Ioc 2 ⌊Y⌋₊ :=
        Finset.Ioc_subset_Ioc_left (by omega)
      have hterm : ∀ k ∈ Finset.Ioc m ⌊Y⌋₊,
          (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j else 0)
            ≤ 2 / Real.log Y *
              (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j *
                Real.log k else 0) := by
        intro k hk
        rw [Finset.mem_Ioc] at hk
        by_cases hp : k.Prime
        · rw [if_pos hp, if_pos hp]
          have hkm : m < k := hk.1
          have hkY : (k : ℝ) ≤ Y := by
            have h := hk.2
            have hfl := Nat.floor_le hY0.le
            calc (k : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h
              _ ≤ Y := hfl
          have hk0 : (0 : ℝ) < (k : ℝ) := by
            have : (0 : ℕ) < k := by omega
            exact_mod_cast this
          have hklarge : Real.sqrt Y < (k : ℝ) := by
            have h := Nat.lt_floor_add_one (Real.sqrt Y)
            have hkm' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkm
            calc Real.sqrt Y < (m : ℝ) + 1 := by rw [hm]; exact h
              _ ≤ (k : ℝ) := hkm'
          have hlogk : Real.log Y / 2 < Real.log k := by
            have h := Real.log_lt_log (by linarith [hsq4]) hklarge
            rwa [hlogsqrt] at h
          have hfac : (1 : ℝ) ≤ 2 / Real.log Y * Real.log k := by
            have hcoef : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
            have hone : 2 / Real.log Y * (Real.log Y / 2) = 1 := by
              field_simp
            have h3 := mul_le_mul_of_nonneg_left hlogk.le hcoef
            rwa [hone] at h3
          have hnn : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j := by
            have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) := Real.rpow_nonneg hk0.le _
            have h2 : (0 : ℝ) ≤ Real.log Y - Real.log k := by
              have := Real.log_le_log hk0 hkY
              linarith
            exact mul_nonneg h1 (pow_nonneg h2 j)
          calc (k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j
              = ((k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j) * 1 := by ring
            _ ≤ ((k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j) *
                (2 / Real.log Y * Real.log k) := by
                exact mul_le_mul_of_nonneg_left hfac hnn
            _ = 2 / Real.log Y *
                ((k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j * Real.log k) := by ring
        · rw [if_neg hp, if_neg hp, mul_zero]
      have hstep : ∑ k ∈ Finset.Ioc m ⌊Y⌋₊,
          (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j else 0)
          ≤ ∑ k ∈ Finset.Ioc m ⌊Y⌋₊, 2 / Real.log Y *
              (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j *
                Real.log k else 0) := Finset.sum_le_sum hterm
      refine le_trans hstep (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      intro k hk _
      by_cases hp : k.Prime
      · rw [if_pos hp]
        rw [Finset.mem_Ioc] at hk
        have hk2 : 2 < k := hk.1
        have hkY : (k : ℝ) ≤ Y := by
          have h := hk.2
          have hfl := Nat.floor_le hY0.le
          calc (k : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h
            _ ≤ Y := hfl
        have hk0 : (0 : ℝ) < (k : ℝ) := by
          have : (0 : ℕ) < k := by omega
          exact_mod_cast this
        have hlogk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by
          have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
          linarith)
        have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) := Real.rpow_nonneg hk0.le _
        have h2 : (0 : ℝ) ≤ Real.log Y - Real.log k := by
          have := Real.log_le_log hk0 hkY
          linarith
        have hnn : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j * Real.log k :=
          mul_nonneg (mul_nonneg h1 (pow_nonneg h2 j)) hlogk
        have hcoef : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
        exact mul_nonneg hcoef hnn
      · rw [if_neg hp, mul_zero]
    -- lower block
    have hlower : ∑ k ∈ Finset.Ioc 2 m,
        (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j else 0)
        ≤ 1 / Real.log 2 * (Real.log Y) ^ j * primeRpowLogSumIoc a (Real.sqrt Y) := by
      rw [primeRpowLogSumIoc, ← hm, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ioc] at hk
      by_cases hp : k.Prime
      · rw [if_pos hp, if_pos hp]
        have hk2 : 2 < k := hk.1
        have hkm : k ≤ m := hk.2
        have hk0 : (0 : ℝ) < (k : ℝ) := by
          have : (0 : ℕ) < k := by omega
          exact_mod_cast this
        have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
        have hkY : (k : ℝ) ≤ Y := by
          have hkm' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
          have hmsq : (m : ℝ) ≤ Real.sqrt Y := Nat.floor_le (Real.sqrt_nonneg Y)
          linarith [hsqY]
        have hlogk2 : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2R
        have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) := Real.rpow_nonneg hk0.le _
        have hw0 : (0 : ℝ) ≤ Real.log Y - Real.log k := by
          have := Real.log_le_log hk0 hkY
          linarith
        have hwle : Real.log Y - Real.log k ≤ Real.log Y := by
          have : (0 : ℝ) ≤ Real.log k := by linarith
          linarith
        have hpow : (Real.log Y - Real.log k) ^ j ≤ (Real.log Y) ^ j :=
          pow_le_pow_left₀ hw0 hwle j
        have hfac : (1 : ℝ) ≤ 1 / Real.log 2 * Real.log k := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          linarith
        calc (k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j
            ≤ (k : ℝ) ^ (a - 1) * (Real.log Y) ^ j :=
              mul_le_mul_of_nonneg_left hpow h1
          _ = ((k : ℝ) ^ (a - 1) * (Real.log Y) ^ j) * 1 := by ring
          _ ≤ ((k : ℝ) ^ (a - 1) * (Real.log Y) ^ j) * (1 / Real.log 2 * Real.log k) := by
              refine mul_le_mul_of_nonneg_left hfac ?_
              have : (0 : ℝ) ≤ (Real.log Y) ^ j := pow_nonneg hlogY0.le j
              exact mul_nonneg h1 this
          _ = 1 / Real.log 2 * (Real.log Y) ^ j * ((k : ℝ) ^ (a - 1) * Real.log k) := by ring
      · rw [if_neg hp, if_neg hp, mul_zero]
    -- assemble
    have hsum : primeWindowSumNoLog a j Y
        ≤ 2 / Real.log Y * primeWindowSum a j Y
          + 1 / Real.log 2 * (Real.log Y) ^ j * primeRpowLogSumIoc a (Real.sqrt Y) := by
      rw [primeWindowSumNoLog, ← hsplit]
      linarith
    have hsqrtpos : (0 : ℝ) < Real.sqrt Y := by linarith [hsq4]
    have hsqa : (0 : ℝ) < Real.sqrt Y ^ a := Real.rpow_pos_of_pos hsqrtpos a
    have hYhalf : (0 : ℝ) < Y ^ (a / 2) := Real.rpow_pos_of_pos hY0 (a / 2)
    have hprod : Real.sqrt Y ^ a = Y ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hY0.le]
      congr 1
      ring
    have hdiv : primeWindowSumNoLog a j Y / Y ^ a
        ≤ (2 / Real.log Y * primeWindowSum a j Y
            + 1 / Real.log 2 * (Real.log Y) ^ j * primeRpowLogSumIoc a (Real.sqrt Y)) / Y ^ a := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hYa.le)
    have hexpand : (2 / Real.log Y * primeWindowSum a j Y
        + 1 / Real.log 2 * (Real.log Y) ^ j * primeRpowLogSumIoc a (Real.sqrt Y)) / Y ^ a
        = 2 / Real.log Y * (primeWindowSum a j Y / Y ^ a)
          + 1 / Real.log 2 * ((Real.log Y) ^ j / Y ^ (a / 2)) *
            (primeRpowLogSumIoc a (Real.sqrt Y) / Real.sqrt Y ^ a) := by
      have hYsplit : Y ^ (a / 2) * Y ^ (a / 2) = Y ^ a := by
        rw [← Real.rpow_add hY0]
        congr 1
        ring
      have hne : Y ^ (a / 2) ≠ 0 := ne_of_gt hYhalf
      rw [hprod, ← hYsplit]
      field_simp
    rw [hexpand] at hdiv
    exact hdiv

/-- **The prime window law without the logarithmic weight.** -/
theorem tendsto_logY_mul_primeWindowSumNoLog {a : ℝ} (ha0 : 0 < a) (j : ℕ) :
    Tendsto (fun Y : ℝ => Real.log Y * primeWindowSumNoLog a j Y / Y ^ a) atTop
      (nhds ((Nat.factorial j : ℝ) / a ^ (j + 1))) := by
  have hS := tendsto_primeWindowSum ha0 j
  have hN := tendsto_primeWindowSumNoLog ha0 (j + 1)
  have hsum := hS.add hN
  rw [add_zero] at hsum
  refine hsum.congr fun Y => ?_
  rw [primeWindowSum_eq a j Y]
  ring

end

end RHTower
