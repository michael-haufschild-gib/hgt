import Mathlib

/-!
# Exponential moments of functions vanishing at the logarithms of the integers

The points `log n` become dense: consecutive ones are `log(1 + 1/n) ≤ 1/n` apart.  A function that
vanishes at every `log n` with `n ≥ N₀` and grows at most linearly away from each of these zeros
is therefore small on `[log N₀, ∞)` on the scale `e^{−y}`, which beats the weight `e^{y/2}`.

**Theorem** (`abs_intervalIntegral_mul_exp_half_le`).  Suppose that for every `n ≥ N₀ ≥ 2` and every
`y ∈ [log n, log(n + 1)]` we have `|g(y)| ≤ L (y − log n)`.  Then for every `K`
`|∫_{log N₀}^{log(N₀ + K)} g(y) e^{y/2} dy| ≤ √2 L / √(N₀ − 1)`.

Proof.  On `[log n, log(n+1)]`, `|g e^{y/2}| ≤ L √(n+1) (y − log n)`, whose integral is
`L √(n+1) (log(1 + 1/n))² / 2 ≤ L/(√2 n^{3/2})`.  Finally
`n^{−3/2} ≤ 2 (1/√(n−1) − 1/√n)` telescopes (`inv_mul_sqrt_le_two_mul_sub`).
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- `1/(m√m) ≤ 2(1/√(m−1) − 1/√m)` for `m > 1`. -/
theorem inv_mul_sqrt_le_two_mul_sub {m : ℝ} (hm : 1 < m) :
    1 / (m * Real.sqrt m) ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  set a := Real.sqrt (m - 1) with ha_def
  set b := Real.sqrt m with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = m - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = m := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hm' : m = b ^ 2 := hb2.symm
  rw [hm', div_le_iff₀ (by positivity)]
  have e : 2 * (1 / a - 1 / b) * (b ^ 2 * b) = 2 * (b - a) * b ^ 2 / a := by
    field_simp
  rw [e, le_div_iff₀ ha, one_mul]
  have h1 : (b - a) * (b + a) = 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab)) (by positivity :
    (0 : ℝ) ≤ 2 * b + a)]

/-- **Telescoping tail.**  `Σ_{k<K} 1/(n_k √n_k) ≤ 2/√(N₀ − 1)` with `n_k = N₀ + k`, `N₀ ≥ 2`. -/
theorem sum_inv_mul_sqrt_le {N₀ : ℕ} (hN : 2 ≤ N₀) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ)) ≤
      2 / Real.sqrt ((N₀ : ℝ) - 1) := by
  set F : ℕ → ℝ := fun k => 1 / Real.sqrt (((N₀ + k : ℕ) : ℝ) - 1) with hF
  have hterm : ∀ k, 1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ)) ≤
      2 * (F k - F (k + 1)) := by
    intro k
    have hm : (1 : ℝ) < ((N₀ + k : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((N₀ + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N₀ + k)
      linarith
    have h := inv_mul_sqrt_le_two_mul_sub hm
    have e : ((N₀ + (k + 1) : ℕ) : ℝ) - 1 = ((N₀ + k : ℕ) : ℝ) := by push_cast; ring
    simp only [hF, e]
    exact h
  calc ∑ k ∈ Finset.range K, 1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.range K, 2 * (F k - F (k + 1)) := Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * (F 0 - F K) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 2 * F 0 := by
        have : 0 ≤ F K := by simp only [hF]; positivity
        linarith
    _ = 2 / Real.sqrt ((N₀ : ℝ) - 1) := by simp only [hF, add_zero]; ring

/-- One interval: if `|g(y)| ≤ L (y − log n)` on `[log n, log(n+1)]` then
`|∫ g e^{y/2}| ≤ L/(√2 n√n)` there. -/
theorem abs_integral_log_interval_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : Continuous g)
    {n : ℕ} (hn : 1 ≤ n)
    (hlin : ∀ y ∈ Icc (Real.log n) (Real.log (n + 1)), |g y| ≤ L * (y - Real.log n)) :
    |∫ y in Real.log n..Real.log (n + 1), g y * Real.exp (y / 2)| ≤
      L / Real.sqrt 2 * (1 / ((n : ℝ) * Real.sqrt n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.log n with ha
  set b := Real.log (n + 1) with hb
  have hab : a ≤ b := Real.log_le_log hn0 (by linarith)
  have hba : b - a ≤ 1 / n := by
    rw [ha, hb, ← Real.log_div (by positivity) hn0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) / n by positivity)
    rw [show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at this
    exact this
  have hsq : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
  have hcont : Continuous fun y => g y * Real.exp (y / 2) := hg.mul (by fun_prop)
  have hbound : ∀ y ∈ Icc a b, |g y * Real.exp (y / 2)| ≤
      L * Real.sqrt ((n : ℝ) + 1) * (y - a) := by
    intro y hy
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (y / 2) ≤ Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.exp_half, hb] at *
      refine Real.sqrt_le_sqrt ?_
      calc Real.exp y ≤ Real.exp (Real.log (n + 1)) := Real.exp_le_exp.mpr hy.2
        _ = n + 1 := Real.exp_log (by positivity)
    have hya : 0 ≤ y - a := by linarith [hy.1]
    calc |g y| * Real.exp (y / 2) ≤ L * (y - a) * Real.sqrt ((n : ℝ) + 1) :=
          mul_le_mul (hlin y hy) hexp (Real.exp_pos _).le (by positivity)
      _ = L * Real.sqrt ((n : ℝ) + 1) * (y - a) := by ring
  have hint : ∫ y in a..b, L * Real.sqrt ((n : ℝ) + 1) * (y - a) =
      L * Real.sqrt ((n : ℝ) + 1) * ((b - a) ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) a, integral_id, sub_self]
    ring
  calc |∫ y in a..b, g y * Real.exp (y / 2)|
      ≤ ∫ y in a..b, |g y * Real.exp (y / 2)| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in a..b, L * Real.sqrt ((n : ℝ) + 1) * (y - a) :=
        intervalIntegral.integral_mono_on hab (hcont.abs.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun y => L * Real.sqrt ((n : ℝ) + 1) * (y - a)
            ).intervalIntegrable _ _) hbound
    _ = L * Real.sqrt ((n : ℝ) + 1) * ((b - a) ^ 2 / 2) := hint
    _ ≤ L * (Real.sqrt 2 * Real.sqrt n) * ((1 / n) ^ 2 / 2) := by
        have h0 : 0 ≤ b - a := by linarith
        gcongr
    _ = L / Real.sqrt 2 * (1 / ((n : ℝ) * Real.sqrt n)) := by
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hn2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
        field_simp
        rw [h2]
        nlinarith [hn2]

/-- **Exponential moment of a function vanishing at the logarithms of the integers.** -/
theorem abs_intervalIntegral_mul_exp_half_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : Continuous g)
    {N₀ : ℕ} (hN₀ : 2 ≤ N₀)
    (hlin : ∀ n : ℕ, N₀ ≤ n → ∀ y ∈ Icc (Real.log n) (Real.log (n + 1)),
      |g y| ≤ L * (y - Real.log n)) (K : ℕ) :
    |∫ y in Real.log N₀..Real.log ((N₀ + K : ℕ) : ℝ), g y * Real.exp (y / 2)| ≤
      Real.sqrt 2 * L / Real.sqrt ((N₀ : ℝ) - 1) := by
  have hcont : Continuous fun y => g y * Real.exp (y / 2) := hg.mul (by fun_prop)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun y => g y * Real.exp (y / 2)) (a := fun k => Real.log ((N₀ + k : ℕ) : ℝ)) (n := K)
    (fun k _ => hcont.intervalIntegrable _ _)
  simp only [add_zero] at hsum
  rw [← hsum]
  have hpiece : ∀ k ∈ Finset.range K,
      |∫ y in Real.log ((N₀ + k : ℕ) : ℝ)..Real.log ((N₀ + (k + 1) : ℕ) : ℝ),
        g y * Real.exp (y / 2)| ≤
      L / Real.sqrt 2 * (1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ))) := by
    intro k _
    have e : ((N₀ + (k + 1) : ℕ) : ℝ) = ((N₀ + k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e]
    exact abs_integral_log_interval_le hL hg (by omega) (hlin _ (by omega))
  calc |∑ k ∈ Finset.range K, ∫ y in Real.log ((N₀ + k : ℕ) : ℝ)..Real.log
        ((N₀ + (k + 1) : ℕ) : ℝ), g y * Real.exp (y / 2)|
      ≤ ∑ k ∈ Finset.range K, |∫ y in Real.log ((N₀ + k : ℕ) : ℝ)..Real.log
        ((N₀ + (k + 1) : ℕ) : ℝ), g y * Real.exp (y / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K,
        L / Real.sqrt 2 * (1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ))) :=
        Finset.sum_le_sum hpiece
    _ = L / Real.sqrt 2 * ∑ k ∈ Finset.range K,
        1 / (((N₀ + k : ℕ) : ℝ) * Real.sqrt ((N₀ + k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ L / Real.sqrt 2 * (2 / Real.sqrt ((N₀ : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le hN₀ K) (by positivity)
    _ = Real.sqrt 2 * L / Real.sqrt ((N₀ : ℝ) - 1) := by
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hs2 : 0 < Real.sqrt 2 := by positivity
        field_simp
        rw [h2]

end GaloisForLFunctions.HTGeometry
