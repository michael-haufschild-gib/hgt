import GaloisForLFunctions.RHTower.MontgomeryAssemblyBounds

/-!
# The error ratios of the pair-correlation assembly at `x = T^α`

For fixed `0 < α < 1` and `x = T^α`, the three error terms of the assembly of Montgomery's pair
form are `o` of the main term `(T/4) log x = (T/4) α log T`:

* the truncation error `131072 x (L² (3 log(1+T) + 2) + 64)`, `L = C + log(2T+5)`;
* the remainder energy `96x² + 3T (C' + log(T+4))²/x + 1536/x⁴`, against `T x log x`;
* the prime-side error `312 x² log x`, against `T x log x`.

All three reduce to `(log T)^r / T^{s} → 0` for `s > 0`.
-/

open Filter Topology Asymptotics

namespace RHTower

/-- `(log T)^n / T^s → 0` for `s > 0`. -/
theorem tendsto_log_pow_div_rpow (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun T : ℝ => Real.log T ^ n / T ^ s) atTop (𝓝 0) := by
  have := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).tendsto_div_nhds_zero
  refine this.congr fun T => ?_
  simp only [Real.rpow_natCast]

/-- `T^α / T → 0` for `α < 1`. -/
theorem tendsto_rpow_div_self {α : ℝ} (hα : α < 1) :
    Tendsto (fun T : ℝ => T ^ α / T) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [show -(1 - α) = α - 1 by ring, Real.rpow_sub hT, Real.rpow_one]

/-- Eventually `log T ≥ 1`, `log(2T+5) ≤ 2 log T`, `log(1+T) ≤ 2 log T`, `log(T+4) ≤ 2 log T`. -/
theorem eventually_log_bounds :
    ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T ∧ Real.log (2 * T + 5) ≤ 2 * Real.log T ∧
      Real.log (1 + T) ≤ 2 * Real.log T ∧ Real.log (T + 4) ≤ 2 * Real.log T := by
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ T by
      linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at this
  have hsq : Real.log (T ^ 2) = 2 * Real.log T := by
    rw [Real.log_pow]; push_cast; ring
  refine ⟨hlog1, ?_, ?_, ?_⟩
  · rw [← hsq]; exact Real.log_le_log (by linarith) (by nlinarith)
  · rw [← hsq]; exact Real.log_le_log (by linarith) (by nlinarith)
  · rw [← hsq]; exact Real.log_le_log (by linarith) (by nlinarith)

/-- **The truncation error is `o` of the main term.** -/
theorem tendsto_truncation_error_div {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun T : ℝ => 131072 * T ^ α *
        ((C + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
        / ((T / 4) * (α * Real.log T))) atTop (𝓝 0) := by
  -- dominating function `K (log T)^2 / T^{1-α}`
  set K : ℝ := 524288 / α * (8 * (C + 2) ^ 2 + 64) with hK
  have hK0 : 0 ≤ K := by positivity
  have hdom := (tendsto_log_pow_div_rpow 2 (s := 1 - α) (by linarith)).const_mul K
  rw [mul_zero] at hdom
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdom ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hT0 : 0 < T := by linarith
    have : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (2 * T + 5) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_log_bounds, eventually_gt_atTop (1 : ℝ)] with T hb hT
    obtain ⟨h1, h2, h3, _⟩ := hb
    have hT0 : 0 < T := by linarith
    have hlog : 0 < Real.log T := by linarith
    have hxpos : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
    -- numerator bound
    have hL : C + Real.log (2 * T + 5) ≤ (C + 2) * Real.log T := by nlinarith
    have hL0 : 0 ≤ C + Real.log (2 * T + 5) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T + 5); linarith
    have hLsq : (C + Real.log (2 * T + 5)) ^ 2 ≤ (C + 2) ^ 2 * Real.log T ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hL0 hL 2
    have h3' : 3 * Real.log (1 + T) + 2 ≤ 8 * Real.log T := by nlinarith
    have h3'0 : 0 ≤ 3 * Real.log (1 + T) + 2 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T); linarith
    have h64 : (64 : ℝ) ≤ 64 * Real.log T ^ 3 := by
      have : 1 ≤ Real.log T ^ 3 := one_le_pow₀ h1
      linarith
    have hnum : (C + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64
        ≤ (8 * (C + 2) ^ 2 + 64) * Real.log T ^ 3 := by
      have := mul_le_mul hLsq h3' h3'0 (by positivity)
      nlinarith
    -- the ratio
    rw [div_le_iff₀ (by positivity)]
    have hRHS : K * (Real.log T ^ 2 / T ^ (1 - α)) * (T / 4 * (α * Real.log T))
        = K * (α / 4) * (T ^ α * Real.log T ^ 3) := by
      rw [Real.rpow_sub hT0, Real.rpow_one]
      field_simp
    refine le_of_le_of_eq ?_ hRHS.symm
    rw [hK]
    calc 131072 * T ^ α * ((C + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
        ≤ 131072 * T ^ α * ((8 * (C + 2) ^ 2 + 64) * Real.log T ^ 3) := by gcongr
      _ = 524288 / α * (8 * (C + 2) ^ 2 + 64) * (α / 4) * (T ^ α * Real.log T ^ 3) := by
          field_simp; ring

/-- **The remainder energy is `o` of `T x log x`.** -/
theorem tendsto_remainder_energy_div {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun T : ℝ => (96 * (T ^ α) ^ 2 + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α
        + 1536 / (T ^ α) ^ 4) / (T * T ^ α * (α * Real.log T))) atTop (𝓝 0) := by
  -- three dominating terms
  have h1 : Tendsto (fun T : ℝ => 96 * (T ^ α / T)) atTop (𝓝 0) := by
    have := (tendsto_rpow_div_self hα1).const_mul 96; rwa [mul_zero] at this
  have h2 : Tendsto (fun T : ℝ => (3 * (C + 2) ^ 2 / α) * (Real.log T ^ 2 / T ^ (2 * α)))
      atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow 2 (s := 2 * α) (by linarith)).const_mul (3 * (C + 2) ^ 2 / α)
    rwa [mul_zero] at this
  have h3 : Tendsto (fun T : ℝ => 1536 * T⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul (1536 : ℝ); rwa [mul_zero] at this
  have hsum := (h1.add h2).add h3
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hT0 : 0 < T := by linarith
    have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    positivity
  · have hαlog : ∀ᶠ T : ℝ in atTop, 1 ≤ α * Real.log T :=
      (Real.tendsto_log_atTop.const_mul_atTop hα0).eventually_ge_atTop 1
    filter_upwards [eventually_log_bounds, eventually_gt_atTop (1 : ℝ), hαlog] with T hb hT hαl
    obtain ⟨hl1, _, _, h4⟩ := hb
    have hT0 : 0 < T := by linarith
    have hlog : 0 < Real.log T := by linarith
    have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT.le hα0.le
    have hden : 0 < T * T ^ α * (α * Real.log T) := by positivity
    -- bound the three pieces separately
    have hA : 96 * (T ^ α) ^ 2 / (T * T ^ α * (α * Real.log T)) ≤ 96 * (T ^ α / T) := by
      rw [div_le_iff₀ hden]
      have : 96 * (T ^ α / T) * (T * T ^ α * (α * Real.log T))
          = 96 * (T ^ α) ^ 2 * (α * Real.log T) := by field_simp
      rw [this]
      nlinarith [sq_nonneg (T ^ α)]
    have hB : 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α / (T * T ^ α * (α * Real.log T))
        ≤ (3 * (C + 2) ^ 2 / α) * (Real.log T ^ 2 / T ^ (2 * α)) := by
      have hL : C + Real.log (T + 4) ≤ (C + 2) * Real.log T := by nlinarith
      have hL0 : 0 ≤ C + Real.log (T + 4) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 4); linarith
      have hLsq : (C + Real.log (T + 4)) ^ 2 ≤ (C + 2) ^ 2 * Real.log T ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hL0 hL 2
      have hx2 : T ^ (2 * α) = (T ^ α) ^ 2 := by
        rw [mul_comm, Real.rpow_mul hT0.le]; norm_cast
      rw [hx2, div_div, div_le_iff₀ (by positivity)]
      have : 3 * (C + 2) ^ 2 / α * (Real.log T ^ 2 / (T ^ α) ^ 2)
          * (T ^ α * (T * T ^ α * (α * Real.log T)))
          = 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) * Real.log T := by
        field_simp
      rw [this]
      calc 3 * T * (C + Real.log (T + 4)) ^ 2 ≤ 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) := by
            gcongr
        _ = 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) * 1 := (mul_one _).symm
        _ ≤ 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) * Real.log T := by gcongr
    have hCc : 1536 / (T ^ α) ^ 4 / (T * T ^ α * (α * Real.log T)) ≤ 1536 * T⁻¹ := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have hx5 : 1 ≤ (T ^ α) ^ 4 * T ^ α := by
        have : 1 ≤ (T ^ α) ^ 4 := one_le_pow₀ hx1
        nlinarith
      have : 1536 * T⁻¹ * ((T ^ α) ^ 4 * (T * T ^ α * (α * Real.log T)))
          = 1536 * (((T ^ α) ^ 4 * T ^ α) * (α * Real.log T)) := by field_simp
      rw [this]
      nlinarith
    calc (96 * (T ^ α) ^ 2 + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α + 1536 / (T ^ α) ^ 4)
          / (T * T ^ α * (α * Real.log T))
        = 96 * (T ^ α) ^ 2 / (T * T ^ α * (α * Real.log T))
          + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α / (T * T ^ α * (α * Real.log T))
          + 1536 / (T ^ α) ^ 4 / (T * T ^ α * (α * Real.log T)) := by
          rw [add_div, add_div]
      _ ≤ 96 * (T ^ α / T) + (3 * (C + 2) ^ 2 / α) * (Real.log T ^ 2 / T ^ (2 * α)) + 1536 * T⁻¹ :=
          add_le_add (add_le_add hA hB) hCc

/-- **The prime-side error is `o` of `T x log x`**: `312 x² log x / (T x log x) = 312 x/T → 0`. -/
theorem tendsto_prime_error_div {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun T : ℝ => 312 * (T ^ α / T)) atTop (𝓝 0) := by
  have := (tendsto_rpow_div_self hα1).const_mul 312; rwa [mul_zero] at this

end RHTower
