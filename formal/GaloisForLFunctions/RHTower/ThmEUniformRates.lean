import Zeta23.Defs
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary rates for the uniform Theorem E

All error terms of the modulus-uniform rank–trace certificate are controlled by three facts:

* `(log T)^k T^s → 0` for every `k` and `s < 0` (`tendsto_log_pow_mul_rpow`);
* `(log log T)² / log T → 0` (`tendsto_loglog_sq_div_log`);
* `l(T) = log(T/2π)` lies between `log T/2` and `log T` for `T ≥ 4π²` (`eventually_l_bounds`).

From these, for fixed `λ ∈ (0, 1)`, `A ≥ 0` and constants, every term of the error budget is eventually
below its share (`eventually_rate_*`).  None of the statements involves the modulus.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-- `(log T)^k T^s → 0` for `s < 0`. -/
theorem tendsto_log_pow_mul_rpow (k : ℕ) {s : ℝ} (hs : s < 0) :
    Tendsto (fun T : ℝ => Real.log T ^ k * T ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (neg_pos.mpr hs)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.rpow_natCast, Real.rpow_neg hT.le, div_inv_eq_mul]

/-- `(log log T)² (log T)⁻¹ → 0`. -/
theorem tendsto_loglog_sq_div_log :
    Tendsto (fun T : ℝ => Real.log (Real.log T) ^ 2 * Real.log T ^ (-1 : ℝ)) atTop (𝓝 0) :=
  (tendsto_log_pow_mul_rpow 2 (by norm_num : (-1 : ℝ) < 0)).comp Real.tendsto_log_atTop

/-- For large `T`: `log T ≥ 1`, `1 ≤ l`, `log T/2 ≤ l ≤ log T`. -/
theorem eventually_l_bounds :
    ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T ∧ 1 ≤ Zeta23.l T ∧ Real.log T / 2 ≤ Zeta23.l T
      ∧ Zeta23.l T ≤ Real.log T := by
  have h2π : 0 < Real.log (2 * π) := Real.log_pos (by linarith [Real.pi_gt_three])
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log (2 * π) + 2),
    eventually_gt_atTop 0] with T hT hT0
  have hl : Zeta23.l T = Real.log T - Real.log (2 * π) := by
    unfold Zeta23.l; rw [Real.log_div hT0.ne' (by positivity)]
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> rw [hl] <;> linarith

/-- `√(e^{λ l}) ≤ T^{λ/2}`. -/
theorem sqrt_exp_lam_l_le {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T) (hl : Zeta23.l T ≤ Real.log T) :
    Real.sqrt (Real.exp (lam * Zeta23.l T)) ≤ T ^ (lam / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul, Real.rpow_def_of_pos hT]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- `e^{λ l} ≤ T^λ`. -/
theorem exp_lam_l_le {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T) (hl : Zeta23.l T ≤ Real.log T) :
    Real.exp (lam * Zeta23.l T) ≤ T ^ lam := by
  rw [Real.rpow_def_of_pos hT]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **A generic rate.**  `K (log T)^k T^s ≤ c T` eventually, for `s < 1`, `c > 0`. -/
theorem eventually_log_pow_rpow_le (k : ℕ) {s : ℝ} (hs : s < 1) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, K * Real.log T ^ k * T ^ s ≤ c * T := by
  have h := (tendsto_log_pow_mul_rpow k (by linarith : s - 1 < 0)).eventually_le_const
    (by positivity : (0:ℝ) < c / (K + 1))
  filter_upwards [h, eventually_gt_atTop 0] with T hT hT0
  have e : T ^ s = T ^ (s - 1) * T := by
    rw [← Real.rpow_add_one hT0.ne']; ring_nf
  rw [e]
  have hKK : K ≤ K + 1 := by linarith
  calc K * Real.log T ^ k * (T ^ (s - 1) * T) = K * (Real.log T ^ k * T ^ (s - 1)) * T := by ring
    _ ≤ (K + 1) * (c / (K + 1)) * T := by
        apply mul_le_mul_of_nonneg_right _ hT0.le
        rcases le_or_gt (Real.log T ^ k * T ^ (s - 1)) 0 with hneg | hpos
        · have : K * (Real.log T ^ k * T ^ (s - 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK hneg
          have : 0 ≤ (K + 1) * (c / (K + 1)) := by positivity
          linarith
        · exact mul_le_mul hKK hT hpos.le (by linarith)
    _ = c * T := by field_simp

/-- **A generic decay.**  `K (log T)^k T^s ≤ c` eventually, for `s < 0`, `c > 0`. -/
theorem eventually_log_pow_rpow_le_const (k : ℕ) {s : ℝ} (hs : s < 0) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 < c) : ∀ᶠ T : ℝ in atTop, K * Real.log T ^ k * T ^ s ≤ c := by
  have h := (tendsto_log_pow_mul_rpow k hs).eventually_le_const
    (by positivity : (0:ℝ) < c / (K + 1))
  filter_upwards [h] with T hT
  calc K * Real.log T ^ k * T ^ s = K * (Real.log T ^ k * T ^ s) := by ring
    _ ≤ (K + 1) * (c / (K + 1)) := by
        rcases le_or_gt (Real.log T ^ k * T ^ s) 0 with hneg | hpos
        · have : K * (Real.log T ^ k * T ^ s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK hneg
          have : 0 ≤ (K + 1) * (c / (K + 1)) := by positivity
          linarith
        · exact mul_le_mul (by linarith) hT hpos.le (by linarith)
    _ = c := by field_simp

/-- `log²(A log T + 8) ≤ c log T` eventually. -/
theorem eventually_log_sq_le {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, Real.log (A * Real.log T + 8) ^ 2 ≤ c * Real.log T := by
  have h1 := tendsto_loglog_sq_div_log.eventually_le_const (by positivity : (0:ℝ) < c / 4)
  have h2 : ∀ᶠ T : ℝ in atTop, 4 * Real.log (A + 8) ^ 2 ≤ c / 2 * Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (8 * Real.log (A + 8) ^ 2 / c) |>.mono
      fun T hT => by
        rw [div_le_iff₀ hc] at hT
        nlinarith
  filter_upwards [h1, h2, Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT1 hT2 hT3
  have hy0 : 0 < Real.log T := by linarith
  have hloglog0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hT3
  have hle : Real.log (A * Real.log T + 8) ≤ Real.log (A + 8) + Real.log (Real.log T) := by
    rw [← Real.log_mul (by positivity) hy0.ne']
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hpos : 0 ≤ Real.log (A * Real.log T + 8) := Real.log_nonneg (by nlinarith)
  have hsq : Real.log (A * Real.log T + 8) ^ 2
      ≤ 2 * Real.log (A + 8) ^ 2 + 2 * Real.log (Real.log T) ^ 2 := by
    have h := pow_le_pow_left₀ hpos hle 2
    nlinarith [sq_nonneg (Real.log (A + 8) - Real.log (Real.log T))]
  have hll : Real.log (Real.log T) ^ 2 ≤ c / 4 * Real.log T := by
    rw [Real.rpow_neg_one] at hT1
    rw [← div_le_iff₀ hy0]
    simpa [div_eq_mul_inv] using hT1
  have hcl := mul_pos hc hy0
  linarith

end RHTower
