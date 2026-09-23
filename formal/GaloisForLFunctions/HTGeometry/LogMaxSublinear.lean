import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Logarithms of a growing maximum are sublinear

A logarithm divided by its argument tends to zero, and taking the maximum with a fixed positive
constant or multiplying the argument by one changes nothing: for large arguments the maximum is the
growing branch and the constant contributes an additive logarithm.

The same holds after the quantity is fed through a square root against a fixed quadratic and an
additive constant, since the root of a sum is below the sum of the roots.  This is the shape a
bound built from a layer logarithm and a tail constant takes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

/-- A logarithm divided by its argument tends to zero. -/
theorem tendsto_log_div_atTop : Tendsto (fun r : ℝ => Real.log r / r) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- The logarithm of a maximum with a growing branch is still sublinear. -/
theorem tendsto_log_max_div_atTop {A K : ℝ} (hK : 0 < K) :
    Tendsto (fun r : ℝ => Real.log (max A (K * r)) / r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => Real.log K / r) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id (Real.log K)
  have hlim : Tendsto (fun r : ℝ => Real.log K / r + Real.log r / r) atTop (𝓝 0) := by
    have := h1.add tendsto_log_div_atTop
    rwa [add_zero] at this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (A / K), eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hKr : A ≤ K * r := by
    rw [div_le_iff₀ hK] at hr
    linarith [hr]
  rw [max_eq_right hKr, Real.log_mul (ne_of_gt hK) (ne_of_gt hr0)]
  ring

/-- The larger of a fixed logarithm and the logarithm of a growing maximum is sublinear. -/
theorem tendsto_max_abs_log_div_atTop {A K : ℝ} (hK : 0 < K) :
    Tendsto (fun r : ℝ => max |Real.log A| |Real.log (max A (K * r))| / r) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun r : ℝ => (|Real.log A| + Real.log (max A (K * r))) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => |Real.log A| / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id _
    have h2 := h1.add (tendsto_log_max_div_atTop (A := A) hK)
    rw [add_zero] at h2
    exact h2.congr fun r => by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) hr.le
  · filter_upwards [eventually_ge_atTop (1 / K), eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hKr : (1 : ℝ) ≤ K * r := by
      rw [div_le_iff₀ hK] at hr
      linarith [hr]
    have hone : (1 : ℝ) ≤ max A (K * r) := le_trans hKr (le_max_right _ _)
    have hlognn : (0 : ℝ) ≤ Real.log (max A (K * r)) := Real.log_nonneg hone
    have habs : |Real.log (max A (K * r))| = Real.log (max A (K * r)) := abs_of_nonneg hlognn
    have hmax : max |Real.log A| |Real.log (max A (K * r))| ≤
        |Real.log A| + Real.log (max A (K * r)) := by
      rw [habs]
      exact max_le (le_add_of_nonneg_right hlognn) (le_add_of_nonneg_left (abs_nonneg _))
    gcongr

/-- A square root of a fixed quadratic in a sublinear quantity, plus a constant, is sublinear. -/
theorem tendsto_sqrt_sq_mul_add_div_atTop {f : ℝ → ℝ} (hf0 : ∀ r, 0 ≤ f r)
    (hf : Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0)) {W C : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) :
    Tendsto (fun r : ℝ => Real.sqrt (f r ^ (2 : ℕ) * W ^ (2 : ℕ) + C) / r) atTop (𝓝 0) := by
  have hupper : Tendsto (fun r : ℝ => (f r * W + Real.sqrt C) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => f r / r * W) atTop (𝓝 0) := by
      simpa using hf.mul_const W
    have h2 : Tendsto (fun r : ℝ => Real.sqrt C / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id _
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3.congr fun r => by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (Real.sqrt_nonneg _) hr.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hnn : (0 : ℝ) ≤ f r * W + Real.sqrt C := by
      have := mul_nonneg (hf0 r) hW
      linarith [Real.sqrt_nonneg C]
    have hkey : f r ^ (2 : ℕ) * W ^ (2 : ℕ) + C ≤ (f r * W + Real.sqrt C) ^ (2 : ℕ) := by
      have hsq := Real.sq_sqrt hC
      nlinarith [Real.sqrt_nonneg C, mul_nonneg (hf0 r) hW]
    have hsub : Real.sqrt (f r ^ (2 : ℕ) * W ^ (2 : ℕ) + C) ≤ f r * W + Real.sqrt C :=
      calc Real.sqrt (f r ^ (2 : ℕ) * W ^ (2 : ℕ) + C) ≤ Real.sqrt ((f r * W + Real.sqrt C) ^ (2 : ℕ)) :=
            Real.sqrt_le_sqrt hkey
        _ = f r * W + Real.sqrt C := Real.sqrt_sq hnn
    gcongr

end GaloisForLFunctions.HTGeometry
