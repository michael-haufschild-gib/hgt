import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Summability from a nonzero polynomial-scale limit

A positive leading coefficient fixes the entire real-power summability
threshold, by limit comparison with the corresponding shifted p-series.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Asymptotics
open scoped Topology

theorem summable_rpow_iff_of_polynomial_limit {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {q L : ℝ} (hL : 0 < L)
    (hlim : Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ q * f n) atTop (𝓝 L)) (p : ℝ) :
    Summable (fun n => f n ^ p) ↔ 1 < q * p := by
  have hratio : Tendsto (fun n : ℕ => f n ^ p / (1 / (n + 1 : ℝ) ^ (q * p)))
      atTop (𝓝 (L ^ p)) := by
    convert! hlim.rpow_const (p := p) (Or.inl hL.ne') using 1
    funext n
    rw [one_div, div_inv_eq_mul, Real.mul_rpow (Real.rpow_nonneg (by positivity) q) (hf n),
      ← Real.rpow_mul (by positivity)]
    exact mul_comm _ _
  have htheta := isTheta_of_div_tendsto_nhds_ne_zero hratio
    (Real.rpow_pos_of_pos hL p).ne'
  have hseries : (Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ (q * p)) ↔ 1 < q * p := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (q * p)) 1).trans
        Real.summable_one_div_nat_rpow
  exact htheta.summable_iff_nat.symm.trans hseries

end GaloisForLFunctions.HTGeometry
