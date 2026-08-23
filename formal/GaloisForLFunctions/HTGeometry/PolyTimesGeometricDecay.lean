import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# A polynomial times a geometric decay tends to zero

`(σ + M)^N · A^σ → 0` as `σ → ∞` for `0 < A < 1`: the elementary fact behind "a rational function
cannot decay exponentially".

## Main results

* `tendsto_poly_mul_rpow_atTop_nhds_zero`
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem tendsto_poly_mul_rpow_atTop_nhds_zero {A M : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (N : ℕ) :
    Tendsto (fun σ : ℝ => (σ + M) ^ N * A ^ σ) atTop (𝓝 0) := by
  set c : ℝ := -Real.log A with hcdef
  have hc0 : 0 < c := by
    rw [hcdef, neg_pos]
    exact Real.log_neg hA0 hA1
  -- the model limit
  have hmodel := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hlin : Tendsto (fun σ : ℝ => c * (σ + M)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hc0 ?_
    exact tendsto_atTop_add_const_right _ M tendsto_id
  have hcomp := hmodel.comp hlin
  have hscale := hcomp.const_mul ((c ^ N)⁻¹ * Real.exp (c * M))
  have hzero : ((c ^ N)⁻¹ * Real.exp (c * M)) * 0 = 0 := by ring
  rw [hzero] at hscale
  refine hscale.congr fun σ => ?_
  simp only [Function.comp_apply]
  have hArw : A ^ σ = Real.exp (-(c * σ)) := by
    rw [hcdef]
    rw [Real.rpow_def_of_pos hA0]
    ring_nf
  rw [hArw]
  have hexp : Real.exp (-(c * (σ + M))) = Real.exp (-(c * σ)) * Real.exp (-(c * M)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hpow : (c * (σ + M)) ^ N = c ^ N * (σ + M) ^ N := by rw [mul_pow]
  rw [hpow]
  have hcne : (c : ℝ) ^ N ≠ 0 := by positivity
  have hexpne : Real.exp (c * M) * Real.exp (-(c * M)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  linear_combination ((σ + M) ^ N) * hexpne

end GaloisForLFunctions.HTGeometry
