import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Uniqueness of second-order jet coefficients

If `‖α + β z‖ ≤ C z²` for all `z` in a right neighbourhood of `0`, then `α = β = 0`: letting
`z → 0⁺` kills `α`, and dividing by `z` then kills `β`.  This is the uniqueness statement that
identifies the counterterm coefficients of an endpoint expansion.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology

/-- A quantity bounded by `C z² + K z` on `(0, b]` is zero. -/
theorem norm_eq_zero_of_le_mul_sq_add_mul {x : ℂ} {b C K : ℝ} (hb : 0 < b)
    (h : ∀ z ∈ Ioc (0:ℝ) b, ‖x‖ ≤ C * z ^ (2 : ℕ) + K * z) : x = 0 := by
  have hlim : Tendsto (fun z : ℝ => C * z ^ (2 : ℕ) + K * z) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ => C * z ^ (2 : ℕ) + K * z) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa using this
  have hle : ‖x‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [Ioc_mem_nhdsGT hb] with z hz
    exact h z hz
  exact norm_le_zero_iff.mp hle

/-- Second-order jet coefficients are unique. -/
theorem eq_zero_of_norm_add_mul_le_mul_sq {α β : ℂ} {b C : ℝ} (hb : 0 < b)
    (h : ∀ z ∈ Ioc (0:ℝ) b, ‖α + β * z‖ ≤ C * z ^ (2 : ℕ)) : α = 0 ∧ β = 0 := by
  have hα : α = 0 := by
    refine norm_eq_zero_of_le_mul_sq_add_mul (C := C) (K := ‖β‖) hb (fun z hz => ?_)
    have h1 := h z hz
    have h2 : ‖β * (z:ℂ)‖ = ‖β‖ * z := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hz.1.le]
    calc ‖α‖ = ‖(α + β * z) - β * z‖ := by ring_nf
      _ ≤ ‖α + β * z‖ + ‖β * (z:ℂ)‖ := norm_sub_le _ _
      _ ≤ C * z ^ (2 : ℕ) + ‖β‖ * z := by rw [h2]; linarith
  refine ⟨hα, ?_⟩
  subst hα
  refine norm_eq_zero_of_le_mul_sq_add_mul (C := 0) (K := C) hb (fun z hz => ?_)
  have h1 := h z hz
  rw [zero_add, norm_mul, Complex.norm_real, Real.norm_of_nonneg hz.1.le] at h1
  have hz0 : 0 < z := hz.1
  have : ‖β‖ * z ≤ C * z * z := by nlinarith [h1]
  have h3 : ‖β‖ ≤ C * z := le_of_mul_le_mul_right this hz0
  linarith

end GaloisForLFunctions.HTGeometry
