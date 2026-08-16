import GaloisForLFunctions.HTGeometry.LogChartEnergyTransfer

/-!
# `(19)` in extended form, and the physical `H¹` conclusion `(8)`

The chart identity `∫‖∂_r u‖²dr = ∫e^{L}‖F′(L)‖²dL` is an equality of Bochner integrals, which by
itself says nothing about *finiteness*.  Stated for `ℝ≥0∞` it does: the change of variables carries
the extended mass verbatim, and then a weight `e^{2σL}` with `σ > 1/2` dominates the chart's own
`e^{L}` on the terminal ray.  So a weighted log-derivative in `L²` gives a spatial derivative in
`L²`, which is `(8)`.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The chart energy identity in extended form.** -/
theorem lintegral_sq_spatial_eq_lintegral_exp_weighted (F' : ℝ → X) (L₀ : ℝ) :
    (∫⁻ r in Ioo (0 : ℝ) (Real.exp (-L₀)), ‖(-r⁻¹) • F' (-Real.log r)‖ₑ ^ 2)
      = ∫⁻ L in Ioi L₀, ENNReal.ofReal (Real.exp L) * ‖F' L‖ₑ ^ 2 := by
  have hderiv : ∀ L ∈ Ioi L₀, HasDerivWithinAt logChart (-Real.exp (-L)) (Ioi L₀) L :=
    fun L _ => (hasDerivAt_logChart L).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv
    (injOn_logChart_Ioi L₀) (fun r => ‖(-r⁻¹) • F' (-Real.log r)‖ₑ ^ 2)
  rw [image_logChart_Ioi' L₀] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
  have hexp : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  have hlog : -Real.log (logChart L) = L := by
    rw [logChart, Real.log_exp, neg_neg]
  have hinv : (logChart L)⁻¹ = Real.exp L := by
    rw [logChart, ← Real.exp_neg, neg_neg]
  rw [abs_neg, abs_of_pos hexp, hlog]
  have hnorm : ‖(-(logChart L)⁻¹) • F' L‖ₑ ^ 2
      = ENNReal.ofReal (Real.exp L) ^ 2 * ‖F' L‖ₑ ^ 2 := by
    rw [enorm_smul, mul_pow]
    congr 2
    rw [hinv]
    rw [← ofReal_norm, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos L)]
  rw [hnorm, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **`(8)`: a weighted log derivative with exponent above `1/2` gives a spatial `L²`
derivative.** -/
theorem lintegral_sq_spatial_ne_top_of_weighted {F' : ℝ → X} {σ L₀ : ℝ}
    (hσ : 1 / 2 < σ) (hL₀ : 0 ≤ L₀)
    (hfin : (∫⁻ L in Ioi L₀, ‖Real.exp (σ * L) • F' L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ r in Ioo (0 : ℝ) (Real.exp (-L₀)), ‖(-r⁻¹) • F' (-Real.log r)‖ₑ ^ 2) ≠ ⊤ := by
  rw [lintegral_sq_spatial_eq_lintegral_exp_weighted]
  refine ne_top_of_le_ne_top hfin ?_
  refine setLIntegral_mono' measurableSet_Ioi fun L hL => ?_
  have hL0 : (0 : ℝ) ≤ L := le_trans hL₀ (le_of_lt hL)
  have hle : Real.exp L ≤ Real.exp (σ * L) * Real.exp (σ * L) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hσ, hL0]
  have hnorm : ‖Real.exp (σ * L) • F' L‖ₑ ^ 2
      = ENNReal.ofReal (Real.exp (σ * L) * Real.exp (σ * L)) * ‖F' L‖ₑ ^ 2 := by
    rw [enorm_smul, mul_pow, ← ofReal_norm, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le]
    congr 2
    ring
  rw [hnorm]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl

end GaloisForLFunctions.HTGeometry
