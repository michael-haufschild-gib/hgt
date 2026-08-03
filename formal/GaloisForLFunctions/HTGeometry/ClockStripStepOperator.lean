import GaloisForLFunctions.HTGeometry.ClockStripCauchyScale

/-!
# The step operator of the clock iteration in sup-norm form

The coefficient form of the scale carries the algebra estimate cleanly, but the iteration itself is
better run in the sup-norm form. The reason is the double integration: in a supremum norm the
estimate

`‖∫∫ F‖ ≤ ∫∫ ‖F‖`

is the pointwise monotonicity of the integral, whereas in an `ℓ¹` norm it is an exchange of a sum
and an integral. So the iterates are taken to be functions holomorphic on a strip, and the operator
is the honest differential operator

`w ↦ (w'' + V w)/4`.

Its estimate in the scale is Cauchy's estimate for the second derivative together with the trivial
product bound: it maps radius `ρ'` to radius `ρ` with norm at most `4/(ρ'-ρ)² + ‖V‖/4`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

/-- The right-hand side of the characteristic clock equation, on a strip. -/
noncomputable def clockStripStep (V w : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (deriv (deriv w) z + V z * w z) / 4

/-- **The step operator preserves holomorphy.** -/
theorem differentiableOn_clockStripStep {ρ : ℝ} {V w : ℂ → ℂ}
    (hV : DifferentiableOn ℂ V (imStrip ρ)) (hw : DifferentiableOn ℂ w (imStrip ρ)) :
    DifferentiableOn ℂ (clockStripStep V w) (imStrip ρ) := by
  have hopen := isOpen_imStrip ρ
  have hana : AnalyticOnNhd ℂ w (imStrip ρ) := hw.analyticOnNhd hopen
  have hd1 : AnalyticOnNhd ℂ (deriv w) (imStrip ρ) := hana.deriv_of_isOpen hopen
  have hd2 : AnalyticOnNhd ℂ (deriv (deriv w)) (imStrip ρ) := hd1.deriv_of_isOpen hopen
  exact ((hd2.differentiableOn.add (hV.mul hw)).div_const 4)

/-- **The estimate of the step operator in the scale.** Two derivatives cost two powers of the gap;
the potential contributes its supremum. -/
theorem norm_clockStripStep_le {ρ ρ' Mv Mw : ℝ} (hρ : ρ < ρ') (hMv0 : 0 ≤ Mv)
    {V w : ℂ → ℂ} (hw : DifferentiableOn ℂ w (imStrip ρ'))
    (hMw : ∀ z ∈ imStrip ρ', ‖w z‖ ≤ Mw) (hMv : ∀ z ∈ imStrip ρ', ‖V z‖ ≤ Mv)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖clockStripStep V w z‖ ≤ (4 / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := by
  have hgap : (0 : ℝ) < ρ' - ρ := by linarith
  have hzmem : z ∈ imStrip ρ' := lt_of_le_of_lt hz hρ
  have hsecond : ‖deriv (deriv w) z‖ ≤ 16 * Mw / (ρ' - ρ) ^ 2 :=
    norm_deriv_deriv_le_on_imStrip hρ hw hMw hz
  have hpot : ‖V z * w z‖ ≤ Mv * Mw := by
    rw [norm_mul]
    exact mul_le_mul (hMv z hzmem) (hMw z hzmem) (norm_nonneg _) hMv0
  have htri : ‖deriv (deriv w) z + V z * w z‖ ≤ 16 * Mw / (ρ' - ρ) ^ 2 + Mv * Mw :=
    le_trans (norm_add_le _ _) (add_le_add hsecond hpot)
  have hdiv : ‖clockStripStep V w z‖
      = ‖deriv (deriv w) z + V z * w z‖ / 4 := by
    rw [clockStripStep, norm_div]
    norm_num
  rw [hdiv]
  have hfinal : (16 * Mw / (ρ' - ρ) ^ 2 + Mv * Mw) / 4
      = (4 / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := by
    field_simp
    ring
  calc ‖deriv (deriv w) z + V z * w z‖ / 4
      ≤ (16 * Mw / (ρ' - ρ) ^ 2 + Mv * Mw) / 4 := by linarith
    _ = (4 / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := hfinal

end GaloisForLFunctions.HTGeometry
