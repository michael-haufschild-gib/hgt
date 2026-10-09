import GaloisForLFunctions.RHTower.XiFiniteCriticalFactorRigidity
import GaloisForLFunctions.HTGeometry.LogarithmicTractGrowth

open GaloisForLFunctions.HTGeometry Set

namespace RHTower

/-- Actual Xi cannot factor through an entire function with finitely many critical values and
an injective inverse logarithmic chart. -/
theorem xi_ne_comp_of_finite_critical_values_logarithmic_chart
    {F g φ : ℂ → ℂ} {a : ℂ}
    (hF : Differentiable ℂ F) (hg : Differentiable ℂ g)
    (hcrit : (F '' {z | deriv F z = 0}).Finite)
    (hφ : DifferentiableOn ℂ φ {z | 0 < z.re}) (hinj : InjOn φ {z | 0 < z.re})
    (homit : ∀ z : ℂ, 0 < z.re → φ z ≠ a)
    (hvalue : ∀ x : ℝ, 0 < x → Real.exp x ≤ ‖F (φ (x : ℂ))‖) :
    xi ≠ fun z => F (g z) :=
  xi_ne_comp_of_positiveLowerOrder_finite_critical_values hF hg
    (positiveLowerOrder_of_univalent_logarithmic_chart hφ hinj homit hvalue) hcrit

/-- There is no finite-critical-value entire factorization of Xi admitting such a chart. -/
theorem not_exists_xi_finite_critical_logarithmic_factor :
    ¬ ∃ (F g φ : ℂ → ℂ) (a : ℂ),
      Differentiable ℂ F ∧ Differentiable ℂ g ∧
      (F '' {z | deriv F z = 0}).Finite ∧
      DifferentiableOn ℂ φ {z | 0 < z.re} ∧ InjOn φ {z | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → φ z ≠ a) ∧
      (∀ x : ℝ, 0 < x → Real.exp x ≤ ‖F (φ (x : ℂ))‖) ∧
      (∀ z : ℂ, xi z = F (g z)) := by
  rintro ⟨F, g, φ, a, hF, hg, hcrit, hφ, hinj, homit, hvalue, heq⟩
  exact xi_ne_comp_of_finite_critical_values_logarithmic_chart
    hF hg hcrit hφ hinj homit hvalue (funext heq)

end RHTower
