import GaloisForLFunctions.RHTower.XiCriticalValueAccumulation
import GaloisForLFunctions.HTGeometry.PositiveLowerOrderCompositionRigidity

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The corpus's order-one Xi bound supplies the finite-order composition envelope. -/
theorem finiteOrderEnvelope_xi : FiniteOrderEnvelope xi := by
  obtain ⟨C, hC, hbound⟩ := xi_growth_order_le_one
  refine ⟨C, 2, hC.le, fun z => (hbound z).trans (Real.exp_le_exp.2 ?_)⟩
  have hlog : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖z‖)
    linarith
  calc
    C * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ C * (1 + ‖z‖) * (1 + ‖z‖) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C * (1 + ‖z‖) ^ 2 := by ring

/-- Actual Xi has no entire left factor with positive lower order and finitely many critical
values, regardless of the entire inner function. -/
theorem xi_ne_comp_of_positiveLowerOrder_finite_critical_values
    {F g : ℂ → ℂ} (hF : Differentiable ℂ F) (hg : Differentiable ℂ g)
    (hpos : PositiveLowerOrder F) (hcrit : (F '' {z | deriv F z = 0}).Finite) :
    xi ≠ fun z => F (g z) := by
  intro heq
  have hcomp : FiniteOrderEnvelope (fun z => F (g z)) := heq ▸ finiteOrderEnvelope_xi
  obtain ⟨P, hP⟩ := exists_polynomial_inner_of_positiveLowerOrder_comp hF hg hpos hcomp
  apply xi_ne_comp_polynomial_of_finite_critical_values hF hcrit P
  exact heq.trans (funext fun z => congrArg F (hP z))

end RHTower
