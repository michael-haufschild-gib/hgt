import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vanishing integral of a derivative on the whole real line
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

theorem integral_derivative_eq_zero_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E}
    (hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hint : Integrable f')
    (htop : Tendsto f atTop (nhds 0))
    (hbot : Tendsto f atBot (nhds 0)) :
    (∫ x : ℝ, f' x) = 0 := by
  have hfinite : ∀ T : ℝ,
      (∫ x in (-T)..T, f' x) = f T - f (-T) := by
    intro T
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint.intervalIntegrable
  have hintegral : Tendsto (fun T : ℝ => ∫ x in (-T)..T, f' x)
      atTop (nhds (∫ x : ℝ, f' x)) := by
    simpa only [id_eq] using intervalIntegral_tendsto_integral hint
      tendsto_neg_atTop_atBot tendsto_id
  have hboundary : Tendsto (fun T : ℝ => f T - f (-T)) atTop (nhds 0) := by
    simpa using htop.sub (hbot.comp tendsto_neg_atTop_atBot)
  have heq : (fun T : ℝ => ∫ x in (-T)..T, f' x) =
      fun T : ℝ => f T - f (-T) := by
    funext T
    exact hfinite T
  rw [heq] at hintegral
  exact tendsto_nhds_unique hintegral hboundary

end GaloisForLFunctions.HTGeometry
