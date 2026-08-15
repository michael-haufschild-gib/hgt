import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exchanging a block integral with a frequency window

A vector-valued integrand on a physical block times a compact frequency window may be integrated in
either order as soon as it is jointly measurable and dominated by `M‖g(L)‖` — the profile being
integrable on the block and the window carrying finite measure.  No continuity in the block variable
is needed, which is exactly what the block estimate requires: the profile may be arbitrarily rough
inside its unit block, and only the frequency dependence is smooth.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Fubini on a block-times-window box with a dominating profile.** -/
theorem integral_swap_block_of_dominated {F : ℝ → ℝ → X} {s : Set ℝ}
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → X} (hg : IntegrableOn g s) {M : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict s).prod (volume.restrict (Ioc a b))))
    (hbound : ∀ᵐ p ∂((volume.restrict s).prod (volume.restrict (Ioc a b))),
      ‖Function.uncurry F p‖ ≤ M * ‖g p.1‖) :
    (∫ L in s, ∫ t in a..b, F L t) = ∫ t in a..b, ∫ L in s, F L t := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
  have hmaj : Integrable (fun p : ℝ × ℝ => M * ‖g p.1‖)
      ((volume.restrict s).prod (volume.restrict (Ioc a b))) := by
    have h1 : Integrable (fun L : ℝ => M * ‖g L‖) (volume.restrict s) := hg.norm.const_mul M
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc a b)) := integrable_const 1
    have := h1.mul_prod h2
    simpa using this
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict s).prod (volume.restrict (Ioc a b))) :=
    Integrable.mono' hmaj hmeas hbound
  have hswap := MeasureTheory.integral_integral_swap hint
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact hswap

end GaloisForLFunctions.HTGeometry
