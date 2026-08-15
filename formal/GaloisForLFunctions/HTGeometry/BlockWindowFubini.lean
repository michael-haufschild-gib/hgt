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

/-- **Fubini with a product majorant.**  A jointly measurable integrand dominated by a product of
integrable profiles, one in each variable, may be integrated in either order. -/
theorem integral_swap_of_dominated_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {F : α → β → X} {w₁ : α → ℝ} {w₂ : β → ℝ}
    (hw₁ : Integrable w₁ μ) (hw₂ : Integrable w₂ ν)
    (hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hbound : ∀ᵐ p ∂(μ.prod ν), ‖Function.uncurry F p‖ ≤ w₁ p.1 * w₂ p.2) :
    (∫ a, ∫ b, F a b ∂ν ∂μ) = ∫ b, ∫ a, F a b ∂μ ∂ν :=
  MeasureTheory.integral_integral_swap (Integrable.mono' (hw₁.mul_prod hw₂) hmeas hbound)

/-- **Fubini on a block-times-window box with a dominating profile.** -/
theorem integral_swap_block_of_dominated {F : ℝ → ℝ → X} {s : Set ℝ}
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → X} (hg : IntegrableOn g s) {M : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict s).prod (volume.restrict (Ioc a b))))
    (hbound : ∀ᵐ p ∂((volume.restrict s).prod (volume.restrict (Ioc a b))),
      ‖Function.uncurry F p‖ ≤ M * ‖g p.1‖) :
    (∫ L in s, ∫ t in a..b, F L t) = ∫ t in a..b, ∫ L in s, F L t := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
  have hw₁ : Integrable (fun L : ℝ => M * ‖g L‖) (volume.restrict s) := hg.norm.const_mul M
  have hw₂ : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc a b)) := integrable_const 1
  have hb' : ∀ᵐ p ∂((volume.restrict s).prod (volume.restrict (Ioc a b))),
      ‖Function.uncurry F p‖ ≤ (M * ‖g p.1‖) * (1 : ℝ) := by
    filter_upwards [hbound] with p hp
    simpa using hp
  have hswap := integral_swap_of_dominated_prod hw₁ hw₂ hmeas hb'
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact hswap

/-- **Fubini on a block times the positive ray**, with a product majorant: an integrable profile on
the block and an integrable weight on the ray. -/
theorem integral_swap_block_ray_of_dominated {F : ℝ → ℝ → X} {s : Set ℝ}
    {w₁ w₂ : ℝ → ℝ} (hw₁ : IntegrableOn w₁ s) (hw₂ : IntegrableOn w₂ (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict s).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hbound : ∀ᵐ p ∂((volume.restrict s).prod (volume.restrict (Ioi (0 : ℝ)))),
      ‖Function.uncurry F p‖ ≤ w₁ p.1 * w₂ p.2) :
    (∫ L in s, ∫ r in Ioi (0 : ℝ), F L r) = ∫ r in Ioi (0 : ℝ), ∫ L in s, F L r :=
  integral_swap_of_dominated_prod hw₁ hw₂ hmeas hbound

end GaloisForLFunctions.HTGeometry
