import GaloisForLFunctions.HTGeometry.L2FamilyCongruence

/-! L² holomorphy on the actual measurable spatial domain. -/
open MeasureTheory Filter Set Topology Metric
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [MeasurableSpace A]

/-- Holomorphy and domination are needed only on the actual restricted spatial domain. -/
theorem differentiableAt_l2Family_restrict_of_cauchy_dominated (μ : Measure A) (S : Set A)
    (hS : MeasurableSet S) (F : ℂ → A → ℂ) (z : ℂ) (R : ℝ) (hR : 0 < R)
    (b : A → ℝ) (hb : MemLp b 2 (μ.restrict S))
    (hm : ∀ u ∈ ball z R, AEStronglyMeasurable (F u) (μ.restrict S))
    (hd : ∀ a ∈ S, DifferentiableOn ℂ (fun u => F u a) (ball z R))
    (hbound : ∀ a ∈ S, ∀ u ∈ ball z R, ‖F u a‖ ≤ b a) :
    DifferentiableAt ℂ (l2Family (μ.restrict S) F) z := by
  let G (u : ℂ) := S.indicator (F u)
  have he : l2Family (μ.restrict S) G = l2Family (μ.restrict S) F :=
    funext (fun u => l2Family_congr_ae _ _ _ u (indicator_ae_eq_restrict hS))
  rw [← he]
  apply differentiableAt_l2Family_of_cauchy_dominated (μ.restrict S) G z R hR (fun a => ‖b a‖) hb.norm
  · intro u hu
    exact (hm u hu).indicator hS
  · intro a
    by_cases ha : a ∈ S
    · have he : (fun u => G u a) = (fun u => F u a) := funext (fun _ => indicator_of_mem ha _)
      rw [he]
      exact hd a ha
    · have he : (fun u => G u a) = (fun _ : ℂ => (0:ℂ)) := funext (fun _ => indicator_of_notMem ha _)
      rw [he]
      exact differentiableOn_const 0
  · intro a u hu
    by_cases ha : a ∈ S
    · change ‖S.indicator _ a‖ ≤ _
      rw [indicator_of_mem ha]
      exact (hbound a ha u hu).trans (le_abs_self _)
    · change ‖S.indicator _ a‖ ≤ _
      rw [indicator_of_notMem ha,norm_zero]
      exact norm_nonneg _

end
end GaloisForLFunctions.HTGeometry
