import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Strong continuity of L² classes from pointwise continuity and a fixed square-integrable majorant. -/
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Dominated pointwise continuity gives continuity in the actual L² quotient. -/
theorem continuous_toLp_two_of_dominated {X A E : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [MeasurableSpace A] [NormedAddCommGroup E] (μ : Measure A)
    (f : X → A → E) (hf : ∀ x, MemLp (f x) 2 μ) (b : A → ℝ)
    (hb : MemLp b 2 μ) (hbound : ∀ x, ∀ᵐ a ∂μ, ‖f x a‖ ≤ b a)
    (hc : ∀ᵐ a ∂μ, Continuous (fun x => f x a)) :
    Continuous (fun x => (hf x).toLp (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have hi : Integrable (fun a => 4*(b a)^(2 : ℕ)) μ :=
    ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 4
  have hdist : Continuous (fun x => ∫ a, ‖f x a-f x₀ a‖^(2 : ℕ) ∂μ) := by
    apply continuous_of_dominated (bound := fun a => 4*(b a)^(2 : ℕ))
    · intro x
      exact ((hf x).aestronglyMeasurable.sub (hf x₀).aestronglyMeasurable).norm.pow 2
    · intro x
      filter_upwards [hbound x,hbound x₀] with a ha ha₀
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hd := norm_sub_le (f x a) (f x₀ a)
      have hn := norm_nonneg (f x a-f x₀ a)
      nlinarith [norm_nonneg (f x a)]
    · exact hi
    · filter_upwards [hc] with a ha
      exact ((ha.sub continuous_const).norm).pow 2
  have hnorm (x : X) : ‖(hf x).toLp (f x)-(hf x₀).toLp (f x₀)‖^(2 : ℕ) =
      ∫ a, ‖f x a-f x₀ a‖^(2 : ℕ) ∂μ := by
    rw [← MemLp.toLp_sub,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [((hf x).sub (hf x₀)).coeFn_toLp] with a ha
    rw [ha]
    rfl
  change Tendsto _ (𝓝 x₀) _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun x => ‖(hf x).toLp (f x)-(hf x₀).toLp (f x₀)‖^(2 : ℕ))
      (𝓝 x₀) (𝓝 0) := by
    simpa only [hnorm,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),integral_zero]
      using hdist.tendsto x₀
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def,Real.sqrt_sq (norm_nonneg _)] using h

end
end GaloisForLFunctions.HTGeometry
