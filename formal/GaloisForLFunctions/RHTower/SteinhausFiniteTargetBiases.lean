import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse
import Mathlib.Analysis.InnerProductSpace.LinearMap

open scoped BigOperators InnerProductSpace

noncomputable section
namespace RHTower

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The literal finite Gram operator of the complex channel columns. -/
def steinhausFiniteFrameOperator (a : ι → E) : E →L[ℂ] E :=
  ∑ i, InnerProductSpace.rankOne ℂ (a i) (a i)

theorem steinhausFiniteFrameOperator_apply (a : ι → E) (w : E) :
    steinhausFiniteFrameOperator a w = ∑ i, inner ℂ (a i) w • a i := by
  simp only [steinhausFiniteFrameOperator, _root_.sum_apply, InnerProductSpace.rankOne_apply]

/-- The operator quadratic form is exactly the original finite channel energy. -/
theorem steinhausFiniteFrameOperator_energy (a : ι → E) (w : E) :
    (inner ℂ (steinhausFiniteFrameOperator a w) w).re = ∑ i, ‖inner ℂ (a i) w‖ ^ 2 := by
  rw [steinhausFiniteFrameOperator_apply, sum_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inner_smul_left, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable [CompleteSpace E]

/-- A coercive actual frame synthesizes every target with controlled total bias energy and individual circle means. -/
theorem exists_steinhausFiniteTargetBiases (a : ι → E) {c : ℝ} (hc : 0 < c)
    (hframe : ∀ w : E, c * ‖w‖ ^ 2 ≤ ∑ i, ‖inner ℂ (a i) w‖ ^ 2) (v : E) :
    ∃ m : ι → ℂ, (∑ i, m i • a i) = v ∧
      (∑ i, ‖m i‖ ^ 2) ≤ ‖v‖ ^ 2 / c ∧
      ∀ i, ‖m i‖ ≤ ‖a i‖ * ‖v‖ / c := by
  have hcoe (w : E) : c * ‖w‖ ^ 2 ≤ (inner ℂ (steinhausFiniteFrameOperator a w) w).re := by
    rw [steinhausFiniteFrameOperator_energy]
    exact hframe w
  obtain ⟨S, hright, _, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_inverse_of_coercive hc hcoe
  refine ⟨fun i => inner ℂ (a i) (S v), ?_, ?_, ?_⟩
  · rw [← steinhausFiniteFrameOperator_apply]
    exact hright v
  · calc
      _ = (inner ℂ (steinhausFiniteFrameOperator a (S v)) (S v)).re :=
        (steinhausFiniteFrameOperator_energy a (S v)).symm
      _ = (inner ℂ v (S v)).re := by rw [hright]
      _ ≤ ‖v‖ * ‖S v‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
      _ ≤ ‖v‖ * (c⁻¹ * ‖v‖) := mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg v)
      _ = ‖v‖ ^ 2 / c := by ring
  · intro i
    calc
      _ ≤ ‖a i‖ * ‖S v‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖a i‖ * (c⁻¹ * ‖v‖) := mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg _)
      _ = ‖a i‖ * ‖v‖ / c := by ring

end RHTower
