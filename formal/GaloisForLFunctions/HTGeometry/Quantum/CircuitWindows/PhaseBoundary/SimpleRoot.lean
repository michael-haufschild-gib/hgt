import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! # Simple real roots persist inside prescribed neighborhoods -/
open Polynomial Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

/-- A simple root has opposite endpoint signs on arbitrarily short
closed intervals about it. -/
theorem sign_bracket (p : ℝ[X]) (y : ℝ) (hy : p.eval y = 0)
    (hd : p.derivative.eval y ≠ 0) {U : Set ℝ} (hU : U ∈ 𝓝 y) :
    ∃ l r : ℝ, l ≤ r ∧ Icc l r ⊆ U ∧ p.eval l * p.eval r < 0 := by
  obtain ⟨q,hq⟩ := Polynomial.dvd_iff_isRoot.mpr hy
  have hn : q.eval y ≠ 0 := by
    simpa only [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul,eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero] using hd
  have hs : ∀ᶠ z in 𝓝 y, 0 < q.eval y * q.eval z := by
    apply continuousAt_const.eventually_lt (continuous_const.mul q.continuous).continuousAt
    exact mul_self_pos.mpr hn
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hs)
  let l := y-δ/2
  let r := y+δ/2
  have hlr : l ≤ r := by dsimp only [l,r]; linarith
  have hsub : Icc l r ⊆ Metric.ball y δ := by
    intro z hz
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp only [l,r] at hz
    constructor <;> linarith only [hz.1,hz.2,hδ]
  have hsign : 0 < q.eval l * q.eval r := by
    have h₁ : 0 < q.eval y * q.eval l := (hball (hsub (left_mem_Icc.mpr hlr))).2
    have h₂ : 0 < q.eval y * q.eval r := (hball (hsub (right_mem_Icc.mpr hlr))).2
    rcases (mul_pos_iff.mp h₁) with h|h <;> rcases (mul_pos_iff.mp h₂) with k|k
    · exact mul_pos h.2 k.2
    · exact (h.1.not_gt k.1).elim
    · exact (k.1.not_gt h.1).elim
    · exact mul_pos_of_neg_of_neg h.2 k.2
  refine ⟨l,r,hlr,fun z hz => (hball (hsub hz)).1,?_⟩
  simp only [hq,eval_mul,eval_sub,eval_X,eval_C]
  rw [show (l-y)*q.eval l*((r-y)*q.eval r) = ((l-y)*(r-y))*(q.eval l*q.eval r) by ring]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by dsimp [l]; linarith) (by dsimp [r]; linarith)) hsign

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
