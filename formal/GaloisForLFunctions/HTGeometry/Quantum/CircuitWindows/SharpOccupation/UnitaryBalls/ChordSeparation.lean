import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.AntipodalFiber
import GaloisForLFunctions.HTGeometry.FiniteCyclicAffineCorrelations

/-! # Operator separation from a packet with an antipodal eigenvector -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The sum of phases at most g/2 turns apart has length at least
twice the cosine of half the largest angular change. -/
private theorem chord_lower (x : UnitAddCircle) {g t : ℝ} (hg : g≤1) (ht : |t|≤g/2) :
    2*Real.cos (Real.pi*g/2) ≤ ‖(x.toCircle:ℂ)+((x+(t:UnitAddCircle)).toCircle:ℂ)‖ := by
  rw [AddCircle.toCircle_add,Circle.coe_mul,←mul_one_add,norm_mul,Circle.norm_coe,one_mul,
    AddCircle.toCircle_apply_mk,div_one,Circle.coe_exp,norm_one_add_exp_mul_I]
  rw [show 2*Real.pi*t/2=Real.pi*t by ring]
  apply mul_le_mul_of_nonneg_left _ zero_lt_two.le
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi*t))
    (by nlinarith only [mul_le_mul_of_nonneg_left hg Real.pi_pos.le,Real.pi_pos] : Real.pi*g/2≤Real.pi)
    (by rw [abs_mul,abs_of_pos Real.pi_pos]; linarith only [mul_le_mul_of_nonneg_left ht Real.pi_pos.le])
  rw [Real.cos_abs] at h
  exact h.trans (le_abs_self _)

/-- Each coordinate of the kernel vector sees the sum of the nearby
phases. Summing its squared amplitudes gives an operator-norm lower bound. -/
theorem antipodal_separation {C : Matrix I I ℂ} (x : UnitAddTorus I) (u : I→ℝ)
    {g : ℝ} (hg : g≤1) (hu : ∀ i, |u i|≤g/2)
    {v : I→ℂ} (hv : v≠0) (hker : (C+packet (x+fun i => (u i:UnitAddCircle))) *ᵥ v=0) :
    2*Real.cos (Real.pi*g/2) ≤ ‖C-packet x‖ := by
  let y := x+(fun i => (u i:UnitAddCircle))
  let R := 2*Real.cos (Real.pi*g/2)
  let V := WithLp.toLp 2 v
  let W := WithLp.toLp 2 ((C-packet x) *ᵥ v)
  have hV : 0<‖V‖ := norm_pos_iff.mpr fun h => hv (congrArg WithLp.ofLp h)
  by_cases hR : 0≤R
  · have hp (i : I) : R*‖v i‖ ≤ ‖((C-packet x) *ᵥ v) i‖ := by
      have hi := congrFun hker i
      change ((C+packet y) *ᵥ v) i=0 at hi
      rw [add_mulVec,Pi.add_apply,packet,mulVec_diagonal] at hi
      rw [sub_mulVec,Pi.sub_apply,packet,mulVec_diagonal,eq_neg_of_add_eq_zero_left hi]
      have he : -(((y i).toCircle:ℂ)*v i)-((x i).toCircle:ℂ)*v i =
          -((((x i).toCircle:ℂ)+((y i).toCircle:ℂ))*v i) := by ring
      rw [he,norm_neg,norm_mul]
      exact mul_le_mul_of_nonneg_right (chord_lower (x i) hg (hu i)) (norm_nonneg _)
    have hsq := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
      pow_le_pow_left₀ (mul_nonneg hR (norm_nonneg (v i))) (hp i) 2
    simp only [mul_pow,←Finset.mul_sum] at hsq
    have hle : R*‖V‖ ≤ ‖W‖ := by
      apply (sq_le_sq₀ (mul_nonneg hR (norm_nonneg _)) (norm_nonneg _)).mp
      rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
      exact hsq
    exact (mul_le_mul_iff_left₀ hV).mp (hle.trans ((C-packet x).l2_opNorm_mulVec V))
  · exact (le_of_not_ge hR).trans (norm_nonneg _)

#print axioms antipodal_separation
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
