import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import Mathlib.Analysis.Calculus.MeanValue

/-! # Operator-norm Lie product error for a pair of skew-adjoint generators -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance liePairRationalAlgebra : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

private theorem reverseFlow_deriv (x : A) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => exp ((t-r) • x)) (-(exp ((t-s) • x)*x)) s := by
  have hd := (hasDerivAt_const s t).sub (hasDerivAt_id s)
  simpa [Function.comp_def] using (hasDerivAt_exp_smul_const x (t-s)).scomp s hd

private theorem flow_unitary (x : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    exp (s • x) ∈ unitary A :=
  exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx)

/-- Moving an observable through a unitary flow costs at most the elapsed
time times its generator commutator. -/
theorem norm_exp_mul_sub_mul_exp_le_commutator (x y : A) (hx : x ∈ skewAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖exp (t • x)*y-y*exp (t • x)‖ ≤ ‖x*y-y*x‖*t := by
  let f (s : ℝ) := exp ((t-s) • x)*y*exp (s • x)
  let g (s : ℝ) := exp ((t-s) • x)*(y*x-x*y)*exp (s • x)
  have h (s : ℝ) : HasDerivAt f (g s) s := by
    have hd := ((reverseFlow_deriv x t s).mul_const y).fun_mul (hasDerivAt_exp_smul_const' x s)
    convert hd using 1
    dsimp [g]
    noncomm_ring
  have hbound (s : ℝ) : ‖g s‖ ≤ ‖x*y-y*x‖ := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_unitary x hx s),
      CStarRing.norm_mem_unitary_mul _ (flow_unitary x hx (t-s)),norm_sub_rev]
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := t) (fun s _ => (h s).hasDerivWithinAt) (fun s _ => hbound s)
    t ⟨ht,le_rfl⟩
  rw [norm_sub_rev]
  simpa [f] using he

/-- Interpolate between the product and the exact flow. Its derivative
contains only the failure of the first flow to commute with the second generator. -/
theorem norm_lie_pair_error_le_commutator (x y : A) (hx : x ∈ skewAdjoint A)
    (hy : y ∈ skewAdjoint A) (t : ℝ) (ht : 0 ≤ t) :
    ‖exp (t • x)*exp (t • y)-exp (t • (x+y))‖ ≤ t^2*‖x*y-y*x‖ := by
  let f (s : ℝ) := exp ((t-s) • (x+y))*exp (s • x)*exp (s • y)
  let g (s : ℝ) := exp ((t-s) • (x+y))*(exp (s • x)*y-y*exp (s • x))*exp (s • y)
  have h (s : ℝ) : HasDerivAt f (g s) s := by
    have hd := ((reverseFlow_deriv (x+y) t s).fun_mul
      (hasDerivAt_exp_smul_const' x s)).fun_mul (hasDerivAt_exp_smul_const' y s)
    convert hd using 1
    dsimp [g]
    noncomm_ring
  have hbound s (hs : s ∈ Set.Ico 0 t) : ‖g s‖ ≤ ‖x*y-y*x‖*t := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_unitary y hy s),
      CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ((skewAdjoint A).add_mem hx hy) (t-s))]
    exact (norm_exp_mul_sub_mul_exp_le_commutator x y hx s hs.1).trans
      (mul_le_mul_of_nonneg_left hs.2.le (norm_nonneg _))
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (h s).hasDerivWithinAt) hbound t ⟨ht,le_rfl⟩
  simpa [f,pow_two,mul_comm,mul_left_comm,mul_assoc] using he

#print axioms norm_lie_pair_error_le_commutator
end
end GaloisForLFunctions.HTGeometry
