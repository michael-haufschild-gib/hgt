import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture

/-! # Comparing a truncated Heisenberg observable with the full evolution -/
open NormedSpace Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

/-- Heisenberg evolution for a skew-adjoint generator. -/
def reporter (a x : A) (t : ℝ) := exp (t • (-a))*x*exp (t • a)

private theorem flow_unitary (a : A) (ha : a∈skewAdjoint A) (s : ℝ) :
    exp (s • a)∈unitary A :=
  exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s ha)

private theorem opposite_cancel (a : A) (s : ℝ) : exp (s • a)*exp (s • (-a))=1 := by
  rw [smul_neg,←exp_add_of_commute (Commute.refl (s • a)).neg_right]
  simp

/-- A boundary commutator of order p produces an observable error of
order p+1. The divisor p+1 accumulates to a factorial across path shells. -/
theorem reporter_difference (a b x : A) (ha : a∈skewAdjoint A) (p : ℕ) (K t : ℝ)
    (ht : 0≤t) (h : ∀ s ∈ Ico 0 t,
      ‖(a-b)*reporter b x s-reporter b x s*(a-b)‖ ≤ K*s^p) :
    ‖reporter b x t-reporter a x t‖ ≤ K*t^(p+1)/(p+1) := by
  let f (s : ℝ) := exp (s • a)*reporter b x s*exp (s • (-a))-x
  let g (s : ℝ) := exp (s • a)*((a-b)*reporter b x s-reporter b x s*(a-b))*exp (s • (-a))
  have hd (s : ℝ) : HasDerivAt f (g s) s := by
    have hd' := (((((hasDerivAt_exp_smul_const a s).fun_mul
      (hasDerivAt_exp_smul_const' (-b) s)).mul_const x).fun_mul
      (hasDerivAt_exp_smul_const b s)).fun_mul (hasDerivAt_exp_smul_const' (-a) s)).sub_const x
    convert hd' using 1
    · funext u
      simp only [f,reporter,mul_assoc]
    · dsimp only [g,reporter]
      noncomm_ring
  have hn (s : ℝ) : ‖g s‖=‖(a-b)*reporter b x s-reporter b x s*(a-b)‖ := by
    rw [g,CStarRing.norm_mul_mem_unitary _ (flow_unitary _ ((skewAdjoint A).neg_mem ha) _),
      CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ha _)]
  let B (s : ℝ) := K*s^(p+1)/(p+1)
  have hB (s : ℝ) : HasDerivAt B (K*s^p) s := by
    convert (((hasDerivAt_pow (p+1) s).const_mul K).div_const ((p:ℝ)+1)) using 1
    push_cast
    field_simp
  have he := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (fun s _ => (hd s).hasDerivWithinAt)
    (show ‖f 0‖≤B 0 by simp [f,reporter,B]) hB
    (fun s hs => (hn s).le.trans (h s hs)) (show t∈Icc 0 t from ⟨ht,le_rfl⟩)
  have heq : exp (t • a)*(reporter b x t-reporter a x t)*exp (t • (-a))=f t := by
    rw [mul_sub,sub_mul]
    congr 1
    change exp (t • a)*(exp (t • (-a))*x*exp (t • a))*exp (t • (-a))=x
    rw [←mul_assoc,←mul_assoc,opposite_cancel,one_mul,mul_assoc,opposite_cancel,mul_one]
  rw [←heq,CStarRing.norm_mul_mem_unitary _ (flow_unitary _ ((skewAdjoint A).neg_mem ha) _),
    CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ha _)] at he
  exact he

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
