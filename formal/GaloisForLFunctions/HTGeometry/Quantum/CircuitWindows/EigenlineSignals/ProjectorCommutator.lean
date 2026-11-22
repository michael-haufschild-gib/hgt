import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Two commuting probes detect a phase on a rank-one subspace -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
variable {d : Type*} [Fintype d] [DecidableEq d]
private abbrev M (d : Type*) := Matrix d d ℂ

/-- Insert a phase on the range of a projection. -/
def twist (z : ℂ) (P : M d) := 1+(z-1) • P

theorem twist_mul {P : M d} (hp : P*P=P) (z w : ℂ) : twist z P*twist w P=twist (z*w) P := by
  simp only [twist,add_mul,mul_add,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hp]
  module

theorem twist_unitary {P : M d} (hp : star P=P) (h₂ : P*P=P) (z : ℂ) (hz : ‖z‖=1) :
    twist z P ∈ unitary _ := by
  have he : star (twist z P)=twist (star z) P := by
    simp only [twist,star_add,star_smul,star_sub,star_one,hp]
  have hnorm : z*star z=1 := by simp [Complex.star_def,Complex.mul_conj',hz]
  simp only [Unitary.mem_iff,he,twist_mul h₂,mul_comm (star z) z,hnorm,twist,sub_self,zero_smul,add_zero,and_self]

/-- On the marked subspace, the transmitted signal is exactly
(1−z)AB when A, B and AB carry that subspace into its orthogonal complement. -/
theorem commutator_mul_projection (z : ℂ) (P A B : M d) (hP : star P=P)
    (hP2 : P*P=P) (hAB : Commute A B) (ha : P*A*P=0) (hb : P*B*P=0)
    (hab : P*(A*B)*P=0) :
    ((star (twist z P)*A*twist z P)*B-B*(star (twist z P)*A*twist z P))*P=
      (1-z) • (A*B*P) := by
  let R := twist z P
  have hr : R*P=z • P := by
    rw [show R=1+(z-1) • P from rfl,add_mul,one_mul,Matrix.smul_mul,hP2,sub_smul,one_smul]
    abel
  have hleft (K : M d) (hk : P*K*P=0) : star R*(K*P)=K*P := by
    simp only [R,twist,star_add,star_one,star_smul,hP,add_mul,one_mul,Matrix.smul_mul,
      ←mul_assoc P K P,hk,smul_zero,add_zero]
  have hright : R*(B*P)=B*P := by
    simp only [R,twist,add_mul,one_mul,Matrix.smul_mul,←mul_assoc P B P,hb,smul_zero,add_zero]
  change ((star R*A*R)*B-B*(star R*A*R))*P=_
  have h₁ : ((star R*A*R)*B)*P=A*B*P := by
    rw [mul_assoc (star R*A*R),mul_assoc (star R*A),hright,mul_assoc,←mul_assoc A B,hleft _ hab]
  have h₂ : (B*(star R*A*R))*P=z • (A*B*P) := by
    rw [mul_assoc B,mul_assoc (star R*A),hr,Matrix.mul_smul,mul_assoc,hleft A ha,
      Matrix.mul_smul,←mul_assoc,hAB.symm.eq]
  rw [sub_mul,h₁,h₂,sub_smul,one_smul]

/-- A unit-norm projection and unitary probes give an operator-norm
signal at least as large as the chord cut out by the marked phase. -/
theorem chord_le_commutator (z : ℂ) (P A B : M d) (hP : star P=P) (hP2 : P*P=P)
    (hn : ‖P‖=1) (hA : A ∈ unitary _) (hB : B ∈ unitary _) (hAB : Commute A B)
    (ha : P*A*P=0) (hb : P*B*P=0) (hab : P*(A*B)*P=0) :
    ‖1-z‖ ≤ ‖(star (twist z P)*A*twist z P)*B-B*(star (twist z P)*A*twist z P)‖ := by
  have h := norm_mul_le ((star (twist z P)*A*twist z P)*B-B*(star (twist z P)*A*twist z P)) P
  rwa [commutator_mul_projection z P A B hP hP2 hAB ha hb hab,norm_smul,
    CStarRing.norm_mem_unitary_mul P (mul_mem hA hB),hn,mul_one,mul_one] at h

end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
