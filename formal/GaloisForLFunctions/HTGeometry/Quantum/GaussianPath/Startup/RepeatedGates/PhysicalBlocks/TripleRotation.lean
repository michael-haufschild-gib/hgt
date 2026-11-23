import GaloisForLFunctions.HTGeometry.ScalarSquareExponential
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PauliWitnesses

/-! # A static two-bond rotation with maximal signals on three sites -/
open Matrix Real NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private theorem quarter_exp {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (J : R) (hJ : J*J=1) :
    exp ((-Complex.I*((π/2:ℝ):ℂ)) • J)=(-Complex.I) • J := by
  let x : ℝ := π/2
  have hx : x≠0 := (half_pos pi_pos).ne'
  have hsq : ((-Complex.I*(x:ℂ)) • J)*((-Complex.I*(x:ℂ)) • J)=(-((x:ℂ)^2)) • (1:R) := by
    rw [smul_mul_smul_comm,hJ]
    congr 1
    calc _ = (Complex.I*Complex.I)*(x:ℂ)^2 := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [_root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one _ x hsq]
  simp only [x,Real.cos_pi_div_two,Complex.ofReal_zero,zero_smul,zero_add,smul_smul,
    Real.sinc_of_ne_zero hx,Real.sin_pi_div_two,Complex.ofReal_div,Complex.ofReal_one]
  congr 1
  have hne : ((π/2:ℝ):ℂ)≠0 := by exact_mod_cast hx
  field_simp

/-- The equal superposition of anticommuting involutions is itself an
involution. Its quarter turn implements that superposition up to phase. -/
def mix {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] (A B : R) :=
  ((1/sqrt 2:ℝ):ℂ) • (A+B)

private theorem factor_sq : ((1/sqrt 2:ℝ):ℂ)*((1/sqrt 2:ℝ):ℂ)=1/2 := by
  norm_cast
  rw [←sq,div_pow,sq_sqrt (by norm_num : (0:ℝ)≤2),one_pow]
  norm_num

private theorem mix_square {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] (A B : R)
    (ha : A*A=1) (hb : B*B=1) (hab : A*B=-(B*A)) : mix A B*mix A B=1 := by
  have he : (A+B)*(A+B)=(2:ℂ) • (1:R) := by
    rw [add_mul,mul_add,mul_add,ha,hb,hab,two_smul]; abel
  rw [mix,smul_mul_smul_comm,he,factor_sq,smul_smul,show (1/2:ℂ)*2=1 by norm_num,one_smul]

theorem mix_quarter {N : ℕ} (A B : Matrix (Fin N→Bool) (Fin N→Bool) ℂ) (ha : A*A=1) (hb : B*B=1) (hab : A*B=-(B*A)) :
    unitaryEvolution (mix A B) (π/2)=(-Complex.I) • mix A B := by
  unfold unitaryEvolution
  rw [←Complex.coe_smul,smul_smul,mul_comm]
  exact quarter_exp _ (mix_square A B ha hb hab)

/-- A probe odd on the first bond and even on the second becomes their
three-site product. Interchanging the bonds handles the opposite parity. -/
theorem mix_conjugate {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] (A B P : R)
    (ha : A*A=1) (hb : B*B=1) (hab : A*B=-(B*A))
    (hP : A*P=-(P*A)) (hc : Commute B P) : mix A B*P*mix A B=-(P*A*B) := by
  have hba : B*A=-(A*B) := by rw [hab,neg_neg]
  have he : (A+B)*P*(A+B)=(-2:ℂ) • (P*A*B) := by
    simp only [add_mul,mul_add,hP,hc.eq,neg_mul,mul_assoc,ha,hb,hba,mul_neg,mul_one,neg_smul,two_smul]
    abel
  rw [mix,smul_mul_assoc,smul_mul_smul_comm,he,factor_sq,smul_smul,show (1/2:ℂ)*(-2) = -1 by norm_num,neg_one_smul]

#print axioms mix_quarter
#print axioms mix_conjugate
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
