import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleRotation

/-! # The quadratic Choi signal of an involutory rotation -/
open Matrix Real NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
variable {N : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem involution_evolution (J : Reg N) (hJ : J*J=1) (t : ℝ) :
    unitaryEvolution J t=(cos t:ℂ) • 1+(-Complex.I*(sin t:ℂ)) • J := by
  by_cases ht : t=0
  · subst t; simp [unitaryEvolution]
  have hs : ((-Complex.I*(t:ℂ)) • J)*((-Complex.I*(t:ℂ)) • J)=(-((t:ℂ)^2)) • (1:Reg N) := by
    rw [smul_mul_smul_comm,hJ]
    congr 1
    calc _ = (Complex.I*Complex.I)*(t:ℂ)^2 := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  unfold unitaryEvolution
  rw [←Complex.coe_smul,smul_smul,mul_comm (t:ℂ),_root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one _ t hs]
  rw [smul_smul,Real.sinc_of_ne_zero ht,Complex.ofReal_div]
  congr 2
  field_simp [show (t:ℂ)≠0 by exact_mod_cast ht]

/-- If the quarter-turn image of an output probe flips a second local
probe commuting with the original, its normalized transfer coefficient at
angle t is exactly sin² t. -/
theorem rotation_transfer (J P Q : Reg N) (hJ : IsSelfAdjoint J) (hJ₂ : J*J=1)
    (hP : P*P=1) (hQ : Q*Q=1) (hc : Commute P Q)
    (ha : Q*(J*P*J)=-((J*P*J)*Q)) (t : ℝ) :
    let U := unitaryEvolution J t
    let B := J*P*J
    (star U*P*U*B).trace/(Fintype.card (Fin N→Bool):ℂ)=(sin t:ℂ)^2 := by
  intro U B
  have collapse (Z : Reg N) : J*(J*Z)=Z := by rw [←mul_assoc,hJ₂,one_mul]
  have collapseP (Z : Reg N) : P*(P*Z)=Z := by rw [←mul_assoc,hP,one_mul]
  have hBB : (J*P*J)*B=1 := by simp only [B,mul_assoc,collapse,collapseP,hJ₂]
  have h₀ : (P*B).trace=0 := trace_zero_of_flip P B Q hc hQ ha
  have h₁ : (P*J*B).trace=J.trace := by simp only [B,mul_assoc,collapse,collapseP]
  have h₂ : (J*P*B).trace=J.trace := by
    dsimp only [B]
    rw [show J*P*(J*P*J)=((J*P)*J*P)*J by simp only [mul_assoc],Matrix.trace_mul_comm _ J]
    simp only [mul_assoc,collapse]
    rw [Matrix.trace_mul_comm P (J*P),mul_assoc,hP,mul_one]
  have hdim : (Fintype.card (Fin N→Bool):ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hu := involution_evolution J hJ₂ t
  change (star (unitaryEvolution J t)*P*(unitaryEvolution J t)*B).trace/_=_
  rw [hu]
  simp only [star_add,star_smul,star_one,hJ.star_eq,Complex.star_def,Complex.conj_ofReal,map_mul,
    map_neg,Complex.conj_I,neg_neg,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    one_mul,mul_one,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,hBB,h₀,h₁,h₂,
    Matrix.trace_one]
  apply (div_eq_iff hdim).mpr
  linear_combination (norm := ring) -((sin t:ℂ)^2*(Fintype.card (Fin N→Bool):ℂ))*Complex.I_mul_I

#print axioms rotation_transfer
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
