import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondActions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture
import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient

/-! # The initial transfer coefficient of one longitudinal bond -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalPatches FixedHorizon
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance longitudinalAlgebra (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

private theorem longitudinal_trace (u : PathShell n) (e : Fin (n+1)) :
    (edgePart u e*finitePauliMatrix (pathWord (bondLabel e))).trace =
      ((u (bondLabel e):ℝ):ℂ)*(2:ℂ)^(n+2) := by
  classical
  change ((∑ ab : Fin 3×Fin 3, ((u (.inr (e,ab)):ℝ):ℂ) • finitePauliMatrix (couplingWord e ab))*
    finitePauliMatrix (couplingWord e (2,2))).trace=_
  rw [Matrix.sum_mul,Matrix.trace_sum,sum_eq_single (2,2)]
  · simp only [Matrix.smul_mul,Matrix.trace_smul,trace_pauli_mul,if_true,Fintype.card_fin,smul_eq_mul,bondLabel]
  · intro ab _ hn
    have hne : couplingWord e ab≠couplingWord e (2,2) := by
      intro he
      have hh := @pathWord_injective n (.inr (e,ab)) (.inr (e,(2,2))) he
      exact hn (Prod.mk.inj (Sum.inr.inj hh)).2
    simp only [Matrix.smul_mul,Matrix.trace_smul,trace_pauli_mul,if_neg hne,smul_zero]
  · exact fun hn => (hn (mem_univ _)).elim

/-- The derivative seen by the calibrated two-site reporter is twice
the actual longitudinal coefficient. Every other Pauli coordinate
vanishes by trace orthogonality. -/
theorem longitudinal_transfer (u : PathShell n) (e : Fin (n+1)) :
    (bracketStep ((-Complex.I) • edgePart u e) (bondOutput e)*bondInput e).trace =
      (2:ℂ)^(n+2)*(2*((u (bondLabel e):ℝ):ℂ)) := by
  let J := edgePart u e
  let P := finitePauliMatrix (pathWord (bondLabel e))
  let Y := bondOutput e
  have hY : Y*Y=1 := finitePauliMatrix_mul_self _
  have ha : P*Y=-(Y*P) := bond_reporter_anticommutes e
  have hr : Y*P=-(P*Y) := by rw [ha,neg_neg]
  have h₁ : ((Y*J)*(P*Y)).trace=(J*P).trace := calc
    _ = ((Y*(J*P))*Y).trace := by simp only [mul_assoc]
    _ = (Y*(Y*(J*P))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [←mul_assoc,hY,one_mul]
  have h₂ : (J*Y)*(P*Y)=-(J*P) := by
    rw [mul_assoc J Y,←mul_assoc Y P,hr,neg_mul,mul_assoc,hY,mul_one,mul_neg]
  change ((Y*((-Complex.I) • J)-((-Complex.I) • J)*Y)*(Complex.I • (P*Y))).trace=_
  have hb : Y*((-Complex.I) • J)-((-Complex.I) • J)*Y=(-Complex.I) • (Y*J-J*Y) := by
    rw [Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  have htrace : (J*P).trace=((u (bondLabel e):ℝ):ℂ)*(2:ℂ)^(n+2) := longitudinal_trace u e
  rw [hb,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    show (-Complex.I)*Complex.I=1 by rw [neg_mul,Complex.I_mul_I,neg_neg],one_smul,
    sub_mul,Matrix.trace_sub,h₁,h₂,Matrix.trace_neg,htrace]
  ring

#print axioms longitudinal_transfer
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
