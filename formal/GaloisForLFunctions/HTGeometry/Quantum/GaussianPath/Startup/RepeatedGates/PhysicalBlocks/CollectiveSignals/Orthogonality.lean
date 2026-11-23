import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CausalSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CutMoments

/-! # Orthogonal Choi tests from two missing temporal connections -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal
noncomputable section

/-- An involution commuting with one factor and reversing the other
annihilates their trace. -/
theorem trace_zero_of_flip {I : Type*} [Fintype I] [DecidableEq I]
    (A B Q : Matrix I I ℂ) (hc : Commute A Q) (hq : Q*Q=1) (ha : Q*B=-(B*Q)) :
    (A*B).trace=0 := by
  have hf : Q*(A*B)*Q=-(A*B) := calc
    _ = A*(Q*B)*Q := by rw [←mul_assoc Q A B,←hc.eq,mul_assoc A Q B]
    _ = _ := by rw [ha,mul_neg,neg_mul]; simp only [mul_assoc,hq,mul_one]
  have hh : (Q*(A*B)*Q).trace=(A*B).trace := by
    rw [Matrix.trace_mul_comm (Q*(A*B)) Q,←mul_assoc,hq,one_mul]
  rw [hf,trace_neg] at hh
  linear_combination -hh / 2

/-- If one input flip misses both propagated probes, it can reverse the
paired left-right test without changing its circuit expectation. -/
theorem orthogonal_of_missing_input {N : ℕ} (C : TwoQubitCircuit N) (i j k : Fin N)
    (hi : i∉inputs (circuitWord C) k) (hj : j∉inputs (circuitWord C) k)
    (P R B D Q : Register N) (hP : P.IsHermitian) (hs : IsSiteSupported {i} P)
    (ht : IsSiteSupported {j} R) (hu : IsSiteSupported {k} Q) (hQ : Q*Q=1)
    (ha : Q*(D*Bᴴ)=-((D*Bᴴ)*Q)) :
    inner ℂ (RHTower.choiVector (P*C.eval.val*B)) (RHTower.choiVector (R*C.eval.val*D))=0 := by
  let U := C.eval.val
  have h₁ := commute_of_absent C i k hi P Q hs hu
  have h₂ := commute_of_absent C j k hj R Q ht hu
  have he : (star U*P*U)*(star U*R*U)=star U*(P*R)*U := by
    have hh : U*star U=1 := C.eval.property.2
    simp only [mul_assoc,←mul_assoc U (star U),hh,one_mul]
  have hc := h₁.mul_left h₂
  change Commute ((star U*P*U)*(star U*R*U)) Q at hc
  rw [he] at hc
  have hz := trace_zero_of_flip _ _ Q hc hQ ha
  rw [RHTower.inner_choiVector Fintype.card_pos]
  change ((P*U*B)ᴴ*(R*U*D)).trace/_=0
  have ht' : ((P*U*B)ᴴ*(R*U*D)).trace=((star U*(P*R)*U)*(D*Bᴴ)).trace := by
    simp only [Matrix.conjTranspose_mul,hP.eq,mul_assoc]
    rw [Matrix.trace_mul_comm Bᴴ]
    simp only [Matrix.star_eq_conjTranspose,mul_assoc]
  rw [ht',hz,zero_div]

#print axioms orthogonal_of_missing_input
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
