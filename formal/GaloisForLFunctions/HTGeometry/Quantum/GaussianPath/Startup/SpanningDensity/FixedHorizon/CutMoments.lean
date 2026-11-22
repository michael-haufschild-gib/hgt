import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.RHTower.AutonomousReturnReflection

/-! # Orthogonality of Choi tests across a circuit cut -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
private abbrev Op (I : Type*) := Matrix I I ℂ
private abbrev Reg (n : ℕ) := Op (Fin n → Bool)

/-- Moving a Hermitian left-right test from one Choi vector to the other
uses cyclicity of trace, with the same normalization on each side. -/
theorem choi_test_transfer {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Y B U V : Op I) (hY : Y.IsHermitian) (hB : B.IsHermitian) :
    inner ℂ (RHTower.choiVector (Y*U*B)) (RHTower.choiVector V) =
      inner ℂ (RHTower.choiVector U) (RHTower.choiVector (Y*V*B)) := by
  rw [RHTower.inner_choiVector Fintype.card_pos,RHTower.inner_choiVector Fintype.card_pos]
  congr 1
  simp only [Matrix.conjTranspose_mul,hY.eq,hB.eq,mul_assoc]
  rw [Matrix.trace_mul_comm B]
  simp only [mul_assoc]

private theorem flipped_trace {I : Type*} [Fintype I] [DecidableEq I] (A B Q : Op I)
    (hc : Commute A Q) (hQ : Q*Q=1) (ha : Q*B=-(B*Q)) : (A*B).trace=0 := by
  have hf : Q*(A*B)*Q=-(A*B) := calc
    _ = A*(Q*B)*Q := by rw [←mul_assoc Q A B,←hc.eq,mul_assoc A Q B]
    _ = -(A*B) := by rw [ha,mul_neg,neg_mul]; simp only [mul_assoc,hQ,mul_one]
  have h : (Q*(A*B)*Q).trace=(A*B).trace := by
    rw [Matrix.trace_mul_comm (Q*(A*B)) Q,←mul_assoc,hQ,one_mul]
  rw [hf,Matrix.trace_neg] at h
  linear_combination -h / 2

/-- If the two outputs lie on the same side, one unused opposite-side
Pauli flip can reverse the paired inputs. Their circuit Choi tests are
then exactly orthogonal, regardless of the gates within either side. -/
theorem circuit_test_orthogonal {n : ℕ} (C : TwoQubitCircuit n) (S : Finset (Fin n))
    (hc : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S)
    (Y Y' B B' Q : Reg n) (hY : IsSiteSupported S (Yᴴ*Y'))
    (hQ : IsSiteSupported Sᶜ Q) (hq : Q*Q=1) (ha : Q*(B'*Bᴴ)=-((B'*Bᴴ)*Q)) :
    inner ℂ (RHTower.choiVector (Y*C.eval.val*B)) (RHTower.choiVector (Y'*C.eval.val*B'))=0 := by
  let A := star C.eval.val*(Yᴴ*Y')*C.eval.val
  have hA := circuit_conjugate_supported C S hc _ hY
  have ht := flipped_trace A (B'*Bᴴ) Q (commute_of_isSiteSupported_disjoint disjoint_compl_right hA hQ) hq ha
  rw [RHTower.inner_choiVector Fintype.card_pos]
  suffices he : ((Y*C.eval.val*B)ᴴ*(Y'*C.eval.val*B')).trace=(A*(B'*Bᴴ)).trace by
    rw [he,ht,zero_div]
  simp only [Matrix.conjTranspose_mul,mul_assoc]
  rw [Matrix.trace_mul_comm Bᴴ]
  simp only [A,Matrix.star_eq_conjTranspose,mul_assoc]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
