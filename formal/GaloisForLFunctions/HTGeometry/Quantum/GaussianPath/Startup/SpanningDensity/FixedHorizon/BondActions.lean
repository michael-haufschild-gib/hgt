import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CutMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondProbability
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Choi tests on physical bonds crossing an oriented circuit cut -/
open Matrix GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {n : ℕ}

def bondOutput (e : Fin (n+1)) := finitePauliMatrix (bondReporter e)
def bondInput (e : Fin (n+1)) := Complex.I • (finitePauliMatrix (pathWord (bondLabel e))*bondOutput e)

theorem bond_input_hermitian (e : Fin (n+1)) : (bondInput e).IsHermitian := by
  let P := finitePauliMatrix (pathWord (bondLabel e))
  let Y := bondOutput e
  have ha : P*Y=-(Y*P) := bond_reporter_anticommutes e
  have hrev : Y*P=-(P*Y) := by rw [ha,neg_neg]
  change (Complex.I • (P*Y))ᴴ=Complex.I • (P*Y)
  rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
    (show Yᴴ=Y from (finitePauliMatrix_isHermitian _).eq),
    (show Pᴴ=P from (finitePauliMatrix_isHermitian _).eq),hrev,Complex.star_def,Complex.conj_I,
    neg_smul,smul_neg,neg_neg]

theorem bond_input_norm (e : Fin (n+1)) : ‖bondInput e‖ ≤ 1 := by
  rw [bondInput,norm_smul,Complex.norm_I,one_mul]
  exact (norm_mul_le _ _).trans_eq (by rw [bondOutput,norm_finitePauliMatrix,norm_finitePauliMatrix,one_mul])

private theorem onsite_supported {S : Finset (Fin (n+2))} {i : Fin (n+2)} (hi : i∈S) :
    IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) S (finitePauliMatrix (onsiteWord i 0)) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro v hv
  exact if_neg (show v≠i from fun h => hv (h ▸ hi))

theorem bond_output_supported {S : Finset (Fin (n+2))} {e : Fin (n+1)} (hl : e.castSucc∈S) :
    IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) S (bondOutput e) := onsite_supported hl

theorem bond_input_supported {S : Finset (Fin (n+2))} {e : Fin (n+1)}
    (hl : e.castSucc∈S) (hr : e.succ∈S) :
    IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) S (bondInput e) := by
  apply IsSiteSupported.complex_smul
  apply IsSiteSupported.matrix_mul _ (bond_output_supported hl)
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro v hv
  simp only [bondLabel,pathWord,couplingWord,if_neg (show v≠e.castSucc from fun h => hv (h ▸ hl)),
    if_neg (show v≠e.succ from fun h => hv (h ▸ hr))]

/-- Distinct bonds with left endpoints on the same side of a circuit cut
have orthogonal circuit test vectors. The right-hand spin flip commutes
with both outputs and with the other input, and reverses its own input. -/
theorem oriented_bond_orthogonal (C : TwoQubitCircuit (n+2)) (S : Finset (Fin (n+2)))
    (hc : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S)
    {e f : Fin (n+1)} (hef : e≠f) (he : e.castSucc∈S) (hf : f.castSucc∈S) (her : e.succ∉S) :
    inner ℂ (choiVector (bondOutput e*C.eval.val*bondInput e))
      (choiVector (bondOutput f*C.eval.val*bondInput f))=0 := by
  let Q := finitePauliMatrix (onsiteWord e.succ 0)
  let P (g : Fin (n+1)) := finitePauliMatrix (pathWord (bondLabel g))
  have hY (g : Fin (n+1)) : Commute Q (bondOutput g) := (commute_onsitePauli_iff ..).mpr (Or.inr rfl)
  have hPf : Commute Q (P f) := (commute_onsite_coupling_iff e.succ 0 f (2,2)).mpr
    ⟨fun h => (her (h ▸ hf)).elim,fun h => (hef (Fin.succ_injective _ h)).elim⟩
  have hPe : Q*P e=-(P e*Q) := by
    apply finitePauliMatrix_anticommute_of_not_commute
    intro h
    exact (by decide : (0:Fin 3)≠2) (((commute_onsite_coupling_iff e.succ 0 e (2,2)).mp h).2 rfl)
  have hb : Commute Q (bondInput f) := (hPf.mul_right (hY f)).smul_right _
  have ha : Q*bondInput e=-(bondInput e*Q) := by
    change Q*(Complex.I • (P e*bondOutput e))=-(Complex.I • (P e*bondOutput e)*Q)
    rw [mul_smul_comm,smul_mul_assoc,←mul_assoc,hPe,neg_mul,mul_assoc,(hY e).eq,
      ←mul_assoc,smul_neg]
  apply circuit_test_orthogonal C S hc _ _ _ _ Q
    (IsSiteSupported.matrix_mul (bond_output_supported he).conjTranspose (bond_output_supported hf))
    (onsite_supported (Finset.mem_compl.mpr her)) (finitePauliMatrix_mul_self _)
  rw [(bond_input_hermitian e).eq,←mul_assoc,hb.eq,mul_assoc,ha,mul_neg,mul_assoc]

#print axioms oriented_bond_orthogonal
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
