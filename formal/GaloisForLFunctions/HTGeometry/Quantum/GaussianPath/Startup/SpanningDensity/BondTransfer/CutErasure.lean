import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.CutPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SelectedOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality

/-! # An erased bond has zero transfer between its two endpoints -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBonds RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
variable {n : ℕ}

/-- The calibrated input has zero trace against every observable
supported away from the right endpoint. A single right-site flip
commutes with that observable and reverses the input. -/
theorem bond_input_trace_zero (e : Fin (n+1)) (S : Finset (Fin (n+2))) (hr : e.succ∉S)
    (A : Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) (hA : IsSiteSupported S A) :
    (A*bondInput e).trace=0 := by
  let Q := finitePauliMatrix (onsiteWord e.succ 0)
  let P := finitePauliMatrix (pathWord (bondLabel e))
  let Y := bondOutput e
  let B := bondInput e
  have hQ : IsSiteSupported Sᶜ Q := by
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro i hi
    exact if_neg (show i≠e.succ from fun h => hi (h ▸ Finset.mem_compl.mpr hr))
  have hPY : Commute Q Y := (commute_onsitePauli_iff ..).mpr (Or.inr rfl)
  have hP : Q*P=-(P*Q) := by
    apply finitePauliMatrix_anticommute_of_not_commute
    intro h
    exact (by decide : (0:Fin 3)≠2) (((commute_onsite_coupling_iff e.succ 0 e (2,2)).mp h).2 rfl)
  have hB : Q*B=-(B*Q) := by
    change Q*(Complex.I • (P*Y))=-(Complex.I • (P*Y)*Q)
    rw [mul_smul_comm,smul_mul_assoc,←mul_assoc,hP,neg_mul,mul_assoc,hPY.eq,←mul_assoc,smul_neg]
  exact trace_zero_of_flip A B Q
    (commute_of_isSiteSupported_disjoint disjoint_compl_right hA hQ) (finitePauliMatrix_mul_self _) hB

/-- The right-hand flip reverses the two-site input, whereas the
cut evolution keeps the reporter on the left half for every real time. -/
theorem erased_transfer_zero (u : PathShell n) (e : Fin (n+1)) (t : ℝ) :
    signal (pathHamiltonianCut u e) (bondOutput e) (bondInput e) t=0 := by
  let L := leftBlock e
  let R := rightBlock e
  let Y := bondOutput e
  let B := bondInput e
  have hl : e.castSucc∈L := Finset.mem_Iic.mpr le_rfl
  have hr : e.succ∈R := Finset.mem_Ioi.mpr (Fin.castSucc_lt_succ ..)
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    exact fun _ h₁ h₂ => (Finset.mem_Ioi.mp h₂).not_ge (Finset.mem_Iic.mp h₁)
  have hY : IsSiteSupported L Y := bond_output_supported hl
  let U := unitaryEvolution (packet u L) t
  let V := unitaryEvolution (packet u R) t
  have hU := isSiteSupported_unitaryEvolution (packet_supported u L) t
  have hV := isSiteSupported_unitaryEvolution (packet_supported u R) t
  have comm : Commute Y V := commute_of_isSiteSupported_disjoint hd hY hV
  have hV' : Vᴴ*V=1 := (Unitary.mem_iff.mp (unitaryEvolution_mem_unitary (packet_selfAdjoint u R) t)).1
  have restore : Vᴴ*Y*V=Y := by rw [mul_assoc,comm.eq,←mul_assoc,hV',one_mul]
  have fac : unitaryEvolution (pathHamiltonianCut u e) t=V*U := by
    rw [SingleCut.cut_eq_packets,add_comm (packet u (leftBlock e)) (packet u (rightBlock e))]
    exact unitaryEvolution_add_of_isSiteSupported_disjoint hd.symm (packet_supported u R) (packet_supported u L) t
  have erase : (V*U)ᴴ*Y*(V*U)=Uᴴ*Y*U := calc
    _ = Uᴴ*(Vᴴ*Y*V)*U := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = _ := by rw [restore]
  have hz := bond_input_trace_zero e L (fun h => Finset.disjoint_left.mp hd h hr)
    (Uᴴ*Y*U) ((hU.conjTranspose.matrix_mul hY).matrix_mul hU)
  have hneg := EigenlineSignals.adjoint_evolution
    (⟨pathHamiltonianCut u e,isSelfAdjoint_pathHamiltonianCut u e⟩ :
      selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ)) t
  unfold signal
  change ((Fintype.card (Fin (n+2)→Bool):ℂ)⁻¹*
    (unitaryEvolution (pathHamiltonianCut u e) (-t)*Y*unitaryEvolution (pathHamiltonianCut u e) t*B).trace).re=0
  rw [show unitaryEvolution (pathHamiltonianCut u e) (-t)=(unitaryEvolution (pathHamiltonianCut u e) t)ᴴ from hneg,
    fac,erase,hz,mul_zero,Complex.zero_re]

#print axioms erased_transfer_zero
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
