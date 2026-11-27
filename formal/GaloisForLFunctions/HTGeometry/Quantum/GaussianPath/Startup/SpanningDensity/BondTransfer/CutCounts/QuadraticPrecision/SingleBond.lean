import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LocalTests.ProjectiveTrace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutErasure
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.CalibratedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.LocalRows

/-! # One sufficiently strong bond excludes a circuit cut at fine precision -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon
noncomputable section
variable {n : ℕ}

/-- The circuit contribution is zero across its own cut. A bond with
transfer strictly greater than twice the fitting error cannot cross it. -/
theorem empty_detectable_of_fit (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (t r ε : ℝ) (hr : 2*ε≤r) (z : ℂ) (hz : ‖z‖=1)
    (hf : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤ε) :
    detectable c u t r=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hcross,hstrong⟩ := mem_filter.mp he
  let S := univ.filter fun i => c.val i=c.val e.castSucc
  have hl : e.castSucc∈S := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have hright : e.succ∉S := fun hh => (mem_crossed_iff c e).mp hcross (mem_filter.mp hh).2.symm
  have hcut (i : Fin C.gateCount) : (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S := by
    simp only [S,mem_filter,mem_univ,true_and,c.gate_agrees i]
  have hs := circuit_conjugate_supported C S hcut (bondOutput e) (bond_output_supported hl)
  let U := unitaryEvolution (pathHamiltonian u) t
  have ht := missing_trace_bound U C.eval.val (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t)
    C.eval.2 (bondOutput e) (bondInput e) (norm_finitePauliMatrix _).le (bond_input_norm _) z hz
    (bond_input_trace_zero e S hright _ hs)
  let d : ℂ := Fintype.card (Fin (n+2)→Bool)
  change r < |(d⁻¹*(unitaryEvolution (pathHamiltonian u) (-t)*bondOutput e*U*bondInput e).trace).re| at hstrong
  rw [EigenlineSignals.adjoint_evolution ⟨_,isSelfAdjoint_pathHamiltonian u⟩ t] at hstrong
  rw [div_eq_mul_inv,mul_comm _ d⁻¹] at ht
  exact hstrong.not_ge ((Complex.abs_re_le_norm _).trans (ht.trans ((mul_le_mul_of_nonneg_left hf zero_le_two).trans hr)))

/-- Only weak bonds and locally exceptional bonds can cross a fine fit.
There is no allowance for unresolved packets. -/
theorem fine_crossed_edges (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    {t h B ε : ℝ} (ht : 0<t) (hh : 0<h) (hB : 0≤B) (hsmall : 3348*t*B≤1) (hr : 2*ε≤t*h)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤ε) :
    let u := pathPauliDisorderShell ω n
    (crossed c).card≤(weakEdges u h).card+(exceptionalEdges u B).card := by
  classical
  intro u
  let W := weakEdges u h∪exceptionalEdges u B
  have hh' := crossed_from_detectable ω C c W ht hh hB subset_union_left
    (fun a e he => rotated_cap_at_row a u (fun hb => he (mem_union_right _ hb))) hsmall 0 z hf
    (fun a D c' he => by rw [empty_detectable_of_fit _ D c' _ _ _ hr z hz he,card_empty])
  simp only [Nat.mul_zero,Nat.add_zero] at hh'
  exact hh'.trans (card_union_le ..)

#print axioms fine_crossed_edges
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
