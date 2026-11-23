import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PacketData
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # A local reporter for the actual physical evolution at small angles -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
variable {n : ℕ}

def packetTest (e f : Fin (n+1)) (i : Fin (n+2)) (t : ℝ) :=
  let V := unitaryEvolution (tripleGenerator e f) t
  star V*packetProbe e i*V*packetImage e f i

theorem packetTest_supported {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (t : ℝ) : IsSiteSupported (tripleSites e f) (packetTest e f i t) := by
  have hV := isSiteSupported_unitaryEvolution (tripleGenerator_supported hm) t
  have hP := IsSiteSupported.mono (singleton_subset_iff.mpr hi) (onsite_probe_supported i (tripleAxis e i))
  exact IsSiteSupported.matrix_mul (IsSiteSupported.matrix_mul
    (IsSiteSupported.matrix_mul (IsSiteSupported.conjTranspose hV) hP) hV) (packetImage_supported hm hi)

theorem packetTest_unitary {e f : Fin (n+1)} (hm : e.succ=f.castSucc) (i : Fin (n+2)) (t : ℝ) :
    packetTest e f i t∈unitary _ := by
  have hV := unitaryEvolution_mem_unitary (tripleGenerator_selfAdjoint e f) t
  exact mul_mem (mul_mem (mul_mem (Unitary.star_mem hV) (finitePauliMatrix_mem_unitary _)) hV)
    (packetImage_unitary hm i)

/-- The exterior Hamiltonian may be arbitrarily large. Only its couplings
to the tested triple enter the error in the Heisenberg reporter. -/
theorem packetTest_local_error {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) {δ : ℝ} (hδ : 0≤δ) (t : ℝ)
    (hbox : ∀ l∈(tripleSites e f).biUnion pathIncidentLabels,
      |u l-tripleField e f (1/sqrt 2) l|≤δ) :
    let U := unitaryEvolution (pathHamiltonian u) t
    ‖star U*packetProbe e i*U*packetImage e f i-packetTest e f i t‖≤126*|t|*δ := by
  intro U
  let S := tripleSites e f
  let H := pathHamiltonianOnSites Sᶜ u
  let J := tripleGenerator e f
  let V := unitaryEvolution J t
  let E := unitaryEvolution H t
  let P := packetProbe e i
  have hH := isSelfAdjoint_pathHamiltonianOnSites Sᶜ u
  have hJ := tripleGenerator_selfAdjoint e f
  have hU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hE := unitaryEvolution_mem_unitary hH t
  have hV := unitaryEvolution_mem_unitary hJ t
  have hHS := pathHamiltonianOnSites_isSiteSupported Sᶜ u
  have hcomm : Commute E P := commute_of_isSiteSupported_disjoint
    (Finset.disjoint_singleton_right.mpr (fun h => Finset.mem_compl.mp h hi))
    (isSiteSupported_unitaryEvolution hHS t) (onsite_probe_supported i _)
  have hfactor : unitaryEvolution (H+J) t=E*V :=
    unitaryEvolution_add_of_isSiteSupported_disjoint disjoint_compl_left hHS (tripleGenerator_supported hm) t
  have herr := triple_local_error u (1/sqrt 2) δ hδ hbox
  rw [one_div_mul_cancel (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne',Complex.ofReal_one,one_smul] at herr
  have hdist := norm_unitaryEvolution_sub_le (pathHamiltonian u) (H+J) (isSelfAdjoint_pathHamiltonian u) (hH.add hJ) t
  rw [hfactor] at hdist
  have hdiff : ‖U-E*V‖≤|t|*(63*δ) := hdist.trans (mul_le_mul_of_nonneg_left herr (abs_nonneg _))
  have hchange := unitary_conjugation_norm_sub_le (star U) (star (E*V)) P
    (Unitary.star_mem hU) (Unitary.star_mem (mul_mem hE hV))
  have hlocal : star (E*V)*P*(E*V)=star V*P*V := by
    rw [star_mul]
    calc _ = star V*(star E*(P*E))*V := by simp only [mul_assoc]
         _ = _ := by rw [←hcomm.eq,←mul_assoc (star E) E,Unitary.star_mul_self_of_mem hE,one_mul]
  simp only [star_star,←star_sub,norm_star,hlocal] at hchange
  rw [show ‖P‖=1 from norm_finitePauliMatrix _,mul_one] at hchange
  change ‖star U*P*U*packetImage e f i-(star V*P*V)*packetImage e f i‖≤_
  rw [←sub_mul,CStarRing.norm_mul_mem_unitary _ (packetImage_unitary hm i)]
  exact hchange.trans ((mul_le_mul_of_nonneg_left hdiff (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

#print axioms packetTest_local_error
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
