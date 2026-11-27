import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.Propagation.FinitePatch
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.Propagation.Interval
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.CorrectedReporter
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SelectedOverlap

/-! # A local contraction for the calibrated physical bond signal -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon RepeatedGates.PhysicalBlocks.CollectiveSignals
open private transported_probe from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.CorrectedReporter
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ
variable {n : ℕ}

/-- Cutting away the exterior at radius p gives a contraction on p+1
neighbor layers. Its error depends on the measured interaction mass in
the patch, even when neither boundary bond is weak. -/
theorem local_bond_reporter (u : PathShell n) (e : Fin (n+1)) (p : ℕ) (t : ℝ) (ht : 0≤t) :
    let U := unitaryEvolution (pathHamiltonian u) t
    let T := bondNeighborhood e p
    let E := ∑ l∈T.biUnion pathIncidentLabels, |u l|
    ∃ X : Reg n, IsSiteSupported (bondNeighborhood e (p+1)) X ∧ ‖X‖≤1 ∧
      ‖Uᴴ*bondOutput e*U*bondInput e-X‖≤2*(2*E)^p*t^p := by
  intro U T E
  let H := pathHamiltonian u-pathHamiltonianOnSites Tᶜ u
  let W := unitaryEvolution H t
  let M := bondNeighborhood e (p+1)
  have hH : IsSelfAdjoint H := (isSelfAdjoint_pathHamiltonian u).sub (isSelfAdjoint_pathHamiltonianOnSites Tᶜ u)
  have hW := unitaryEvolution_mem_unitary hH t
  have hl : e.castSucc∈M := bondNeighborhood_contains e (p+1) (mem_insert_self ..)
  have hr : e.succ∈M := bondNeighborhood_contains e (p+1) (mem_insert_of_mem (mem_singleton_self _))
  have hs : IsSiteSupported M H := by
    dsimp only [M,H]
    rw [bondNeighborhood_succ]
    exact incident_difference_supported u T
  have hW' := isSiteSupported_unitaryEvolution hs t
  have hX := ((hW'.conjTranspose.matrix_mul (bond_output_supported hl)).matrix_mul hW').matrix_mul
    (bond_input_supported hl hr)
  refine ⟨Wᴴ*bondOutput e*W*bondInput e,hX,?_,?_⟩
  · have hnorm : ‖star W*bondOutput e*W‖=1 := by
      rw [CStarRing.norm_mul_mem_unitary _ hW,
        CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hW),bondOutput,norm_finitePauliMatrix]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (bond_input_norm e) (norm_nonneg _)).trans_eq
      ((mul_one _).trans hnorm))
  · have he := local_transport_error u ({e.castSucc,e.succ}:Finset _) (bond_output_supported (mem_insert_self ..)) p t ht
    change ‖transported ((-Complex.I) • pathHamiltonian u) t (bondOutput e)-
      transported ((-Complex.I) • H) t (bondOutput e)‖≤2*((2*E)^p*‖bondOutput e‖)*t^p at he
    rw [transported_probe _ _ (isSelfAdjoint_pathHamiltonian u),transported_probe H _ hH,
      show ‖bondOutput e‖=1 from norm_finitePauliMatrix _,mul_one] at he
    rw [←sub_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (bond_input_norm e) (norm_nonneg _)).trans
      ((mul_one _).le.trans he))

#print axioms local_bond_reporter
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
