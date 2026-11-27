import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.IncidentSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.LocalTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.IncidentCommutators
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal

/-! # A local reporter with quadratic accuracy on fixed-width calibration boxes -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open LocalPatches SpanningDensity.BondTransfer
open private isolated_packet_reporter from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.LocalTest
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance reporterAlgebra (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

private abbrev perturb (e f : Fin (n+1)) (u : PathShell n) :=
  (-Complex.I) • pathHamiltonian (packetPerturbation e f u)

/-- Add the first-order evolution of the measured perturbation. This
restores the local operator while leaving its trace exactly unchanged. -/
def correctedReporter (e f : Fin (n+1)) (i : Fin (n+2)) (u : PathShell n) (t : ℝ) :=
  packetTest e f i t+(t • bracketStep (perturb e f u) (packetProbe e i))*packetImage e f i

theorem correctedReporter_trace {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) (t : ℝ) :
    (correctedReporter e f i u t).trace=(packetTest e f i t).trace := by
  have h := path_linear_transfer_zero hm hi (packetPerturbation e f u)
  simp only [correctedReporter,perturb,bracketStep,Matrix.mul_smul,Matrix.smul_mul,←smul_sub,
    Matrix.trace_add,Matrix.trace_smul,h,smul_zero,add_zero]

theorem correctedReporter_supported {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) (t : ℝ) :
    IsSiteSupported (incidentSites (tripleSites e f)) (correctedReporter e f i u t) := by
  let S := incidentSites (tripleSites e f)
  have hT : tripleSites e f⊆S := subset_union_left
  have hP : IsSiteSupported S (packetProbe e i) := IsSiteSupported.mono
    ((singleton_subset_iff.mpr hi).trans hT) (probe_supported i _)
  have hJ : IsSiteSupported S (perturb e f u) :=
    IsSiteSupported.complex_smul _ (packetPerturbation_supported hm u)
  have hc : IsSiteSupported S (bracketStep (perturb e f u) (packetProbe e i)) := by
    rw [bracketStep,sub_eq_add_neg]
    exact (hP.matrix_mul hJ).add (hJ.matrix_mul hP).neg
  exact (IsSiteSupported.mono hT (packetTest_supported hm hi t)).add
    ((IsSiteSupported.complex_smul (t:ℂ) hc).matrix_mul (IsSiteSupported.mono hT (packetImage_supported hm hi)))

private theorem transported_probe (H P : Reg (n+2)) (hH : IsSelfAdjoint H) (t : ℝ) :
    transported ((-Complex.I) • H) t P=star (unitaryEvolution H t)*P*unitaryEvolution H t := by
  rw [←EigenlineSignals.adjoint_evolution ⟨H,hH⟩ t]
  simp only [transported,unitaryEvolution,smul_neg,neg_smul]

/-- The quadratic remainder is proportional to the local perturbation
and the mass incident to its support, independently of the exterior. -/
theorem correctedReporter_error {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i : Fin (n+2)}
    (hi : i∈tripleSites e f) (u : PathShell n) (t : ℝ) (ht : 0≤t) :
    let U := unitaryEvolution (pathHamiltonian u) t
    let J := perturb e f u
    let S := incidentSites (tripleSites e f)
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    ‖star U*packetProbe e i*U*packetImage e f i-correctedReporter e f i u t‖≤
      t^2*(4*‖J‖*(2*E+‖J‖)) := by
  intro U J S E
  let P := packetProbe e i
  let B := packetImage e f i
  let H := pathHamiltonian u
  let H₀ := pathHamiltonianOnSites (tripleSites e f)ᶜ u+tripleGenerator e f
  have hH₀ : IsSelfAdjoint H₀ := (isSelfAdjoint_pathHamiltonianOnSites _ u).add (tripleGenerator_selfAdjoint e f)
  have hP : IsSiteSupported S P := IsSiteSupported.mono
    ((singleton_subset_iff.mpr hi).trans (show tripleSites e f⊆S from subset_union_left)) (probe_supported i _)
  have hJ : J∈skewAdjoint (Reg (n+2)) := by
    change star ((-Complex.I) • pathHamiltonian _)=-((-Complex.I) • pathHamiltonian _)
    rw [star_smul,(isSelfAdjoint_pathHamiltonian _).star_eq,star_neg,Complex.star_def,Complex.conj_I,
      neg_neg,neg_smul,neg_neg]
  have h := local_erasure u S P J hP (IsSiteSupported.complex_smul _ (packetPerturbation_supported hm u)) hJ t ht
  have hk : (-Complex.I) • H-J=(-Complex.I) • H₀ := by
    dsimp only [J,perturb,H,H₀]
    rw [packetPerturbation_eq,←smul_sub,sub_sub_cancel]
  change ‖transported ((-Complex.I) • H) t P-transported ((-Complex.I) • H-J) t P-
    t • bracketStep J P‖≤t^2*(4*‖P‖*‖J‖*(2*E+‖J‖)) at h
  have hiso := isolated_packet_reporter hm hi u t
  rw [hk,transported_probe H P (isSelfAdjoint_pathHamiltonian u),transported_probe H₀ P hH₀,hiso,
    show ‖P‖=1 from norm_finitePauliMatrix _,mul_one] at h
  have heq : star U*P*U*B-correctedReporter e f i u t=
      (star U*P*U-star (unitaryEvolution (tripleGenerator e f) t)*P*
        unitaryEvolution (tripleGenerator e f) t-t • bracketStep J P)*B := by
    simp only [correctedReporter,packetTest,sub_mul]
    abel
  change ‖star U*P*U*B-correctedReporter e f i u t‖≤_
  rw [heq,CStarRing.norm_mul_mem_unitary _ (packetImage_unitary hm i)]
  exact h

#print axioms correctedReporter_trace
#print axioms correctedReporter_error
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
