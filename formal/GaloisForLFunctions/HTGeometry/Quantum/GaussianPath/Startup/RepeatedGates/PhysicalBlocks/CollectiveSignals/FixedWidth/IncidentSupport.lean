import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.LinearCancellation
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport

/-! # Support of the perturbation from a calibrated signaling triple -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open private triple_supported triple_field_sum from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.LocalReplacement
noncomputable section
variable {n : ℕ}

/-- Sites used by terms meeting S, including S itself. On a path this
adds at most the two adjacent sites to an interval. -/
def incidentSites (S : Finset (Fin (n+2))) :=
  S ∪ (S.biUnion pathIncidentLabels).biUnion (fun l => labelSupport (pathWord l))

theorem incident_difference_supported (u : PathShell n) (S : Finset (Fin (n+2))) :
    IsSiteSupported (incidentSites S) (pathHamiltonian u-pathHamiltonianOnSites Sᶜ u) := by
  classical
  rw [pathHamiltonian_eq_sum,pathHamiltonianOnSites,←sum_sub_distrib]
  apply Finset.sum_induction _ _ (fun _ _ h₁ h₂ => IsSiteSupported.add h₁ h₂) (IsSiteSupported.zero _)
  intro l _
  by_cases h : l∈S.biUnion pathIncidentLabels
  · rw [←sub_smul]
    apply IsSiteSupported.complex_smul
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    by_contra hn
    exact hv (mem_union_right _ (mem_biUnion.mpr ⟨l,h,mem_labelSupport.mpr hn⟩))
  · rw [if_pos (path_supported_compl_of_not_incident S l h),sub_self]
    exact IsSiteSupported.zero _

/-- Actual couplings minus the exterior and the two calibrated bonds. -/
def packetPerturbation (e f : Fin (n+1)) (u : PathShell n) : PathShell n :=
  u-(pathShellOnSites (tripleSites e f)ᶜ u+WithLp.toLp 2 (tripleField e f (1/sqrt 2)))

theorem packetPerturbation_eq (e f : Fin (n+1)) (u : PathShell n) :
    pathHamiltonian (packetPerturbation e f u)=
      pathHamiltonian u-(pathHamiltonianOnSites (tripleSites e f)ᶜ u+tripleGenerator e f) := by
  let v : PathShell n := WithLp.toLp 2 (tripleField e f (1/sqrt 2))
  have href : pathHamiltonian v=tripleGenerator e f := by
    rw [pathHamiltonian_eq_sum]
    have he := triple_field_sum e f (1/sqrt 2)
    rwa [div_mul_cancel₀ _ (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne',Complex.ofReal_one,one_smul] at he
  change pathHamiltonianLM n (u-(pathShellOnSites (tripleSites e f)ᶜ u+v))=_
  rw [map_sub,map_add]
  change pathHamiltonian u-(pathHamiltonian (pathShellOnSites (tripleSites e f)ᶜ u)+pathHamiltonian v)=_
  rw [←pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites,href]

theorem packetPerturbation_supported {e f : Fin (n+1)} (hm : e.succ=f.castSucc) (u : PathShell n) :
    IsSiteSupported (incidentSites (tripleSites e f)) (pathHamiltonian (packetPerturbation e f u)) := by
  rw [packetPerturbation_eq,←sub_sub,sub_eq_add_neg]
  exact (incident_difference_supported u _).add ((IsSiteSupported.mono subset_union_left (triple_supported hm)).neg)

#print axioms packetPerturbation_supported
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
