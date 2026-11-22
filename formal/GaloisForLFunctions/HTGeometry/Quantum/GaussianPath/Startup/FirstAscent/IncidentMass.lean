import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms

/-! # Absolute interaction mass lost by deleting sites -/
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

/-- Only Pauli words incident to a deleted site contribute to the norm
error. Keeping their individual magnitudes permits order-statistic bounds. -/
theorem incident_deletion {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) :
    ‖pathHamiltonian u-pathHamiltonianOnSites Sᶜ u‖ ≤
      ∑ l ∈ S.biUnion pathIncidentLabels, |u l| := by
  classical
  let W := S.biUnion pathIncidentLabels
  have hmiss (l) (hl : l ∉ W) := path_supported_compl_of_not_incident S l hl
  have h := norm_pathHamiltonian_sub_packetReference_le Sᶜ ∅ u 0
  have hR : pathHamiltonianPacketReference Sᶜ ∅ u 0=pathHamiltonianOnSites Sᶜ u := by
    simp [pathHamiltonianPacketReference,pathHamiltonianOnSites]
  rw [hR] at h
  apply h.trans
  rw [←Finset.sum_subset (Finset.subset_univ W) (fun l _ hl => by simp [pathPacketReferenceCoeff,hmiss l hl])]
  apply Finset.sum_le_sum
  intro l _
  by_cases hl : PathWordSupportedIn Sᶜ l <;> simp [pathPacketReferenceCoeff,hl]

end
end GaloisForLFunctions.HTGeometry.FirstAscent
