import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound

/-! # Error from replacing weakly coupled sites by longitudinal fields -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Every term incident to the site is within η of a pure longitudinal field. -/
def isolatedLongitudinalSite {n : ℕ} (u : PathShell n) (q η : ℝ) (s : Fin (n+2)) : Prop :=
  ∀ l, pathIncident s l → |u l-longitudinalPacket Finset.univ q l| ≤ η

private theorem packet_coefficient_outside {n : ℕ} (S : Finset (Fin (n+2))) (q : ℝ) (l : PathLabel n)
    (h : ¬PathWordSupportedIn S l) : longitudinalPacket S q l = 0 := by
  rcases l with ⟨s,a⟩ | e
  · have hout : s ∉ S := by
      intro hs
      apply h
      intro v hv
      have hne : v ≠ s := by intro he; subst v; exact hv hs
      simp [pathWord,onsiteWord,hne]
    simp [longitudinalPacket,hout]
  · rfl

/-- The longitudinal packet is unchanged by restriction to its sites. -/
theorem longitudinalPacket_restriction {n : ℕ} (S : Finset (Fin (n+2))) (q : ℝ) :
    pathHamiltonianOnSites S (longitudinalPacket S q) = pathHamiltonian (longitudinalPacket S q) := by
  classical
  rw [pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites]
  apply congrArg pathHamiltonian
  ext l
  change (if PathWordSupportedIn S l then _ else 0) = _
  by_cases h : PathWordSupportedIn S l
  · rw [if_pos h]
  · rw [if_neg h,packet_coefficient_outside S q l h]

/-- The coefficient error vanishes outside the incident labels and is at
most η on each of them, including when selected sites are adjacent. -/
theorem isolated_field_coefficient_bounds {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) (q η : ℝ)
    (hs : ∀ s ∈ S, isolatedLongitudinalSite u q η s) :
    let W := S.biUnion pathIncidentLabels
    let err (l : PathLabel n) := |u l-pathPacketReferenceCoeff Sᶜ S u (longitudinalPacket S q) l|
    (∀ l ∈ W, err l ≤ η) ∧ ∀ l ∉ W, err l = 0 := by
  classical
  let p := longitudinalPacket S q
  let W := S.biUnion pathIncidentLabels
  have hp (l) : (if PathWordSupportedIn S l then p l else 0) = p l := by
    split_ifs with h
    · rfl
    · exact (packet_coefficient_outside S q l h).symm
  have ho (l) (hl : l ∉ W) : p l = 0 := by
    rcases l with ⟨s,a⟩ | e
    · have hs : s ∉ S := by
        intro hS
        apply hl
        exact Finset.mem_biUnion.mpr ⟨s,hS,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
      simp [p,longitudinalPacket,hs]
    · rfl
  have hc (l) (hl : l ∈ W) : |u l-pathPacketReferenceCoeff Sᶜ S u p l| ≤ η := by
    obtain ⟨s,hS,hl⟩ := Finset.mem_biUnion.mp hl
    have hi : pathIncident s l := (Finset.mem_filter.mp hl).2
    have hcomp : ¬PathWordSupportedIn Sᶜ l := fun h =>
      pathWord_ne_none_of_incident hi (h s (by simpa using hS))
    have he : p l = longitudinalPacket Finset.univ q l := by
      rcases l with ⟨v,a⟩ | e
      · change v=s at hi
        simp [p,longitudinalPacket,hi,hS]
      · rfl
    rw [pathPacketReferenceCoeff,if_neg hcomp,hp l,zero_add,he]
    exact hs s hS l hi
  have hz (l) (hl : l ∉ W) : |u l-pathPacketReferenceCoeff Sᶜ S u p l| = 0 := by
    rw [pathPacketReferenceCoeff,if_pos (path_supported_compl_of_not_incident S l hl),
      hp l,ho l hl,add_zero,sub_self,abs_zero]
  exact ⟨hc,hz⟩

/-- Replacing all interactions on nearly isolated sites by their uniform
longitudinal field costs at most 21η in operator norm per site. -/
theorem isolated_field_replacement_error {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) (q η : ℝ)
    (hη : 0 ≤ η) (hs : ∀ s ∈ S, isolatedLongitudinalSite u q η s) :
    ‖pathHamiltonian u-(pathHamiltonianOnSites Sᶜ u + pathHamiltonian (longitudinalPacket S q))‖ ≤
      21*(S.card:ℝ)*η := by
  classical
  let p := longitudinalPacket S q
  let W := S.biUnion pathIncidentLabels
  obtain ⟨hc,hz⟩ := isolated_field_coefficient_bounds u S q η hs
  have herr := norm_pathHamiltonian_sub_packetReference_le Sᶜ S u p
  have hres : pathHamiltonianOnSites S p = pathHamiltonian p := longitudinalPacket_restriction S q
  rw [pathHamiltonianPacketReference,hres] at herr
  rw [← Finset.sum_subset (Finset.subset_univ W) (fun l _ hl => hz l hl)] at herr
  refine herr.trans ((Finset.sum_le_sum hc).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hη
  exact_mod_cast pathIncident_union_card S

/-- A circuit missing m good sites pays at least the packet's spectral
deficit after subtracting the total error on their incident terms. -/
theorem isolated_field_circuit_deficit {n : ℕ} (u : PathShell n) (q η : ℝ) (hq : 0 < q) (hη : 0 ≤ η)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (S : Finset (Fin (n+2))) (hS : 0 < S.card)
    (hd : Disjoint S C.touchedSites) (hs : ∀ s ∈ S, isolatedLongitudinalSite u q η s)
    (t : ℝ) :
    1 ≤ ‖unitaryEvolution (pathHamiltonian u) t-z • (C.eval : Reg (n+2))‖ +
      |t| * (21*(S.card:ℝ)*η) + |t*((S.card:ℝ)*q)-Real.pi/2| := by
  let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let J : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonianOnSites Sᶜ u,isSelfAdjoint_pathHamiltonianOnSites _ _⟩
  let K : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (longitudinalPacket S q),isSelfAdjoint_pathHamiltonian _⟩
  have hK : IsSiteSupported S K.val := by
    change IsSiteSupported S (pathHamiltonian (longitudinalPacket S q))
    rw [← longitudinalPacket_restriction]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  have hC := (C.isSiteSupported_touchedSites.complex_smul z).mono (show C.touchedSites ⊆ Sᶜ from
    fun s hs => Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp hd h hs))
  obtain ⟨c,hc⟩ := packet_scalar_distance_with_spectator disjoint_compl_right H K J hK
    (pathHamiltonianOnSites_isSiteSupported _ _) _ hC t
  have hf := longitudinal_packet_scalar_floor S hS q hq t c
  apply hf.trans
  exact add_le_add (hc.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (isolated_field_replacement_error u S q η hη hs) (abs_nonneg _)))) le_rfl

#print axioms isolated_field_circuit_deficit
end
end GaloisForLFunctions.HTGeometry
