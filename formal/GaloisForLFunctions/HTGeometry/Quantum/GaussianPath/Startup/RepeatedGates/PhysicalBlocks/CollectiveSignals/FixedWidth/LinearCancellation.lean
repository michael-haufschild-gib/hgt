import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PacketData
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathOverlap

/-! # A triple reporter annihilates the entire two-local tangent space -/

open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
variable {n : ℕ}

theorem tripleSites_card {e f : Fin (n+1)} (hm : e.succ=f.castSucc) : (tripleSites e f).card=3 := by
  have hl := e.castSucc_lt_succ
  have hr : e.succ<f.succ := hm ▸ f.castSucc_lt_succ
  simp [tripleSites,hl.ne,hr.ne,(hl.trans hr).ne]

/-- An interaction missing the reporter commutes with it. An interaction
touching it still misses another packet site, whose onsite flip reverses
the input and leaves the commutator invariant. -/
theorem two_site_linear_transfer_zero {e f : Fin (n+1)} (hm : e.succ=f.castSucc)
    {i : Fin (n+2)} (hi : i∈tripleSites e f) (X : Reg (n+2)) (T : Finset (Fin (n+2)))
    (hT : T.card≤2) (hX : IsSiteSupported T X) :
    ((packetProbe e i*X-X*packetProbe e i)*packetImage e f i).trace=0 := by
  have hP : IsSiteSupported {i} (packetProbe e i) := probe_supported i _
  by_cases h : i∈T
  · have miss : ∃ j∈tripleSites e f, j∉T := by
      by_contra! hall
      have hh := (card_le_card (show tripleSites e f⊆T from hall)).trans hT
      rw [tripleSites_card hm] at hh
      omega
    obtain ⟨j,hj,hjT⟩ := miss
    have hne : i≠j := fun he => hjT (he ▸ h)
    have hP' := IsSiteSupported.mono (singleton_subset_iff.mpr h) hP
    have hcomm := commute_of_isSiteSupported_disjoint (disjoint_singleton_right.mpr hjT)
      ((hP'.matrix_mul hX).add (hX.matrix_mul hP').neg) (probe_supported j (tripleAxis e j))
    apply trace_zero_of_flip _ _ (packetProbe e j) _ (finitePauliMatrix_mul_self _)
      (packetImage_flip hm hi hj hne)
    simpa only [sub_eq_add_neg,packetProbe] using hcomm
  · have he := (commute_of_isSiteSupported_disjoint (disjoint_singleton_left.mpr h) hP hX).eq
    rw [he,sub_self,zero_mul,trace_zero]

/-- The linear coefficient of the three-site transfer is identically zero
for every physical path Hamiltonian, without any calibration restrictions. -/
theorem path_linear_transfer_zero {e f : Fin (n+1)} (hm : e.succ=f.castSucc)
    {i : Fin (n+2)} (hi : i∈tripleSites e f) (u : PathShell n) :
    ((packetProbe e i*pathHamiltonian u-pathHamiltonian u*packetProbe e i)*packetImage e f i).trace=0 := by
  rw [pathHamiltonian_eq_sum,Matrix.mul_sum,Matrix.sum_mul,←sum_sub_distrib,Matrix.sum_mul,trace_sum]
  apply sum_eq_zero
  intro l _
  apply two_site_linear_transfer_zero hm hi _ (labelSupport (pathWord l)) (pathWord_support_card_le_two l)
  apply IsSiteSupported.complex_smul
  exact finitePauliMatrix_isSiteSupported_of_eq_none _ _ fun v hv =>
    not_ne_iff.mp (fun h => hv (mem_labelSupport.mpr h))

#print axioms path_linear_transfer_zero
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
