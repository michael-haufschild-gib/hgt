import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.AngularMesh
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.PacketSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.SpectatorPhase

/-! # Near-maximal error forced by a packet of untouched spins -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- A full turn of magnetization phases places a physical eigenphase near
the antipode of a spectator phase. The losses are the angular mesh and the
interaction removed on the untouched sites. -/
theorem packet_deficit {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2)))
    {q δ t : ℝ} (hq : 0 < q) (hδ : 0 ≤ δ) (ht : 0 < t) (hspan : π ≤ (t*q)*S.card)
    (hs : ∀ i∈S, isolatedLongitudinalSite u q δ i)
    (C : TwoQubitCircuit (n+2)) (hd : Disjoint S C.touchedSites) (b : ℂ) (hb : ‖b‖=1) :
    2 ≤ ‖unitaryEvolution (pathHamiltonian u) t-b • (C.eval : Reg (n+2))‖+
      t*(21*(S.card:ℝ)*δ)+2*(t*q) := by
  let H : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  let p := longitudinalPacket S q
  let K : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian p⟩
  let J : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites Sᶜ u⟩
  have hK : IsSiteSupported S K.val := by
    change IsSiteSupported S (pathHamiltonian p)
    rw [←longitudinalPacket_restriction S q]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  have hC := (C.isSiteSupported_touchedSites.complex_smul b).mono (show C.touchedSites ⊆ Sᶜ from
    fun _ hi => mem_compl.mpr (fun h => disjoint_left.mp hd h hi))
  have hu : b • (C.eval : Reg (n+2)) ∈ unitary _ := by
    have hc : star b*b=1 := by rw [Complex.star_def,Complex.conj_mul',hb]; norm_num
    apply Unitary.mem_iff.mpr
    simp only [star_smul,smul_mul_smul_comm,C.eval.property.1,C.eval.property.2,hc,
      (mul_comm b (star b)).trans hc,one_smul,and_self]
  obtain ⟨z,hz,h⟩ := perturbed_packet_phase disjoint_compl_right H K J hK
    (pathHamiltonianOnSites_isSiteSupported _ _) _ hC hu t
  obtain ⟨j,hj,hnear⟩ := packet_phase_mesh S.card (mul_pos ht hq) hspan (-z) ((norm_neg _).trans hz)
  obtain ⟨w,hw⟩ := packet_weight_phase S q t hj
  have hw' := h w
  change ‖z-(unitaryEvolution (pathHamiltonian (longitudinalPacket S q)) t) w w‖ ≤ _ at hw'
  rw [hw,←mul_assoc t q,abs_of_pos ht] at hw'
  let v := Complex.exp (((-((t*q)*((S.card:ℝ)-2*j)):ℝ):ℂ)*Complex.I)
  have hdia : ‖z-(-z)‖=2 := by rw [sub_neg_eq_add,←two_mul,norm_mul,hz,mul_one]; norm_num
  have tri := norm_sub_le_norm_sub_add_norm_sub z v (-z)
  rw [hdia,norm_sub_rev v] at tri
  have herr := mul_le_mul_of_nonneg_left (isolated_field_replacement_error u S q δ hδ hs) ht.le
  change t*‖H.val-(J.val+K.val)‖ ≤ _ at herr
  change ‖z-v‖ ≤ ‖unitaryEvolution H.val t-b • (C.eval : Reg (n+2))‖+t*‖H.val-(J.val+K.val)‖ at hw'
  change ‖-z-v‖ ≤ _ at hnear
  change 2 ≤ ‖unitaryEvolution H.val t-b • (C.eval : Reg (n+2))‖+_+_
  linarith only [tri,hnear,hw',herr]

#print axioms packet_deficit
end
end GaloisForLFunctions.HTGeometry.MaximalError
