import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.PacketApproach
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # Recurrence to prescribed eigenphases in physical coordinates -/

open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Every prescribed unit eigenphase packet is approached in every coordinate
up to one common phase. The admissible dates have bounded gaps. -/
theorem coordinate_hits {n d : ℕ} (e : (Fin n→Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (hm : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (f : (Fin n→Bool) → ℂ) (hf : ∀ i, ‖f i‖=1) {η : ℝ} (he : 0<η) :
    ∃ G : ℝ, 0≤G ∧ ∀ a : ℝ, ∃ v∈Icc a (a+G), ∃ z : ℂ, ‖z‖=1 ∧
      ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i v-z*f i‖<η := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let g := f ∘ e.symm
  have hg : ∀ j, ‖g j‖=1 := fun j => hf (e.symm j)
  obtain ⟨G,hG,hh⟩ := syndetic_packet_approach e H.2.isHermitian (hm.comp_equiv e.symm) g hg he
  refine ⟨G,hG,fun a => ?_⟩
  obtain ⟨v,hv,z,hz,her⟩ := hh a
  refine ⟨v,hv,z,hz,fun i => ?_⟩
  have hgf : g ∘ e = f := funext fun i => congrArg f (e.symm_apply_apply i)
  have hp : (spectralPhaseUnitary e V g hg : Reg n)=V.val*diagonal f*star V.val := by
    change V.val*diagonal (g ∘ e)*star V.val=_
    rw [hgf]
  change ‖unitaryEvolution H.val v-z • (spectralPhaseUnitary e V g hg : Reg n)‖<η at her
  rw [hp,unitaryEvolution_spectral H.2.isHermitian] at her
  change ‖V.val*diagonal (fun j => anchorPhase H.2.isHermitian.eigenvalues j v)*star V.val-
    z • (V.val*diagonal f*star V.val)‖<η at her
  rw [←Matrix.smul_mul,←Matrix.mul_smul,←diagonal_smul,←sub_mul,←mul_sub,diagonal_sub,
    l2_opNorm_unitary_conj_eq V.property,l2_opNorm_diagonal] at her
  exact (norm_le_pi_norm (fun j => anchorPhase H.2.isHermitian.eigenvalues j v-z*f j) i).trans_lt her

#print axioms coordinate_hits
end
end GaloisForLFunctions.HTGeometry.SpectralArcs
