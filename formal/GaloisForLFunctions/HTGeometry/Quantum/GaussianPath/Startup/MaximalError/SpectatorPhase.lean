import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.DisjointSites

/-! # A unimodular spectator phase for every packet configuration -/
open Matrix
open scoped Matrix.Norms.L2Operator Pointwise
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Compressing on the packet sites preserves the spectator. One eigenvalue
of that unitary tests every diagonal entry of the packet simultaneously. -/
theorem spectator_phase {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    {Y X : Reg N} (hy : IsSiteSupported T Y) (hx : IsSiteSupported S X)
    (hu : Y ∈ unitary _) : ∃ z : ℂ, ‖z‖=1 ∧
      ∀ w, ‖z-X w w‖ ≤ ‖Y-X‖ := by
  obtain ⟨z,hz,h⟩ := FirstAscent.disjoint_unitary_phase hd hx hy hu
  refine ⟨z,hz,fun w => ?_⟩
  have he := norm_entry_le_l2_opNorm (X-z • 1) w w
  simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
    norm_sub_rev (X w w) z,norm_sub_rev X Y] using he.trans h

/-- Deleting the packet couplings costs the elapsed time times their
operator norm. Unitarity keeps the same comparison phase on the unit circle. -/
theorem perturbed_packet_phase {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    (H K J : selfAdjoint (Reg N)) (hK : IsSiteSupported S K.val) (hJ : IsSiteSupported T J.val)
    (C : Reg N) (hC : IsSiteSupported T C) (hu : C ∈ unitary _) (t : ℝ) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ w, ‖z-(unitaryEvolution K.val t) w w‖ ≤
      ‖unitaryEvolution H.val t-C‖+|t| *‖H.val-(J.val+K.val)‖ := by
  let V : Reg N := unitaryEvolution J.val (-t)
  let U : Reg N := unitaryEvolution J.val t
  let X : Reg N := unitaryEvolution K.val t
  have hinv : V*U=1 := by
    simpa only [V,U,zero_sub,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using
      unitaryEvolution_sub_mul J 0 t
  have huv : V ∈ unitary _ := unitaryEvolution_mem_unitary J.property _
  have hfac : unitaryEvolution (J.val+K.val) t=U*X :=
    unitaryEvolution_add_of_isSiteSupported_disjoint hd.symm hJ hK t
  have hVC : IsSiteSupported T (V*C) := (isSiteSupported_unitaryEvolution hJ (-t)).matrix_mul hC
  have hX : IsSiteSupported S X := isSiteSupported_unitaryEvolution hK t
  have hunit : V*C ∈ unitary (Reg N) := (unitary (Reg N)).mul_mem huv hu
  obtain ⟨z,hz,h⟩ := spectator_phase (Y:=V*C) (X:=X) hd hVC hX hunit
  have he : V*C-X=V*(C-U*X) := by rw [mul_sub,←mul_assoc,hinv,one_mul]
  have hdif : ‖V*C-X‖=‖unitaryEvolution (J.val+K.val) t-C‖ := by
    rw [he,CStarRing.norm_mem_unitary_mul _ huv,←hfac,norm_sub_rev C]
  have herr := norm_unitaryEvolution_sub_le H.val (J.val+K.val) H.2 (J.2.add K.2) t
  refine ⟨z,hz,fun w => (h w).trans ?_⟩
  rw [hdif]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H.val t) C).trans
  rw [norm_sub_rev (unitaryEvolution (J.val+K.val) t) (unitaryEvolution H.val t),add_comm]
  exact add_le_add le_rfl herr

#print axioms perturbed_packet_phase
end
end GaloisForLFunctions.HTGeometry.MaximalError
