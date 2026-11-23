import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison
import Mathlib.Analysis.CStarAlgebra.Spectrum

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
  letI : CStarAlgebra (Reg N) := {}
  obtain ⟨z,hz⟩ := spectrum.nonempty Y
  refine ⟨z,spectrum.norm_eq_one_of_unitary hu hz,fun w => ?_⟩
  have hs : z-X w w ∈ spectrum ℂ (Y-algebraMap ℂ (Reg N) (X w w)) := by
    rw [←spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hz (Set.mem_singleton _)
  have hn := spectrum.norm_le_norm_of_mem hs
  rw [Algebra.algebraMap_eq_smul_one] at hn
  exact hn.trans (disjoint_site_diagonal_bound hd.symm hy hx w)

/-- Deleting the packet couplings costs the elapsed time times their
operator norm. Unitarity keeps the same comparison phase on the unit circle. -/
theorem perturbed_packet_phase {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    (H K J : selfAdjoint (Reg N)) (hK : IsSiteSupported S K.val) (hJ : IsSiteSupported T J.val)
    (C : Reg N) (hC : IsSiteSupported T C) (hu : C ∈ unitary _) (t : ℝ) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ w, ‖z-(unitaryEvolution K.val t) w w‖ ≤
      ‖unitaryEvolution H.val t-C‖+|t| *‖H.val-(J.val+K.val)‖ := by
  let V := unitaryEvolution J.val (-t)
  let U := unitaryEvolution J.val t
  let X := unitaryEvolution K.val t
  have hinv : V*U=1 := by
    simpa only [V,U,zero_sub,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using
      unitaryEvolution_sub_mul J 0 t
  have huv : V ∈ unitary _ := unitaryEvolution_mem_unitary J.property _
  have hfac : unitaryEvolution (J.val+K.val) t=U*X :=
    unitaryEvolution_add_of_isSiteSupported_disjoint hd.symm hJ hK t
  obtain ⟨z,hz,h⟩ := spectator_phase hd ((isSiteSupported_unitaryEvolution hJ (-t)).matrix_mul hC)
    (isSiteSupported_unitaryEvolution hK t) (mul_mem huv hu)
  refine ⟨z,hz,fun w => (h w).trans ?_⟩
  have he : V*C-X=V*(C-U*X) := by rw [mul_sub,←mul_assoc,hinv,one_mul]
  rw [he,CStarRing.norm_mem_unitary_mul _ huv,←hfac,norm_sub_rev C]
  have herr := norm_unitaryEvolution_sub_le H.val (J.val+K.val) H.2 (J.2.add K.2) t
  rw [norm_sub_rev] at herr
  exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H.val t) _).trans
    ((add_le_add_right herr _).trans_eq (add_comm ..))

#print axioms perturbed_packet_phase
end
end GaloisForLFunctions.HTGeometry.MaximalError
