import GaloisForLFunctions.HTGeometry.Quantum.DisjointSiteCircuitApproximation
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Detecting an omitted tensor factor in a physical circuit -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Operators supported on a common set of sites form a subalgebra. -/
theorem IsSiteSupported.matrix_mul {n : ℕ} {S : Finset (Fin n)} {X Y : Reg n}
    (hx : IsSiteSupported S X) (hy : IsSiteSupported S Y) : IsSiteSupported S (X*Y) := by
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hx
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hy
  have he : liftLocalMatrix S B * liftLocalMatrix S C = liftLocalMatrix S (B*C) := by
    let Φ := Matrix.reindexAlgEquiv ℂ ℂ (configurationSplitEquiv (fun _ : Fin n => Bool) S)
    apply Φ.injective
    rw [map_mul]
    change Matrix.reindex _ _ _ * Matrix.reindex _ _ _ = Matrix.reindex _ _ _
    simp only [reindex_liftLocalMatrix_eq_kronecker_one,← Matrix.mul_kronecker_mul,mul_one]
  rw [he]
  exact isSiteSupported_liftLocalMatrix S _

/-- An arbitrary spectator Hamiltonian can be removed before testing a
scalar-distance witness on a disjoint packet. The perturbation costs the
operator norm of the generator error times elapsed time. -/
theorem packet_scalar_distance_with_spectator {n : ℕ} {S T : Finset (Fin n)} (hST : Disjoint S T)
    (H K J : selfAdjoint (Reg n)) (hK : IsSiteSupported S K.val) (hJ : IsSiteSupported T J.val)
    (C : Reg n) (hC : IsSiteSupported T C) (t : ℝ) :
    ∃ z : ℂ, ‖unitaryEvolution K.val t - z • (1:Reg n)‖ ≤
      ‖unitaryEvolution H.val t - C‖ + |t|*‖H.val-(J.val+K.val)‖ := by
  let V := unitaryEvolution J.val t
  let V' := unitaryEvolution J.val (-t)
  let U := unitaryEvolution K.val t
  have hprod : V'*V = 1 := by
    simpa only [V',V,zero_sub,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using
      unitaryEvolution_sub_mul J 0 t
  have hfac : unitaryEvolution (J.val+K.val) t = V*U :=
    unitaryEvolution_add_of_isSiteSupported_disjoint hST.symm hJ hK t
  have hs : IsSiteSupported T (V'*C) := (isSiteSupported_unitaryEvolution hJ (-t)).matrix_mul hC
  obtain ⟨z,hz⟩ := disjoint_site_scalar_bound hST (isSiteSupported_unitaryEvolution hK t) hs
  have he : U - V'*C = V'*(V*U-C) := by rw [mul_sub,← mul_assoc,hprod,one_mul]
  have hv : ‖V'‖ = 1 := CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary J.2 (-t))
  change ‖U-z • (1:Reg n)‖ ≤ ‖U-V'*C‖ at hz
  refine ⟨z,hz.trans ?_⟩
  rw [he]
  calc
    _ ≤ ‖V'‖*‖V*U-C‖ := norm_mul_le _ _
    _ = ‖unitaryEvolution (J.val+K.val) t-C‖ := by rw [hv,one_mul,hfac]
    _ ≤ ‖unitaryEvolution (J.val+K.val) t-unitaryEvolution H.val t‖ +
      ‖unitaryEvolution H.val t-C‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      rw [norm_sub_rev (unitaryEvolution (J.val+K.val) t),add_comm]
      exact add_le_add_left (norm_unitaryEvolution_sub_le H.val (J.val+K.val) H.2 (J.2.add K.2) t) _

#print axioms packet_scalar_distance_with_spectator
end
end GaloisForLFunctions.HTGeometry
