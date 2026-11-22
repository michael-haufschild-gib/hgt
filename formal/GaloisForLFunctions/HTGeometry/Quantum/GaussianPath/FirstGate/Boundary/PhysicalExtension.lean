import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.ControlledFlip
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.LastSpinBlocks

/-! # Real nearest-neighbour chains with spectrally distinguishing endpoint Z -/
open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section

/-- Adjoin the new field bZ+X and the edge term Z_old X_new. -/
def extendPath (n : ℕ) (H Z : Register n) (b : ℝ) : Register (n+1) :=
  coupleSnoc n (boolPauliOption none) H + b • lastPauli n 2 + lastPauli n 0 +
    coupleSnoc n (finiteQubitPauli 0) Z

private theorem z_blocks (n : ℕ) : blocks n (lastPauli n 2) = sectorZ (Config n) := by
  unfold lastPauli
  rw [blocks_tensor]
  simp [sectorZ,finiteQubitPauli,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]

private theorem extend_blocks (n : ℕ) (H Z : Register n) (b : ℝ) :
    blocks n (extendPath n H Z b)=sectorMatrix H (1+Z) (1+Z) (b:ℂ) := by
  simp only [extendPath,blocks_add,blocks_real_smul,lastPauli,blocks_tensor]
  simp [sectorMatrix,boolPauliOption,finiteQubitPauli,fromBlocks_smul,fromBlocks_add,
    sub_eq_add_neg]

private theorem physical_step (n : ℕ) (H Z : Register n) (hsq : Z*Z=1) (hr : Resolved H Z) :
    ∃ b : ℝ, Resolved (extendPath n H Z b) (lastPauli n 2) := by
  have hc := Complex.continuous_ofReal.tendsto (0:ℝ)
  rw [Complex.ofReal_zero] at hc
  have hlim : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  obtain ⟨u,hu,h⟩ := (hp.and (hlim.eventually (resolved_controlled_flip H Z hsq hr))).exists
  have hub : (u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  have hb : Resolved (blocks n (extendPath n H Z u⁻¹)) (blocks n (lastPauli n 2)) := by
    rw [extend_blocks,z_blocks,Complex.ofReal_inv]
    exact h hub
  refine ⟨u⁻¹,?_⟩
  have hrestore (A : Register (n+1)) : Matrix.reindex (blockConfig n) (blockConfig n) (blocks n A)=A := by
    ext i j
    simp [blocks,Matrix.reindex_apply,Matrix.submatrix_apply]
  simpa only [hrestore] using hb.reindex (blockConfig n)

private theorem empty_resolved : Resolved (0 : Register 0) 1 := by
  refine ⟨fun _ t => t,fun _ => ⟨analyticAt_id,Eventually.of_forall fun t => ?_⟩,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  simp [matrixCharpolyRelation]

/-- For every length there is a real path Hamiltonian for which the last-site Z
has pairwise distinct slopes across all energy levels. -/
theorem exists_resolved_end (n : ℕ) :
    ∃ H ∈ pauliChainSpan (n+1), Resolved H (lastPauli n 2) := by
  induction n with
  | zero =>
    obtain ⟨b,hb⟩ := physical_step 0 0 1 (one_mul _) empty_resolved
    have hm (q : Fin 3) := pauliSiteSpan_le_pauliChainSpan 1 (Fin.last 0) (lastPauli_mem 0 q)
    refine ⟨_,?_,hb⟩
    change extendPath 0 0 1 b ∈ pauliChainSpan 1
    exact (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (couple_one_mem_pauliChainSpan (by exact Submodule.zero_mem _)) (Submodule.smul_mem _ b (hm 2))) (hm 0)) (hm 0))
  | succ n ih =>
    obtain ⟨H,hH,hz⟩ := ih
    obtain ⟨b,hb⟩ := physical_step (n+1) H (lastPauli n 2) (lastPauli_square n 2) hz
    have hm (q : Fin 3) := pauliSiteSpan_le_pauliChainSpan (n+2) (Fin.last (n+1)) (lastPauli_mem (n+1) q)
    exact ⟨_,Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (couple_one_mem_pauliChainSpan hH)
      (Submodule.smul_mem _ b (hm 2))) (hm 0)) (couple_last_mem_pauliChainSpan 0 (lastPauli_mem n 2)),hb⟩

#print axioms exists_resolved_end
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
