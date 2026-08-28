import GaloisForLFunctions.HTGeometry.SiteSupportedReindex
import GaloisForLFunctions.HTGeometry.SiteFactorQubitPauliWeightLaw

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Relabelling physical sites transports every onsite-plus-edge Hamiltonian
to the correspondingly relabelled interaction graph. -/
theorem reindex_mem_siteFactorLocalSubmodule
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph V)
    {H : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ}
    (hH : H ∈ siteFactorLocalSubmodule (fun _ : V => Bool) G) :
    Matrix.reindexAlgEquiv ℂ ℂ (qubitConfigurationEquiv e) H ∈
      siteFactorLocalSubmodule (fun _ : W => Bool) (G.comap e.symm) := by
  let φ : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ →ₗ[ℝ]
      Matrix (FiniteQubitConfiguration W)
        (FiniteQubitConfiguration W) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ (qubitConfigurationEquiv e)).toLinearMap.restrictScalars ℝ
  change φ H ∈ siteFactorLocalSubmodule (fun _ : W => Bool) (G.comap e.symm)
  induction hH using Submodule.span_induction with
  | mem H hgen =>
      rcases hgen with ⟨hHerm, hsite | hedge⟩
      · obtain ⟨v, hsupp⟩ := hsite
        apply Submodule.subset_span
        refine ⟨hHerm.reindex (qubitConfigurationEquiv e), Or.inl ⟨e v, ?_⟩⟩
        simpa [φ] using isSiteSupported_reindexAlgEquiv e {v} hsupp
      · obtain ⟨u, v, huv, hsupp⟩ := hedge
        apply Submodule.subset_span
        refine ⟨hHerm.reindex (qubitConfigurationEquiv e),
          Or.inr ⟨e u, e v, ?_, ?_⟩⟩
        · simpa [SimpleGraph.comap_adj] using huv
        · simpa [φ] using isSiteSupported_reindexAlgEquiv e {u, v} hsupp
  | zero => simp
  | add X Y _ _ hX hY =>
      rw [map_add]
      exact Submodule.add_mem _ hX hY
  | smul r X _ hX =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hX

/-- Pauli weight at most two is invariant under a physical site relabelling
for every ordinary onsite-plus-edge Hamiltonian. -/
theorem hasPauliWeightAtMost_two_reindex_of_mem_siteFactorLocalSubmodule
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph V)
    (H : selfAdjoint (Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ))
    (hH : (H : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ) ∈
        siteFactorLocalSubmodule (fun _ : V => Bool) G) :
    HasPauliWeightAtMost W 2
      ⟨Matrix.reindexAlgEquiv ℂ ℂ (qubitConfigurationEquiv e) H,
        isSelfAdjoint_reindexAlgEquiv (qubitConfigurationEquiv e) H.property⟩ := by
  exact hasPauliWeightAtMost_two_of_mem_siteFactorLocalSubmodule
    (G.comap e.symm) _ (reindex_mem_siteFactorLocalSubmodule e G hH)

end

end GaloisForLFunctions.HTGeometry
