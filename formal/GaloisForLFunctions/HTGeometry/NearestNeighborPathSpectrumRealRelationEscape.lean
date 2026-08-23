import GaloisForLFunctions.HTGeometry.NearestNeighborGaussianSameDrawGrowthLaw
import GaloisForLFunctions.HTGeometry.SubmoduleSpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.ChainPauliFinEscape

open scoped BigOperators Matrix
open Matrix Set

namespace GaloisForLFunctions.HTGeometry

open StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

/-- A Pauli word is supported on every packet containing all its nonidentity sites. -/
theorem finitePauliMatrix_isSiteSupported_of_eq_none
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (P : V → Option (Fin 3))
    (hP : ∀ v, v ∉ S → P v = none) :
    IsSiteSupported S (finitePauliMatrix P) := by
  constructor
  · rintro x y ⟨w, hwS, hxy⟩
    rw [finitePauliMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    rw [hP w hwS]
    simp [boolPauliOptionEntry, boolPauliOption, hxy]
  · intro x y x' y' hx hy hout hout'
    rw [finitePauliMatrix, finitePauliMatrix]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v ∈ S
    · rw [hx v hv, hy v hv]
    · rw [hP v hv]
      simp [boolPauliOptionEntry, boolPauliOption, Matrix.one_apply,
        hout v hv, hout' v hv]

/-- A nonidentity chain label is supported on one vertex or one path edge. -/
theorem exists_singleton_or_pathEdge_support_of_isChainLabel
    {n : ℕ} (P : Fin n → Option (Fin 3))
    (hchain : IsChainLabel P) (hne : P ≠ pauliIdentityLabel n) :
    (∃ v : Fin n, ∀ w, P w ≠ none → w = v) ∨
      ∃ u v : Fin n, (SimpleGraph.pathGraph n).Adj u v ∧
        ∀ w, P w ≠ none → w = u ∨ w = v := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i => P i ≠ none
  have hmemS : ∀ t : Fin n, t ∈ S ↔ P t ≠ none := by
    intro t
    simp [S]
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS
    apply hne
    funext t
    by_contra ht
    have : t ∈ S := (hmemS t).2 ht
    rw [hS] at this
    exact Finset.notMem_empty t this
  let m : Fin n := S.min' hSne
  have hmS : m ∈ S := S.min'_mem hSne
  have hmP : P m ≠ none := (hmemS m).1 hmS
  have hrange : ∀ t : Fin n, P t ≠ none →
      (t : ℕ) = (m : ℕ) ∨ (t : ℕ) = (m : ℕ) + 1 := by
    intro t ht
    have htS : t ∈ S := (hmemS t).2 ht
    have hlow : (m : ℕ) ≤ (t : ℕ) := S.min'_le t htS
    have hhigh : (t : ℕ) ≤ (m : ℕ) + 1 := hchain t m ht hmP
    omega
  by_cases hedge : ∃ i : Fin n, P i ≠ none ∧ (i : ℕ) = (m : ℕ) + 1
  · obtain ⟨i, hiP, hi⟩ := hedge
    right
    refine ⟨m, i, ?_, ?_⟩
    · rw [SimpleGraph.pathGraph_adj]
      exact Or.inl (by omega)
    · intro w hw
      rcases hrange w hw with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by omega))
  · left
    refine ⟨m, fun w hw => ?_⟩
    rcases hrange w hw with h | h
    · exact Fin.ext h
    · exact False.elim (hedge ⟨w, hw, h⟩)

def pairPathConfigurationEquiv (L : ℕ) :
    Config (PairQubit L) ≃ FiniteQubitConfiguration (Fin (L * 2)) :=
  Equiv.arrowCongr
    (StaticLocalLaboratoryComplexityGrowthLaw.pairQubitPathEquiv L)
    (Equiv.refl Bool)

/-- Chain Pauli generators become physical onsite/edge terms on the paired path. -/
theorem reindexed_chainPauliFin_mem_nearestNeighborPathLocalSubmodule
    (k : ℕ) (a : Fin (Fintype.card (ChainLabel ((k + 2) * 2)))) :
    Matrix.reindex
        ((qubitConfigFin ((k + 2) * 2)).symm.trans
          (pairPathConfigurationEquiv (k + 2)).symm)
        ((qubitConfigFin ((k + 2) * 2)).symm.trans
          (pairPathConfigurationEquiv (k + 2)).symm)
        (chainPauliFin ((k + 2) * 2) a) ∈
      StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalSubmodule (k + 2) := by
  classical
  let Q : ChainLabel ((k + 2) * 2) :=
    (Fintype.equivFin (ChainLabel ((k + 2) * 2))).symm a
  let e := StaticLocalLaboratoryComplexityGrowthLaw.pairQubitPathEquiv (k + 2)
  let ec := pairPathConfigurationEquiv (k + 2)
  let Pphys : PairQubit (k + 2) → Option (Fin 3) := fun v => Q.1 (e v)
  have hmatrix :
      Matrix.reindex
          ((qubitConfigFin ((k + 2) * 2)).symm.trans ec.symm)
          ((qubitConfigFin ((k + 2) * 2)).symm.trans ec.symm)
          (chainPauliFin ((k + 2) * 2) a) =
        finitePauliMatrix Pphys := by
    ext x y
    simp [chainPauliFin, Q, Pphys, e, ec, Matrix.reindex_apply,
      finitePauliMatrix, pairPathConfigurationEquiv]
    symm
    simpa [e, Q] using Equiv.prod_comp e (fun z =>
      boolPauliOptionEntry (Q.1 z) (x (e.symm z), y (e.symm z)))
  rw [hmatrix]
  rcases exists_singleton_or_pathEdge_support_of_isChainLabel Q.1 Q.2.1 Q.2.2 with
    hsite | hedge
  · obtain ⟨s, hs⟩ := hsite
    let v : PairQubit (k + 2) := e.symm s
    apply mem_siteFactorLocalSubmodule_of_oneSite
      (fun _ : PairQubit (k + 2) => Bool)
      (StaticLocalLaboratoryComplexityGrowthLaw.nestedQubitPathGraph (k + 2))
      (finitePauliMatrix_isHermitian Pphys) v
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro w hw
    have hwne : e w ≠ s := by
      intro h
      apply hw
      simp [v, ← h]
    have : Q.1 (e w) = none := by
      by_contra hne
      exact hwne (hs (e w) hne)
    exact this
  · obtain ⟨s, t, hst, hsupp⟩ := hedge
    let u : PairQubit (k + 2) := e.symm s
    let v : PairQubit (k + 2) := e.symm t
    apply mem_siteFactorLocalSubmodule_of_edge
      (fun _ : PairQubit (k + 2) => Bool)
      (StaticLocalLaboratoryComplexityGrowthLaw.nestedQubitPathGraph (k + 2))
      (finitePauliMatrix_isHermitian Pphys)
      (u := u) (v := v)
    · rw [StaticLocalLaboratoryComplexityGrowthLaw.nestedQubitPathGraph,
        SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
      simpa [u, v, e] using (SimpleGraph.pathGraph_adj.mp hst)
    · apply finitePauliMatrix_isSiteSupported_of_eq_none
      intro w hw
      have hwu : e w ≠ s := by
        intro h
        apply hw
        simp [u, ← h]
      have hwv : e w ≠ t := by
        intro h
        apply hw
        simp [v, ← h]
      have : Q.1 (e w) = none := by
        by_contra hne
        rcases hsupp (e w) hne with h | h
        · exact hwu h
        · exact hwv h
      exact this

/-- Every reindexed chain Hamiltonian lies in the physical nearest-neighbour space. -/
theorem reindexed_chainPauliFin_ensemble_mem_nearestNeighborPathLocalSubmodule
    (k : ℕ)
    (H : Matrix (Fin (2 ^ ((k + 2) * 2))) (Fin (2 ^ ((k + 2) * 2))) ℂ)
    (hH : H ∈ Set.range
      (spectralEnsembleMatrix (chainPauliFin ((k + 2) * 2)))) :
    Matrix.reindex
        ((qubitConfigFin ((k + 2) * 2)).symm.trans
          (pairPathConfigurationEquiv (k + 2)).symm)
        ((qubitConfigFin ((k + 2) * 2)).symm.trans
          (pairPathConfigurationEquiv (k + 2)).symm) H ∈
      nearestNeighborPathLocalSubmodule (k + 2) := by
  classical
  obtain ⟨θ, rfl⟩ := hH
  let e := (qubitConfigFin ((k + 2) * 2)).symm.trans
    (pairPathConfigurationEquiv (k + 2)).symm
  have hreindex :
      Matrix.reindex e e
          (spectralEnsembleMatrix (chainPauliFin ((k + 2) * 2)) θ) =
        ∑ a, θ a • Matrix.reindex e e (chainPauliFin ((k + 2) * 2) a) := by
    ext x y
    simp [e, spectralEnsembleMatrix, Matrix.reindex_apply,
      Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  rw [hreindex]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (reindexed_chainPauliFin_mem_nearestNeighborPathLocalSubmodule k a)

/-- The exact nearest-neighbour physical Hamiltonian space escapes every
balanced real spectral relation. -/
theorem nearestNeighborPathLocalSubmodule_spectrumEscapesRealRelations
    (k : ℕ) :
    SpectrumEscapesRealRelations
      (↑(nearestNeighborPathLocalSubmodule (k + 2)) :
        Set (Matrix (Config (PairQubit (k + 2)))
          (Config (PairQubit (k + 2))) ℂ)) := by
  have hchain := chainPauliFin_spectrumEscapesRealRelations (2 * k + 1)
  have hsize : 2 * k + 1 + 3 = (k + 2) * 2 := by omega
  rw [hsize] at hchain
  exact hchain.reindex
    ((qubitConfigFin ((k + 2) * 2)).symm.trans
      (pairPathConfigurationEquiv (k + 2)).symm)
    (fun H hH =>
      reindexed_chainPauliFin_ensemble_mem_nearestNeighborPathLocalSubmodule k H hH)

/-- Canonical coordinates of the exact growth ensemble inherit real-relation escape. -/
theorem nearestNeighborPathLocalGenerator_spectrumEscapesRealRelations
    (k : ℕ) :
    SpectrumEscapesRealRelations
      (Set.range (realAffineMatrix 0
        (nearestNeighborPathLocalGenerator (k + 2)))) := by
  exact (nearestNeighborPathLocalSubmodule_spectrumEscapesRealRelations k).ofSubmodule

/-- The exact local family has a nonzero coefficient direction. -/
theorem nearestNeighborPathLocalParameterCount_pos (k : ℕ) :
    0 < nearestNeighborPathLocalParameterCount (k + 2) := by
  let v : PairQubit (k + 2) := (⟨0, by omega⟩, false)
  let Ilabel : PairQubit (k + 2) → Option (Fin 3) := fun _ => none
  have hIeq : finitePauliMatrix Ilabel =
      (1 : Matrix (Config (PairQubit (k + 2)))
        (Config (PairQubit (k + 2))) ℂ) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [finitePauliMatrix, Ilabel, boolPauliOptionEntry, boolPauliOption]
    · rw [finitePauliMatrix]
      obtain ⟨w, hw⟩ := Function.ne_iff.mp hxy
      have hzero : boolPauliOptionEntry (Ilabel w) (x w, y w) = 0 := by
        simp [Ilabel, boolPauliOptionEntry, boolPauliOption, hw]
      rw [Finset.prod_eq_zero (Finset.mem_univ w) hzero]
      simp [hxy]
  have honeMem :
      (1 : Matrix (Config (PairQubit (k + 2)))
        (Config (PairQubit (k + 2))) ℂ) ∈
        nearestNeighborPathLocalSubmodule (k + 2) := by
    rw [← hIeq]
    apply mem_siteFactorLocalSubmodule_of_oneSite
      (fun _ : PairQubit (k + 2) => Bool)
      (nestedQubitPathGraph (k + 2))
      (finitePauliMatrix_isHermitian Ilabel) v
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro w _
    rfl
  let oneLocal : nearestNeighborPathLocalSubmodule (k + 2) := ⟨1, honeMem⟩
  have honeNe : oneLocal ≠ 0 := by
    intro h
    have hv := congrArg (fun M : nearestNeighborPathLocalSubmodule (k + 2) =>
      (M : Matrix (Config (PairQubit (k + 2))) (Config (PairQubit (k + 2))) ℂ)) h
    have hentry := congrFun (congrFun hv (fun _ => false)) (fun _ => false)
    have hentry' : (1 : ℂ) = 0 := by
      simpa [oneLocal] using hentry
    exact one_ne_zero hentry'
  letI : Nontrivial (nearestNeighborPathLocalSubmodule (k + 2)) :=
    ⟨⟨oneLocal, 0, honeNe⟩⟩
  exact Module.finrank_pos

end

end GaloisForLFunctions.HTGeometry
