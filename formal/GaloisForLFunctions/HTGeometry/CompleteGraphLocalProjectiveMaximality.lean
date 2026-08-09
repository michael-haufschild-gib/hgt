import GaloisForLFunctions.HTGeometry.HypergraphLocalHamiltonian

/-!
# All-to-all two-local qudit Hamiltonians have generically maximal projective rank

The complete interaction graph is the two-section of the hypergraph of all two-element site
subsets, so the connected-hypergraph genericity law applies verbatim: for almost every traceless
Hermitian Hamiltonian built from arbitrary one-site and two-site terms on the complete graph the
spectrum is simple, trace is the only rational affine relation among the eigenvalues, and the
anchored projective rank is maximal.
-/

open Set SimpleGraph MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Hyperedges of the all-to-all two-local architecture: every two-element site subset. -/
def completeTwoLocalHyperedges (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.powersetCard 2

omit [Nonempty V] in
theorem twoSection_completeTwoLocalHyperedges :
    twoSection (completeTwoLocalHyperedges V) = (⊤ : SimpleGraph V) := by
  ext u v
  rw [twoSection_adj_iff, SimpleGraph.top_adj]
  constructor
  · rintro ⟨hne, -⟩
    exact hne
  · intro hne
    refine ⟨hne, {u, v}, ?_, by simp, by simp⟩
    rw [completeTwoLocalHyperedges, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

theorem twoSection_completeTwoLocalHyperedges_connected :
    (twoSection (completeTwoLocalHyperedges V)).Connected := by
  rw [twoSection_completeTwoLocalHyperedges]
  exact SimpleGraph.connected_top

variable (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- **Complete-graph two-local genericity.**  In the whole real vector space of Hermitian
Hamiltonians with arbitrary one-site and two-site terms on the complete graph, maximal projective
rational spectral rank is dense, residual and of full Lebesgue measure. -/
theorem completeTwoLocalMaximalSet_dense_residual_fullMeasure
    (hA : ∀ v, 2 ≤ Fintype.card (A v)) :
    Dense (hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V)) ∧
      hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V) ∈
        residual (Fin (Module.finrank ℝ
          (hypergraphLocalSubmodule A (completeTwoLocalHyperedges V))) → ℝ) ∧
      volume (hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V))ᶜ = 0 :=
  hypergraphLocalMaximalSet_dense_residual_fullMeasure A hA
    (completeTwoLocalHyperedges V) twoSection_completeTwoLocalHyperedges_connected

omit [Nonempty V] in
/-- Complete-graph spectral simplicity on the generic set. -/
theorem injective_eigenvalues_completeTwoLocalMatrix
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A (completeTwoLocalHyperedges V))) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V)) :
    Function.Injective
      (hypergraphLocalMatrix_isHermitian A (completeTwoLocalHyperedges V) p).eigenvalues :=
  injective_eigenvalues_hypergraphLocalMatrix A (completeTwoLocalHyperedges V) p hp

omit [Nonempty V] in
/-- Complete-graph maximal projective independence on the generic set: trace is the only rational
affine relation among the eigenvalues. -/
theorem maximallyProjective_completeTwoLocalMatrix
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A (completeTwoLocalHyperedges V))) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V)) :
    MaximallyProjectiveEnergy
      (hypergraphLocalMatrix_isHermitian A (completeTwoLocalHyperedges V) p).eigenvalues :=
  maximallyProjective_of_mem_hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V) p hp

omit [Nonempty V] in
/-- **Complete-graph maximal projective rank.**  On the generic set the anchored projective
rational spectral rank is the full tensor dimension minus one. -/
theorem anchoredTemporalRank_completeTwoLocalMatrix_eq
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A (completeTwoLocalHyperedges V))) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A (completeTwoLocalHyperedges V)) (r : ∀ v, A v) :
    anchoredTemporalRank
        (hypergraphLocalMatrix_isHermitian A (completeTwoLocalHyperedges V) p).eigenvalues r
      = (∏ v, Fintype.card (A v)) - 1 :=
  anchoredTemporalRank_hypergraphLocalMatrix_eq A (completeTwoLocalHyperedges V) p hp r

omit [Nonempty V] in
/-- Uniform `q`-level version: the generic anchored projective rank on `n` all-to-all coupled
`q`-level sites is `q ^ n - 1`. -/
theorem anchoredTemporalRank_completeTwoLocalMatrix_uniform
    {q : ℕ}
    (p : Fin (Module.finrank ℝ
      (hypergraphLocalSubmodule (fun _ : V => Fin q) (completeTwoLocalHyperedges V))) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet (fun _ : V => Fin q) (completeTwoLocalHyperedges V))
    (r : ∀ _ : V, Fin q) :
    anchoredTemporalRank
        (hypergraphLocalMatrix_isHermitian (fun _ : V => Fin q)
          (completeTwoLocalHyperedges V) p).eigenvalues r
      = q ^ Fintype.card V - 1 := by
  rw [anchoredTemporalRank_completeTwoLocalMatrix_eq (fun _ : V => Fin q) p hp r]
  simp [Finset.prod_const, Finset.card_univ]

end

end GaloisForLFunctions.HTGeometry
