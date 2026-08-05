import GaloisForLFunctions.HTGeometry.ConnectedGraphSpanningLocalWitnessLaw

/-!
# Generic nearest-neighbour qudit path maximality

For every finite open path of at least two `q`-level sites, `q ≥ 2`,
this module realizes an exact onsite-plus-nearest-neighbour Hermitian
Hamiltonian space whose maximal-projective-spectrum locus is dense,
residual, and full Lebesgue measure.  The interaction graph is proved equal
to the whole path, not merely contained in it.
-/

open Set SimpleGraph MeasureTheory Topology Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A connected spanning subgraph of a relabelled finite open path is the
whole relabelled path. -/
theorem connected_subgraph_comap_path_eq
    {S : Type*} {n : ℕ} {H : SimpleGraph S}
    (e : S ≃ Fin n)
    (hH : H.Connected)
    (hle : H ≤ SimpleGraph.comap e (SimpleGraph.pathGraph n)) :
    H = SimpleGraph.comap e (SimpleGraph.pathGraph n) := by
  apply le_antisymm hle
  intro u v huv
  change (SimpleGraph.pathGraph n).Adj (e u) (e v) at huv
  rw [SimpleGraph.pathGraph_adj] at huv
  have succ_edge : ∀ {a b : S},
      (e a).val + 1 = (e b).val → H.Adj a b := by
    intro a b habval
    by_contra habH
    have preserve : ∀ {x y : S}, H.Adj x y →
        (e x).val ≤ (e a).val → (e y).val ≤ (e a).val := by
      intro x y hxy hx
      have hxyPath := (SimpleGraph.pathGraph_adj).mp (hle hxy)
      rcases hxyPath with hsucc | hpred
      · by_cases hxa : (e x).val = (e a).val
        · have hxEq : x = a := e.injective (Fin.ext hxa)
          have hyEq : y = b := e.injective (Fin.ext (by omega))
          exact (habH (hxEq ▸ hyEq ▸ hxy)).elim
        · omega
      · omega
    obtain ⟨walk⟩ := hH a b
    have walk_preserve : ∀ {x y : S} (w : H.Walk x y),
        (e x).val ≤ (e a).val → (e y).val ≤ (e a).val := by
      intro x y w
      induction w with
      | nil => exact fun hx => hx
      | @cons x y z hxy w ih =>
          intro hx
          exact ih (preserve hxy hx)
    have hb : (e b).val ≤ (e a).val :=
      walk_preserve walk le_rfl
    omega
  rcases huv with huv | huv
  · exact succ_edge huv
  · exact (succ_edge huv).symm

/-- **Generic nearest-neighbour qudit path law.** For every finite open
path of at least two `q`-level sites, the exact real coefficient space of
Hermitian onsite and nearest-neighbour terms has maximally projective
spectrum on a dense residual full-Lebesgue-measure set. -/
theorem exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph =
          SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
      Dense Z.localHamiltonianMaximalSet ∧
      Z.localHamiltonianMaximalSet ∈
        residual (Fin Z.localHamiltonianParameterCount → ℝ) ∧
      volume Z.localHamiltonianMaximalSetᶜ = 0 := by
  classical
  have hnpos : 0 < n := by omega
  have hpathConnected : (SimpleGraph.pathGraph n).Connected := by
    have h := SimpleGraph.pathGraph_connected (n - 1)
    have heq : n - 1 + 1 = n := by omega
    rw [heq] at h
    exact h
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨Z, e, hgraphLe, hstate, hgraphConnected⟩ :=
      exists_binarySpanningTreePhysicalSystem
        (SimpleGraph.pathGraph n) hpathConnected (by simpa using hn)
    have hgraphEq : Z.architectureGraph =
        SimpleGraph.comap e (SimpleGraph.pathGraph n) :=
      connected_subgraph_comap_path_eq e hgraphConnected hgraphLe
    obtain ⟨hdense, hresidual, hnull⟩ :=
      Z.localHamiltonianMaximalSet_dense_residual_fullMeasure
    exact ⟨Z, e, hgraphEq, by simpa using hstate,
      hdense, hresidual, hnull⟩
  · have hq3 : 3 ≤ q := by omega
    let root : Fin n := ⟨0, hnpos⟩
    obtain ⟨Z, e, hgraphLe, hstate, hgraphConnected⟩ :=
      exists_rootedSpanningTreePhysicalSystem
        (SimpleGraph.pathGraph n) hpathConnected
          (fun _ : Fin n => q) (fun _ => hq) root hq3
    have hgraphEq : Z.architectureGraph =
        SimpleGraph.comap e (SimpleGraph.pathGraph n) :=
      connected_subgraph_comap_path_eq e hgraphConnected hgraphLe
    obtain ⟨hdense, hresidual, hnull⟩ :=
      Z.localHamiltonianMaximalSet_dense_residual_fullMeasure
    refine ⟨Z, e, hgraphEq, ?_, hdense, hresidual, hnull⟩
    simpa using hstate

end

end GaloisForLFunctions.HTGeometry
