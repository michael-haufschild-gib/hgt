import GaloisForLFunctions.HTGeometry.SiteFactorGraphWitness
import GaloisForLFunctions.HTGeometry.DiagonalSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.HypergraphLocalHamiltonian

/-!
# Real spectral nondegeneracy on every connected interaction network

The full Hermitian onsite-plus-edge space of any connected finite graph escapes
every prescribed real affine relation among its energies. Local dimensions may
differ. A removable vertex reduces the construction to one leaf extension of a
charted spectral witness; one- and two-site networks are full matrix spaces.
The same escape holds for support-contained hypergraph interactions whenever
the two-section graph is connected.
-/

open Set SimpleGraph
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Transporting a leaf attached to a charted network preserves exact graph
locality, including arbitrary real linear combinations of local generators. -/
theorem SiteFactorChart.leaf_spectrumEscapesAffineRelations
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (G : SimpleGraph V) (v : V)
    (Z : PhysicallyRealizedTensorTreeSystem)
    (C : SiteFactorChart Z (fun w : {w : V // w ≠ v} => A w.1)
      (G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))))
    (parent : {w : V // w ≠ v}) (hparent : G.Adj parent.1 v)
    (hcard : 2 ≤ Fintype.card (A v)) :
    SpectrumEscapesAffineRelations
      (siteFactorLocalSubmodule A G : Set (Matrix (∀ w, A w) (∀ w, A w) ℂ)) := by
  classical
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Nonempty Z.spectral.State := Z.spectral.stateNonempty
  letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
  letI : DecidableEq Z.spectral.Observer := Z.spectral.observerDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  let root := C.observerEquiv.symm parent
  letI : Fintype (Z.spectral.Probe root) := Z.spectral.probeFintype root
  have hescape := leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations
    Z.tree root (A v) hcard
    Z.spectral.energy Z.spectral.energy_maximallyProjective
    Z.realization.basis Z.realization.star_basis_mul_basis
    Z.realization.basis_mul_star_basis
    Z.hamiltonian Z.locality.hamiltonian_local Z.realization.hamiltonian_coordinate
    (Z.realization.physicalProbe root) (Z.locality.probe_local root)
    (Z.spectral.transition root) (Z.realization.transition_eq_coordinate root)
    (Z.spectral.observerFamily_good root).1
    (Z.spectral.observerFamily_good root).2.1
    (Z.spectral.observerFamily_good root).2.2
  let e : (Z.PhysicalState × A v) ≃ (∀ w, A w) :=
    (C.chart.prodCongr (Equiv.refl (A v))).trans (leafSiteEquiv A v)
  let transport : Matrix (Z.PhysicalState × A v) (Z.PhysicalState × A v) ℂ →ₗ[ℝ]
      Matrix (∀ w, A w) (∀ w, A w) ℂ :=
    { toFun := Matrix.reindex e e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinc : (RootedTensorTree.leaf Z.tree (A v) root).hermitianLocalHamiltonianSubmodule ≤
      (siteFactorLocalSubmodule A G).comap transport := by
    apply Submodule.span_le.2
    rintro H ⟨hlocal, hHerm⟩
    change Matrix.reindex e e H ∈ siteFactorLocalSubmodule A G
    have hHerm' : (Matrix.reindex e e H).IsHermitian := by
      show Matrix.reindex e e Hᴴ = Matrix.reindex e e H
      rw [show Hᴴ = H from hHerm]
    refine mem_siteFactorLocalSubmodule_of_mem_termSpan A G ?_ hHerm'
    obtain ⟨oldHamiltonian, parentOperator, shift, edge, hold, hparentOne, rfl⟩ := hlocal
    have hcouple : ∀ (M : Matrix Z.PhysicalState Z.PhysicalState ℂ)
        (N : Matrix (A v) (A v) ℂ),
        Matrix.reindex e e (layerMatrixCoupling M N) =
          leafTransport A v (layerMatrixCoupling (Matrix.reindex C.chart C.chart M) N) :=
      fun _ _ => rfl
    have hone : Matrix.reindex C.chart C.chart
        (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) = 1 :=
      Matrix.submatrix_one_equiv _
    have hadd : ∀ X Y : Matrix (Z.PhysicalState × A v) (Z.PhysicalState × A v) ℂ,
        Matrix.reindex e e (X + Y) = Matrix.reindex e e X + Matrix.reindex e e Y :=
      fun _ _ => rfl
    change Matrix.reindex e e
      (layerMatrixCoupling oldHamiltonian 1 + layerMatrixCoupling 1 (Matrix.diagonal shift) +
        layerMatrixCoupling parentOperator edge) ∈ _
    rw [hadd, hadd, hcouple, hcouple, hcouple, hone]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact leafTransport_mem_siteFactorTermSpan A v (fun _ _ h => h)
        (C.localHamiltonian oldHamiltonian hold)
    · exact Submodule.subset_span
        (isGraphLocalTerm_leafTransport_newSite A v G (Matrix.diagonal shift))
    · have hsupp := C.oneSite root parentOperator hparentOne
      change IsSiteSupported {C.observerEquiv (C.observerEquiv.symm parent)} _ at hsupp
      rw [Equiv.apply_symm_apply] at hsupp
      exact Submodule.subset_span
        (isGraphLocalTerm_leafTransport_edge A v hsupp hparent edge)
  exact hescape.reindex e (fun _ hH => hinc hH)

/-- Every connected finite interaction graph with local dimensions at least two
has real affine spectral escape in its full Hermitian local coefficient space.
No generic spectral or Diophantine premise is required. -/
theorem connectedGraph_spectrumEscapesAffineRelations
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (hA : ∀ x, 2 ≤ Fintype.card (A x)) :
    SpectrumEscapesAffineRelations
      (siteFactorLocalSubmodule A G : Set (Matrix (∀ v, A v) (∀ v, A v) ℂ)) := by
  classical
  by_cases hlarge : 2 < Fintype.card V
  · letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hremaining⟩ :=
      hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let OldV := {x : V // x ≠ v}
    let oldG : SimpleGraph OldV :=
      G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))
    have holdConnected : oldG.Connected := hremaining
    letI : DecidableRel oldG.Adj := Classical.decRel _
    have holdCard : 2 ≤ Fintype.card OldV := by
      rw [show Fintype.card OldV = Fintype.card V - 1 by
        dsimp [OldV]
        rw [Fintype.card_subtype_compl (fun x : V => x = v), Fintype.card_subtype_eq]]
      omega
    have hcharted : ∃ Z : PhysicallyRealizedTensorTreeSystem,
        Nonempty (SiteFactorChart Z (fun w : OldV => A w.1) oldG) := by
      by_cases h3 : ∃ w : OldV, 3 ≤ Fintype.card (A w.1)
      · obtain ⟨w, hw⟩ := h3
        exact exists_siteFactorChart_rootedSpanningTree oldG holdConnected
          (fun w : OldV => A w.1) (fun w => hA w.1) w hw
      · push Not at h3
        have hA2 : ∀ w : OldV, Fintype.card (A w.1) = 2 := by
          intro w
          have := h3 w
          have := hA w.1
          omega
        exact exists_siteFactorChart_binarySpanningTree oldG holdConnected
          (fun w : OldV => A w.1) hA2 holdCard
    obtain ⟨Z, ⟨C⟩⟩ := hcharted
    obtain ⟨parent, hvparent⟩ := (G.degree_pos_iff_exists_adj v).mp
      (hG.preconnected.degree_pos_of_nontrivial v)
    exact SiteFactorChart.leaf_spectrumEscapesAffineRelations A G v Z C
      ⟨parent, hvparent.ne'⟩ hvparent.symm (hA v)
  · refine diagonalSet_spectrumEscapesAffineRelations.mono ?_
    rintro M ⟨E, rfl⟩
    have hHerm : (Matrix.diagonal (fun i => (E i : ℂ))).IsHermitian :=
      Matrix.isHermitian_diagonal_iff.mpr fun i => Complex.conj_ofReal _
    by_cases htwo : 2 ≤ Fintype.card V
    · have hcardEq : Fintype.card V = 2 := by omega
      obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
      have huniv : ∀ w : V, w = a ∨ w = b := by
        intro w
        by_contra hcon
        push Not at hcon
        have hcard3 : ({w, a, b} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨hcon.1, hcon.2⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact hab), Finset.card_singleton]
        have hle := Finset.card_le_card (Finset.subset_univ ({w, a, b} : Finset V))
        rw [hcard3, Finset.card_univ, hcardEq] at hle
        omega
      have hadj : G.Adj a b := by
        letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj a).mp
          (hG.preconnected.degree_pos_of_nontrivial a)
        rcases huniv w with rfl | rfl
        · exact absurd rfl hw.ne
        · exact hw
      refine mem_siteFactorLocalSubmodule_of_mem_termSpan A G
        (Submodule.subset_span (Or.inr ⟨a, b, hadj, ?_⟩)) hHerm
      refine IsSiteSupported.of_forall_mem (A := A) (fun w => ?_) _
      rcases huniv w with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have hone : Fintype.card V = 1 := by
        have := Fintype.card_pos_iff.mpr ‹Nonempty V›
        omega
      obtain ⟨v, hv⟩ := Fintype.card_eq_one_iff.mp hone
      refine mem_siteFactorLocalSubmodule_of_oneSite A G hHerm v ?_
      refine IsSiteSupported.of_forall_mem (A := A) (fun w => ?_) _
      rw [hv w]
      exact Finset.mem_singleton_self _

/-- Connected support-contained hypergraph interactions inherit real affine
spectral escape from the onsite-plus-edge space of their two-section graph. -/
theorem connectedHypergraph_spectrumEscapesAffineRelations
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (𝔥 : Finset (Finset V)) (hconn : (twoSection 𝔥).Connected)
    (hA : ∀ x, 2 ≤ Fintype.card (A x)) :
    SpectrumEscapesAffineRelations
      (hypergraphLocalSubmodule A 𝔥 : Set (Matrix (∀ v, A v) (∀ v, A v) ℂ)) := by
  classical
  exact (connectedGraph_spectrumEscapesAffineRelations (twoSection 𝔥) hconn A hA).mono
    (siteFactorLocalSubmodule_twoSection_le_hypergraphLocalSubmodule A 𝔥)

end

end GaloisForLFunctions.HTGeometry
