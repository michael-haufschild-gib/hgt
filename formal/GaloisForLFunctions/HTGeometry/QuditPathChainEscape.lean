import GaloisForLFunctions.HTGeometry.QuditPathLeafArchitecture
import GaloisForLFunctions.HTGeometry.DiagonalSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathGenericityLaw

/-!
# The local Hamiltonian space of an open qudit chain escapes every constant real relation

An open chain of `n ≥ 2` sites with `q ≥ 2` levels each is one leaf extension of the chain one site
shorter, attached at its last site.  Its exact onsite-plus-nearest-neighbour Hamiltonian space
therefore inherits the escape property of the local-extension slice.  For two sites the architecture
imposes no restriction at all and a real diagonal witness suffices.

## Main results

* `exists_quditPathChain_spectrumEscapes` — the architecture and its escape property.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The open qudit chain, with the escape property of its local Hamiltonian space.** -/
theorem exists_quditPathChain_spectrumEscapes (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ (Physical Observer : Type) (instP : Fintype Physical) (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      @Fintype.card Physical instP = q ^ n ∧
      @SpectrumEscapesAffineRelations Physical instP instPd
        (↑T.hermitianLocalHamiltonianSubmodule) := by
  classical
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- two sites: the architecture is unrestricted
    refine ⟨Fin q × Fin q, Bool, inferInstance, inferInstance,
      RootedTensorTree.edge (Fin q) (Fin q) Bool (Equiv.refl Bool),
      (finTwoEquiv.symm.trans (finCongr hn2)), ?_, ?_, ?_⟩
    · ext a b
      rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
      cases a <;> cases b <;>
        simp [RootedTensorTree.graph, finTwoEquiv, finCongr]
    · rw [← hn2]
      simp [pow_two]
    · refine diagonalSet_spectrumEscapesAffineRelations.mono ?_
      rintro M ⟨E, rfl⟩
      refine RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _ ?_ ?_
      · exact trivial
      · exact Matrix.isHermitian_diagonal_iff.mpr fun i => Complex.conj_ofReal _
  · -- at least three sites: one leaf extension of the shorter chain
    obtain ⟨Z, e, hgraph, hstate, -, -, -⟩ :=
      exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure
        (n - 1) q (by omega) hq
    letI : Fintype Z.spectral.State := Z.spectral.stateFintype
    letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
    letI : Nonempty Z.spectral.State := Z.spectral.stateNonempty
    letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
    letI : DecidableEq Z.spectral.Observer := Z.spectral.observerDecidableEq
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    let root : Z.spectral.Observer := e.symm ⟨n - 2, by omega⟩
    have hroot : ((e root : Fin (n - 1)) : ℕ) + 1 = n - 1 := by
      have hval : (e root : Fin (n - 1)) = (⟨n - 2, by omega⟩ : Fin (n - 1)) := by
        simp [root]
      rw [hval]
      show n - 2 + 1 = n - 1
      omega
    letI : Fintype (Z.spectral.Probe root) := Z.spectral.probeFintype root
    refine ⟨Z.PhysicalState × Fin q, LeafExtendedObserver Z.spectral.Observer,
      inferInstance, inferInstance,
      RootedTensorTree.leaf Z.locality.tree (Fin q) root,
      (leafPathEquiv e).trans (finCongr (by omega)), ?_, ?_, ?_⟩
    · show leafGraphExtension Z.locality.tree.graph root
        = SimpleGraph.comap _ (SimpleGraph.pathGraph n)
      have hcomap :
          SimpleGraph.comap ((leafPathEquiv e).trans (finCongr (show n - 1 + 1 = n by omega)))
              (SimpleGraph.pathGraph n)
            = SimpleGraph.comap (leafPathEquiv e)
                (SimpleGraph.comap (finCongr (show n - 1 + 1 = n by omega))
                  (SimpleGraph.pathGraph n)) := rfl
      rw [hcomap]
      have hpath :
          SimpleGraph.comap (finCongr (show n - 1 + 1 = n by omega)) (SimpleGraph.pathGraph n)
            = SimpleGraph.pathGraph (n - 1 + 1) := by
        ext i j
        rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]
        simp [finCongr]
      rw [hpath]
      have hZgraph : Z.locality.tree.graph = SimpleGraph.comap e (SimpleGraph.pathGraph (n - 1)) :=
        hgraph
      rw [hZgraph]
      exact leafGraphExtension_comap_pathGraph e root hroot
    · have hcardPhysical : Fintype.card Z.PhysicalState = Fintype.card Z.spectral.State :=
        card_eq_of_coordinateUnitary Z.realization.star_basis_mul_basis
          Z.realization.basis_mul_star_basis
      rw [Fintype.card_prod, hcardPhysical, Fintype.card_fin]
      have : Fintype.card Z.spectral.State = q ^ (n - 1) := hstate
      rw [this, ← pow_succ]
      congr 1
      omega
    · refine leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations
        Z.locality.tree root (Fin q) (by simpa using hq)
        Z.spectral.energy Z.spectral.energy_maximallyProjective
        Z.realization.basis Z.realization.star_basis_mul_basis
        Z.realization.basis_mul_star_basis
        Z.hamiltonian Z.locality.hamiltonian_local Z.realization.hamiltonian_coordinate
        (Z.realization.physicalProbe root) (Z.locality.probe_local root)
        (Z.spectral.transition root) (Z.realization.transition_eq_coordinate root)
        (Z.spectral.observerFamily_good root).1
        (Z.spectral.observerFamily_good root).2.1
        (Z.spectral.observerFamily_good root).2.2

end

end GaloisForLFunctions.HTGeometry
