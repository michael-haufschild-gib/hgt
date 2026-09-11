import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpTorsionLength

/-!
# Lattices adapted to a direct-sum decomposition

The block estimate that makes the relative tower produce a *proper* invariant subspace needs a
lattice compatible with a splitting `V = W ⊕ U`: only then does the decomposition of a vector into
its two components respect the filtration by uniformizer powers.

`adaptedTraceLattice L W U` is the sum of the two traces `L ⊓ W` and `L ⊓ U`.  It is finitely
generated as a sum of two finitely generated submodules, and it is full because each trace already
spans its own subspace (`span_subspaceTraceLattice`) and the two subspaces span everything.

`exists_split_of_uniformizer_smul_mem_adaptedTraceLattice` is the compatibility itself: if a
uniformizer power pushes `x` into the adapted lattice, then `x` splits as `w + u` with `w ∈ W`,
`u ∈ U`, and **the same** uniformizer power pushes each component into the corresponding trace
lattice.  This is what turns a bound on `σⁿ x` into separate bounds on its two components, which the
off-diagonal summation of the block estimate consumes.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Lattice adapted to a direct-sum decomposition of the coordinate space. -/
def adaptedTraceLattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W U : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hWU : W ⊔ U = ⊤) : DiffOp.CompletedPseudoDiffOpLattice K (Fin r) where
  carrier := subspaceTraceLattice L W ⊔ subspaceTraceLattice L U
  fg := (subspaceTraceLattice_fg L W).sup (subspaceTraceLattice_fg L U)
  full := by
    have hWspan : Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        ((subspaceTraceLattice L W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) = W :=
      span_subspaceTraceLattice L W
    have hUspan : Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        ((subspaceTraceLattice L U : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) = U :=
      span_subspaceTraceLattice L U
    have hWle : W ≤ Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        ((subspaceTraceLattice L W ⊔ subspaceTraceLattice L U :
          Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
            (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
          Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) := by
      calc W = Submodule.span (DiffOp.CompletedPseudoDiffOp K)
            ((subspaceTraceLattice L W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) :=
            hWspan.symm
        _ ≤ _ := Submodule.span_mono fun z hz => Submodule.mem_sup_left hz
    have hUle : U ≤ Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        ((subspaceTraceLattice L W ⊔ subspaceTraceLattice L U :
          Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
            (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
          Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) := by
      calc U = Submodule.span (DiffOp.CompletedPseudoDiffOp K)
            ((subspaceTraceLattice L U : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) :=
            hUspan.symm
        _ ≤ _ := Submodule.span_mono fun z hz => Submodule.mem_sup_right hz
    refine le_antisymm le_top ?_
    rw [← hWU]
    exact sup_le hWle hUle

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Splitting of the adapted lattice.**  A vector pushed into the adapted lattice by a uniformizer
power splits into its two components, each pushed into the corresponding trace lattice by the same
power. -/
theorem exists_split_of_uniformizer_smul_mem_adaptedTraceLattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W U : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hWU : W ⊔ U = ⊤) (m : ℕ) {x : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hx : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • x ∈
      (adaptedTraceLattice L W U hWU).carrier) :
    ∃ w u : Fin r → DiffOp.CompletedPseudoDiffOp K, x = w + u ∧ w ∈ W ∧ u ∈ U ∧
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • w ∈
        subspaceTraceLattice L W ∧
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • u ∈
        subspaceTraceLattice L U := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
  refine ⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • a,
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add, hab, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_smul]
  · exact W.smul_mem _ (subspaceTraceLattice_le_subspace L W ha)
  · exact U.smul_mem _ (subspaceTraceLattice_le_subspace L U hb)
  · rw [smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_smul]
    exact ha
  · rw [smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_smul]
    exact hb

end

end GaloisForLFunctions.HTGeometry
