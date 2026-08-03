import GaloisForLFunctions.HTGeometry.BlockSplitBranchEscape
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw
import Mathlib.Logic.Equiv.Prod

/-!
# The edges of one qubit as two-dimensional blocks

Splitting off one Boolean coordinate presents the Boolean cube as two copies of the cube on the
remaining coordinates.  A Hamiltonian which is diagonal apart from the transverse coupling of that
one qubit is therefore block diagonal with two-by-two blocks, one for each configuration of the
environment, and the block entries are the two energies of the edge together with the coupling.

The characteristic relation is invariant under this reindexing, so the block spectral machinery
applies verbatim to such a Hamiltonian.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Boolean configurations of all qubits other than a fixed one. -/
abbrev qubitEnvironment (n : ℕ) (i : Fin n) : Type := {j : Fin n // j ≠ i} → Bool

/-- The Boolean configuration with prescribed environment and prescribed value at one qubit. -/
def edgeState (i : Fin n) (z : qubitEnvironment n i) (b : Bool) : Fin n → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, z)

/-- Presenting the Boolean cube as the two layers of one qubit over its environment. -/
def edgeEquiv (i : Fin n) : Fin 2 × qubitEnvironment n i ≃ (Fin n → Bool) :=
  (finTwoEquiv.prodCongr (Equiv.refl (qubitEnvironment n i))).trans
    (Equiv.funSplitAt i Bool).symm

theorem edgeEquiv_apply (i : Fin n) (a : Fin 2) (z : qubitEnvironment n i) :
    edgeEquiv i (a, z) = edgeState i z (finTwoEquiv a) := rfl

theorem edgeEquiv_zero (i : Fin n) (z : qubitEnvironment n i) :
    edgeEquiv i (0, z) = edgeState i z false := rfl

theorem edgeEquiv_one (i : Fin n) (z : qubitEnvironment n i) :
    edgeEquiv i (1, z) = edgeState i z true := rfl

theorem edgeState_self (i : Fin n) (z : qubitEnvironment n i) (b : Bool) :
    edgeState i z b i = b := by
  simp [edgeState]

theorem edgeState_of_ne (i : Fin n) (z : qubitEnvironment n i) (b : Bool) {j : Fin n}
    (hj : j ≠ i) : edgeState i z b j = z ⟨j, hj⟩ := by
  simp [edgeState, hj]

/-- Toggling the distinguished qubit exchanges the two layers. -/
theorem boolToggle_edgeState (i : Fin n) (z : qubitEnvironment n i) (b : Bool) :
    boolToggle (edgeState i z b) i = edgeState i z (!b) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [boolToggle, Function.update_self, edgeState_self, edgeState_self]
  · rw [boolToggle, Function.update_of_ne hj, edgeState_of_ne i z b hj,
      edgeState_of_ne i z (!b) hj]

theorem edgeState_injective (i : Fin n) :
    Function.Injective fun q : Bool × qubitEnvironment n i => edgeState i q.2 q.1 := by
  intro q q' h
  have h' : (Equiv.funSplitAt i Bool).symm (q.1, q.2)
      = (Equiv.funSplitAt i Bool).symm (q'.1, q'.2) := h
  have := (Equiv.funSplitAt i Bool).symm.injective h'
  exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)

/-- Mean of the two energies of each edge of one qubit. -/
noncomputable def edgeMean (i : Fin n) (e : (Fin n → Bool) → ℝ) : qubitEnvironment n i → ℝ :=
  fun z => (e (edgeState i z false) + e (edgeState i z true)) / 2

/-- Half the energy gap of each edge of one qubit, oriented towards the switched-off layer. -/
noncomputable def edgeGap (i : Fin n) (e : (Fin n → Bool) → ℝ) : qubitEnvironment n i → ℝ :=
  fun z => (e (edgeState i z false) - e (edgeState i z true)) / 2

/-- The unsplit block energies are the energies of the Boolean states. -/
theorem blockEnergy_edge (i : Fin n) (e : (Fin n → Bool) → ℝ)
    (p : Fin 2 × qubitEnvironment n i) :
    blockEnergy (edgeMean i e) (edgeGap i e) p = e (edgeEquiv i p) := by
  obtain ⟨a, z⟩ := p
  revert a
  rw [Fin.forall_fin_two]
  constructor
  · rw [edgeEquiv_zero]
    simp only [blockEnergy, edgeMean, edgeGap]
    norm_num
    ring
  · rw [edgeEquiv_one]
    simp only [blockEnergy, edgeMean, edgeGap]
    norm_num
    ring

/-- The characteristic relation does not see a reindexing of the matrix. -/
theorem matrixCharpolyRelation_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (E : ι ≃ κ) (A : Matrix κ κ ℂ) (w : ℂ) :
    matrixCharpolyRelation (A.submatrix E E, w) = matrixCharpolyRelation (A, w) := by
  have hsub : (Matrix.scalar ι w) - A.submatrix E E
      = ((Matrix.scalar κ w) - A).submatrix E E := by
    ext p q
    simp [Matrix.scalar_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.diagonal_apply, E.injective.eq_iff]
  rw [matrixCharpolyRelation, matrixCharpolyRelation, hsub, Matrix.det_submatrix_equiv_self]

/-- **Edge block form.**  A Hamiltonian which is diagonal apart from the transverse coupling of one
qubit becomes, in the edge presentation of that qubit, the block splitting of its energies. -/
theorem submatrix_edgeEquiv_eq_blockSplitMatrix (i : Fin n)
    (e : (Fin n → Bool) → ℝ) (u : ℂ) (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hdiag : ∀ x, A x x = ((e x : ℝ) : ℂ))
    (hoff : ∀ x y, x ≠ y → A x y = if y = boolToggle x i then u else 0) :
    A.submatrix (edgeEquiv i) (edgeEquiv i)
      = blockSplitMatrix (edgeMean i e) (edgeGap i e) u := by
  classical
  ext p q
  obtain ⟨a, z⟩ := p
  obtain ⟨b, y⟩ := q
  rw [Matrix.submatrix_apply]
  by_cases hzy : z = y
  · subst hzy
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply_eq]
    revert a b
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [show edgeEquiv i (0, z) = edgeState i z false from rfl, hdiag]
      simp only [splitBlock, edgeMean, edgeGap]
      norm_num
      ring
    · have hne : edgeState i z false ≠ edgeState i z true := by
        intro hcon
        have := edgeState_injective i (a₁ := (false, z)) (a₂ := (true, z)) hcon
        exact Bool.false_ne_true (congrArg Prod.fst this)
      rw [show edgeEquiv i (0, z) = edgeState i z false from rfl,
        show edgeEquiv i (1, z) = edgeState i z true from rfl, hoff _ _ hne,
        if_pos (by rw [boolToggle_edgeState]; rfl)]
      simp [splitBlock]
    · have hne : edgeState i z true ≠ edgeState i z false := by
        intro hcon
        have := edgeState_injective i (a₁ := (true, z)) (a₂ := (false, z)) hcon
        exact Bool.false_ne_true (congrArg Prod.fst this).symm
      rw [show edgeEquiv i (1, z) = edgeState i z true from rfl,
        show edgeEquiv i (0, z) = edgeState i z false from rfl, hoff _ _ hne,
        if_pos (by rw [boolToggle_edgeState]; rfl)]
      simp [splitBlock]
    · rw [show edgeEquiv i (1, z) = edgeState i z true from rfl, hdiag]
      simp only [splitBlock, edgeMean, edgeGap]
      norm_num
      ring
  · have hne : edgeEquiv i (a, z) ≠ edgeEquiv i (b, y) := by
      intro hcon
      exact hzy (congrArg Prod.snd ((edgeEquiv i).injective hcon))
    have hnotoggle : edgeEquiv i (b, y) ≠ boolToggle (edgeEquiv i (a, z)) i := by
      rw [edgeEquiv_apply, edgeEquiv_apply, boolToggle_edgeState]
      intro hcon
      exact hzy (congrArg Prod.snd
        (edgeState_injective i (a₁ := (finTwoEquiv b, y)) (a₂ := (!finTwoEquiv a, z)) hcon)).symm
    rw [hoff _ _ hne, if_neg hnotoggle]
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hzy]

end GaloisForLFunctions.HTGeometry
