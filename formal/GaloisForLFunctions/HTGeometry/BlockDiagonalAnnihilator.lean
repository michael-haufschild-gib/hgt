import GaloisForLFunctions.HTGeometry.TriangularCoefficientInjectivity

/-!
# Assembling blockwise injectivity over a sigma index

The coefficient matrix of a full packet is block diagonal over the node index: the jets at one node
expand only in the Cauchy powers at that node.  The rigidity transfer wants transpose injectivity of
the assembled matrix, and what is available is one triangular block per node.

Assembling them needs no transport between fibres, because a packet annihilating the assembled
matrix is tested one node at a time: the off-diagonal blocks vanish, so the test at a node in the
target index involves only the source indices at the same node.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Blockwise injectivity assembles over a sigma index.**  For a block diagonal matrix, a packet
annihilated by the transpose is annihilated blockwise, so blockwise injectivity gives injectivity. -/
theorem sigma_annihilator_eq_zero_of_blockwise
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*} [∀ i, Fintype (F i)]
    (M : (Σ i, F i) → (Σ i, F i) → ℂ)
    (hoff : ∀ s k : Σ i, F i, s.1 ≠ k.1 → M s k = 0)
    (hblock : ∀ (i : ι) (d : F i → ℂ),
      (∀ k : F i, ∑ j : F i, d j * M ⟨i, j⟩ ⟨i, k⟩ = 0) → ∀ j, d j = 0)
    (c : (Σ i, F i) → ℂ)
    (hc : ∀ k : Σ i, F i, ∑ s : Σ i, F i, c s * M s k = 0) :
    ∀ s, c s = 0 := by
  classical
  rintro ⟨i, j⟩
  refine hblock i (fun j => c ⟨i, j⟩) ?_ j
  intro k
  have hsum := hc ⟨i, k⟩
  rw [Fintype.sum_sigma] at hsum
  have hsplit :
      (∑ i' : ι, ∑ j' : F i', c ⟨i', j'⟩ * M ⟨i', j'⟩ ⟨i, k⟩)
        = ∑ j' : F i, c ⟨i, j'⟩ * M ⟨i, j'⟩ ⟨i, k⟩ := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro i' _ hne
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [hoff ⟨i', j'⟩ ⟨i, k⟩ hne, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  rw [← hsplit]
  exact hsum

end

end GaloisForLFunctions.HTGeometry
