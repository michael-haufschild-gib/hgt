import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

/-!
# A block-vanishing permanent factors over the blocks

The fibre amplitude of a monomial in the jets of several carriers is a permanent: a sum over all
permutations of the tuple, of the product of the entries met.  When the carriers have disjoint
frequency blocks the matrix is block-diagonal, and only the permutations preserving the blocks
survive.

This file proves the corresponding factorization.  It is the permanent analogue of
`Matrix.det_blockDiagonal`, but for blocks of *different* sizes: the blocks are the fibres of an
arbitrary labelling map, so no two of them need be in bijection.

The dependent bookkeeping is handled by destructuring rather than by casts: a member of the fibre
over `k` is `⟨a, rfl⟩` once `blk a = k` is substituted, and then both sides of every comparison are
syntactically equal.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

/-- The permutation of the whole index set assembled from permutations of the blocks. -/
def blockPerm (blk : α → κ) (τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k}) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv blk).symm.trans
    ((Equiv.sigmaCongrRight τ).trans (Equiv.sigmaFiberEquiv blk))

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
@[simp] theorem blockPerm_apply (blk : α → κ) (τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k})
    (a : α) : blockPerm blk τ a = ((τ (blk a) ⟨a, rfl⟩ : {x : α // blk x = blk a}) : α) := rfl

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
theorem blk_blockPerm (blk : α → κ) (τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k}) (a : α) :
    blk (blockPerm blk τ a) = blk a := by
  rw [blockPerm_apply]
  exact (τ (blk a) ⟨a, rfl⟩).2

/-- The permutations of the blocks read off a block-preserving permutation. -/
def permBlockRestrict (blk : α → κ) (σ : Equiv.Perm α) (hσ : ∀ a, blk (σ a) = blk a) (k : κ) :
    Equiv.Perm {a : α // blk a = k} :=
  σ.subtypeEquiv fun a => by rw [hσ a]

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
@[simp] theorem permBlockRestrict_coe (blk : α → κ) (σ : Equiv.Perm α) (hσ : ∀ a, blk (σ a) = blk a)
    (k : κ) (b : {a : α // blk a = k}) :
    ((permBlockRestrict blk σ hσ k b : {a : α // blk a = k}) : α) = σ (b : α) := rfl

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
theorem blockPerm_permBlockRestrict (blk : α → κ) (σ : Equiv.Perm α) (hσ : ∀ a, blk (σ a) = blk a) :
    blockPerm blk (permBlockRestrict blk σ hσ) = σ := by
  ext a
  rw [blockPerm_apply, permBlockRestrict_coe]

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
theorem permBlockRestrict_blockPerm (blk : α → κ) (τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k}) :
    permBlockRestrict blk (blockPerm blk τ) (blk_blockPerm blk τ) = τ := by
  funext k
  ext b
  obtain ⟨a, rfl⟩ := b
  rw [permBlockRestrict_coe, blockPerm_apply]

/-- **A block-vanishing permanent factors over the blocks.**  Only the permutations preserving every
block contribute, and those are exactly the families of permutations of the individual blocks. -/
theorem sum_perm_prod_of_blockVanishing (blk : α → κ) (F : α → α → ℂ)
    (hF : ∀ a b : α, blk b ≠ blk a → F a b = 0) :
    ∑ σ : Equiv.Perm α, ∏ a, F a (σ a)
      = ∏ k : κ, ∑ τ : Equiv.Perm {a : α // blk a = k},
          ∏ b : {a : α // blk a = k}, F (b : α) ((τ b : {a : α // blk a = k}) : α) := by
  classical
  -- the block-preserving permutations
  set P : Finset (Equiv.Perm α) :=
    Finset.univ.filter fun σ => ∀ a, blk (σ a) = blk a with hP
  have hmemP : ∀ {σ : Equiv.Perm α}, σ ∈ P ↔ ∀ a, blk (σ a) = blk a := by
    intro σ
    rw [hP, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hvanish : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm α)), σ ∉ P →
      (∏ a, F a (σ a)) = 0 := by
    intro σ _ hσ
    rw [hmemP] at hσ
    push Not at hσ
    obtain ⟨a, ha⟩ := hσ
    exact Finset.prod_eq_zero (Finset.mem_univ a) (hF a (σ a) ha)
  rw [← Finset.sum_subset (Finset.subset_univ P) hvanish]
  -- the right-hand side is a sum over families of block permutations
  rw [Finset.prod_univ_sum]
  set J : Equiv.Perm α → (∀ k : κ, Equiv.Perm {a : α // blk a = k}) :=
    fun σ => if h : ∀ a, blk (σ a) = blk a then permBlockRestrict blk σ h else fun _ => 1 with hJ
  refine (Finset.sum_nbij' (i := fun τ => blockPerm blk τ) (j := J) ?_ ?_ ?_ ?_ ?_).symm
  · intro τ _
    rw [hmemP]
    exact blk_blockPerm blk _
  · intro σ _
    exact Finset.mem_univ _
  · intro τ _
    show J (blockPerm blk τ) = τ
    rw [hJ]
    simp only [dif_pos (blk_blockPerm blk τ)]
    exact permBlockRestrict_blockPerm blk τ
  · intro σ hσ
    show blockPerm blk (J σ) = σ
    rw [hJ]
    simp only [dif_pos (hmemP.mp hσ)]
    exact blockPerm_permBlockRestrict blk σ (hmemP.mp hσ)
  · intro τ _
    rw [← Fintype.prod_sigma
      (fun p : Σ k : κ, {a : α // blk a = k} =>
        F (p.2 : α) ((τ p.1 p.2 : {a : α // blk a = p.1}) : α))]
    refine Fintype.prod_equiv (Equiv.sigmaFiberEquiv blk)
      (fun p : Σ k : κ, {a : α // blk a = k} =>
        F (p.2 : α) ((τ p.1 p.2 : {a : α // blk a = p.1}) : α))
      (fun a : α => F a (blockPerm blk τ a)) ?_
    rintro ⟨k, ⟨a, rfl⟩⟩
    rw [blockPerm_apply]
    rfl

end

end GaloisForLFunctions.HTGeometry
