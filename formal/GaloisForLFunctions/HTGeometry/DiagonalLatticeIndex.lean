import GaloisForLFunctions.HTGeometry.DifferentialOperatorCyclicDimension
import GaloisForLFunctions.HTGeometry.SubspaceRelativeDimension

/-!
# The index of a diagonal lattice pair

For a diagonal family of nonzero operators the relative index of the free module against the
diagonal lattice is the sum of the orders:

`relIndex (∏ᵢ K[∂;δ] dᵢ) ⊤ = ∑ᵢ deg dᵢ`.

This anchors the lattice-distance invariant used in the Cartan comparison: on a diagonal pair it
returns exactly the sum of the elementary divisor orders.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The relative dimension of the whole space over a subspace is the dimension of the quotient. -/
theorem quotDim_top (A : Submodule K V) :
    quotDim A ⊤ = Module.finrank K (V ⧸ A) := by
  rw [quotDim, Submodule.map_top, Submodule.range_mkQ]
  exact finrank_top K (V ⧸ A)

theorem relIndex_top (A : Submodule K V) :
    relIndex A ⊤ = (Module.finrank K (V ⧸ A) : ℤ) := by
  rw [relIndex, quotDim_top, quotDim_of_le le_top]
  omega

/-- The prefix invariant attached to the single full cut is the relative index. -/
theorem relIndexSup_top_cut {ι' : Type*} [Nonempty ι'] (L M : Submodule K V) :
    relIndexSup (fun _ : ι' => (⊤ : Submodule K V)) L M = relIndex L M := by
  have hfun : (fun i : ι' => relIndex (L ⊓ ⊤) (M ⊓ ⊤)) = fun _ : ι' => relIndex L M := by
    funext i
    rw [inf_top_eq, inf_top_eq]
  rw [relIndexSup, hfun]
  simp

namespace DiffOp

variable [Differential K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The index of a diagonal lattice pair.** -/
theorem relIndex_pi_leftMultiples_top (d : ι → DiffOp K) (hd : ∀ i, d i ≠ 0) :
    relIndex (Submodule.pi Set.univ fun i => leftMultiples (d i)) ⊤
      = ((∑ i, degree (d i) : ℕ) : ℤ) := by
  rw [relIndex_top, finrank_quotient_pi_leftMultiples d hd]

end DiffOp

end

end GaloisForLFunctions.HTGeometry
