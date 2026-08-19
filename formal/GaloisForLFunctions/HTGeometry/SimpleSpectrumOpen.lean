/-
# The simple-spectrum locus of a continuous Hermitian family is open

Simplicity of the spectrum is a *finite* set of separation conditions once the spectrum is labelled
canonically, and the canonical labelling is continuous.  So the parameters carrying a simple
spectrum form an open set, and a single simple parameter makes it nonempty.

Main results:
* `injective_iff_injective_sortedTuple` — injectivity is invariant under the rearrangement.
* `isOpen_simpleSpectrumLocus` — **the simple-spectrum locus is open**.
-/
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

theorem injective_iff_injective_sortedTuple (a : Fin D → ℝ) :
    Function.Injective a ↔ Function.Injective (sortedTuple a) := by
  constructor
  · exact fun h => h.comp (Tuple.sort a).injective
  · intro h i j hij
    have : sortedTuple a ((Tuple.sort a).symm i) = sortedTuple a ((Tuple.sort a).symm j) := by
      rw [sortedTuple_symm_apply, sortedTuple_symm_apply]
      exact hij
    have hsymm := h this
    exact (Tuple.sort a).symm.injective hsymm

/-- **The simple-spectrum locus of a continuous Hermitian family is open.** -/
theorem isOpen_simpleSpectrumLocus {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → Matrix (Fin D) (Fin D) ℂ} (hF : Continuous F)
    (hHerm : ∀ x, (F x).IsHermitian) :
    IsOpen {x : X | Function.Injective (hHerm x).eigenvalues} := by
  classical
  have hsort : Continuous (fun x => sortedTuple (hHerm x).eigenvalues) :=
    continuous_sortedTuple_eigenvalues hF hHerm
  have hset : {x : X | Function.Injective (hHerm x).eigenvalues}
      = ⋂ p ∈ (Finset.univ : Finset (Fin D × Fin D)).filter (fun p => p.1 ≠ p.2),
          {x : X | sortedTuple (hHerm x).eigenvalues p.1
            ≠ sortedTuple (hHerm x).eigenvalues p.2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [injective_iff_injective_sortedTuple]
    constructor
    · intro h p hp hcon
      exact hp (h hcon)
    · intro h i j hij
      by_contra hne
      exact h (i, j) hne hij
  rw [hset]
  refine isOpen_biInter_finset fun p _ => ?_
  exact isOpen_ne_fun ((continuous_apply p.1).comp hsort) ((continuous_apply p.2).comp hsort)

end

end GaloisForLFunctions.HTGeometry
