import GaloisForLFunctions.HTGeometry.ConstrainedCauchyJetControllability
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensional closure bridge for density controls

A continuous linear control into a finite-dimensional target is onto as soon as the closure of its
range contains a family of columns whose finite linear combinations are onto.  This separates the
finite Cauchy-column algebra from the later measure-theoretic approximation by bounded densities.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology

noncomputable section

/-- A continuous linear map into a finite-dimensional target is surjective if the closure of its
range contains a spanning family. -/
theorem continuousLinearMap_surjective_of_spanning_columns_mem_closure_range
    {𝕜 X V κ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : X →L[𝕜] V) (column : κ → V)
    (hspan : Submodule.span 𝕜 (Set.range column) = ⊤)
    (hclosure : ∀ k, column k ∈ closure (Set.range T)) :
    Function.Surjective T := by
  have hrangeClosed : IsClosed (LinearMap.range T.toLinearMap : Set V) :=
    (LinearMap.range T.toLinearMap).closed_of_finiteDimensional
  have hcolumnRange : ∀ k, column k ∈ LinearMap.range T.toLinearMap := by
    intro k
    exact (closure_minimal
      (by
        intro y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨x, rfl⟩)
      hrangeClosed) (hclosure k)
  have hspan_le : Submodule.span 𝕜 (Set.range column) ≤ LinearMap.range T.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    exact hcolumnRange k
  have hrangeTop : LinearMap.range T.toLinearMap = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hspan_le
  exact LinearMap.range_eq_top.mp hrangeTop

/-- It suffices that the finitely supported linear-combination map of the columns is onto. -/
theorem continuousLinearMap_surjective_of_finsupp_columns_mem_closure_range
    {𝕜 X V κ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : X →L[𝕜] V) (column : κ → V)
    (hfinite : Function.Surjective (Finsupp.linearCombination 𝕜 column))
    (hclosure : ∀ k, column k ∈ closure (Set.range T)) :
    Function.Surjective T := by
  apply continuousLinearMap_surjective_of_spanning_columns_mem_closure_range T column
  · rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top.mpr hfinite
  · exact hclosure

end
end GaloisForLFunctions.HTGeometry
