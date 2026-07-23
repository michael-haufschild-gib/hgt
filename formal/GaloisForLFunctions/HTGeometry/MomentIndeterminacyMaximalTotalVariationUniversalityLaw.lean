import GaloisForLFunctions.HTGeometry.NevExtremalFamily
import GaloisForLFunctions.HTGeometry.FiberClosed
import GaloisForLFunctions.HTGeometry.MutuallySingularTotalVariation

/-!
# Moment-indeterminacy maximal-total-variation universality law

A bounded-kernel Hamburger moment problem does not merely have distinct representing measures.
Its finite Nevanlinna leaves all have the same complete moment sequence while every distinct pair
is mutually singular and therefore has maximal total-variation mass two.
-/

open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

noncomputable section

/-- **Moment-indeterminacy maximal-total-variation universality law.**  Every normalized positive
moment sequence with bounded kernel carries a real-parameter family of probability measures with
identical complete moments, and every distinct pair is mutually singular with total-variation mass
exactly two. -/
theorem exists_momentIdentical_pairwiseMaximalTotalVariation_family
    {s : ℕ → ℝ} (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    ∃ leaf : ℝ → ProbabilityMeasure ℝ,
      (∀ t : ℝ,
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
          (leaf t : Measure ℝ)) ∧
      ∀ t u : ℝ, t ≠ u →
        (leaf t : Measure ℝ) ⟂ₘ (leaf u : Measure ℝ) ∧
        (((leaf t : Measure ℝ).toSignedMeasure -
              (leaf u : Measure ℝ).toSignedMeasure).totalVariation Set.univ = 2) := by
  let F := nevExtremalFamily h h0b h0
  let leaf : ℝ → ProbabilityMeasure ℝ :=
    fun t => F.leaf (t : OnePoint ℝ)
  refine ⟨leaf, ?_, ?_⟩
  · intro t
    exact F.leaf_moments (t : OnePoint ℝ)
  · intro t u htu
    have hsing :
        (F.leaf (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
          (F.leaf (u : OnePoint ℝ) : Measure ℝ) :=
      mutuallySingular_leaf F htu
    refine ⟨?_, ?_⟩
    · simpa [leaf] using hsing
    · simpa [leaf] using
        totalVariation_univ_eq_of_isProbability
          (F.leaf (t : OnePoint ℝ) : Measure ℝ)
          (F.leaf (u : OnePoint ℝ) : Measure ℝ) hsing

end

end HTGeometry
