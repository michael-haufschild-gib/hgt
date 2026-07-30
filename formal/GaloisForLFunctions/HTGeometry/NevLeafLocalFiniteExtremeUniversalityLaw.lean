import GaloisForLFunctions.HTGeometry.FiberClosed
import GaloisForLFunctions.HTGeometry.FiberFinite
import GaloisForLFunctions.HTGeometry.LeafExtreme

/-!
# Nevanlinna leaf local-finite extremality universality

Canonical Nevanlinna leaves may be globally infinite, but every compact observation is exactly
supported on a finite denominator-fibre section.  This locally finite tomography is compatible with
global convex rigidity: a half-half representing-measure decomposition of a leaf is trivial.
-/

open scoped BigOperators OnePoint
open MeasureTheory OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Every compact restriction of a canonical finite-parameter leaf is exactly its restriction to
the finite intersection of that compact with the denominator fibre. -/
theorem nevLeaf_compactRestriction_eq_finiteDenominatorSection
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ A : Set ℝ, A.Finite ∧ A ⊆ K ∧
      (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict K =
        (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict A := by
  let fiber := (nevMatrixDataInf h h0b).finiteDenominatorFiber tau
  refine ⟨fiber ∩ K, ?_, Set.inter_subset_right, ?_⟩
  · exact finite_finiteDenominatorFiber_inter h h0b tau hK
  · have hrestrict :
        (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict fiber =
          (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      simpa only [fiber] using! nevLeaf_finite_carried h h0b h0 tau
    calc
      (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict K =
          ((nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict fiber).restrict K := by
            rw [hrestrict]
      _ = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict (K ∩ fiber) :=
        Measure.restrict_restrict hK.measurableSet
      _ = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict (fiber ∩ K) := by
        rw [Set.inter_comm]

/-- **Local-finite extreme-leaf law.**  Every compact observation of a canonical leaf has an exact
finite support section, while every probability-measure half decomposition with the same complete
moments collapses globally to that leaf. -/
theorem nevLeaf_localFiniteObservation_and_globalExtreme
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) {K : Set ℝ} (hK : IsCompact K) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    (hν : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν)
    (hmix : (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) =
      (1 / 2 : ENNReal) • μ + (1 / 2 : ENNReal) • ν) :
    (∃ A : Set ℝ, A.Finite ∧ A ⊆ K ∧
      (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict K =
        (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ).restrict A) ∧
      μ = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) ∧
      ν = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := by
  exact ⟨nevLeaf_compactRestriction_eq_finiteDenominatorSection h h0b h0 tau hK,
    nevLeaf_of_half_mixture h h0b h0 tau hμ hν hmix⟩

end HTGeometry
