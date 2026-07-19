import GaloisForLFunctions.HTGeometry.NevFamilyConsequences

/-!
# A bounded kernel forces indeterminacy

The leaves of distinct parameters are distinct measures and all of them represent the sequence, so a
moment sequence whose kernel is bounded at a point has more than one representing measure: it is an
indeterminate moment problem.

This closes the loop with the hypothesis the construction runs on — `BoundedKernel s 0` is not merely
a convenient technical assumption but exactly a witness of indeterminacy.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A bounded kernel forces indeterminacy.**  Two distinct probability measures represent the
sequence: the leaf of the parameter `0` and the leaf of the parameter at infinity. -/
theorem exists_ne_hasHamburgerMoments (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    ∃ μ ν : Measure ℝ, μ ≠ ν ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν := by
  refine ⟨(nevLeaf h h0b h0 ((0 : ℝ) : OnePoint ℝ) : Measure ℝ),
    (nevLeaf h h0b h0 ∞ : Measure ℝ), ?_,
    nevLeaf_hasHamburgerMoments h h0b h0 _, nevLeaf_hasHamburgerMoments h h0b h0 _⟩
  intro hc
  have hsub : nevLeaf h h0b h0 ((0 : ℝ) : OnePoint ℝ) = nevLeaf h h0b h0 ∞ := Subtype.ext hc
  exact absurd (nevLeaf_injective h h0b h0 hsub) (OnePoint.coe_ne_infty (0 : ℝ))

/-- **The representing measures are at least a continuum.**  The leaf map is injective on the
parameter space, so the solution set of the moment problem contains a copy of `ℝ ∪ {∞}`. -/
theorem injective_leaf_into_representing (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    ∃ F : OnePoint ℝ → Measure ℝ, Function.Injective F ∧
      ∀ t, GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (F t) := by
  refine ⟨fun t => (nevLeaf h h0b h0 t : Measure ℝ), ?_,
    fun t => nevLeaf_hasHamburgerMoments h h0b h0 t⟩
  intro t₁ t₂ hEq
  exact nevLeaf_injective h h0b h0 (Subtype.ext hEq)

/-- **The moment problem is not determinate.**  No single measure represents the sequence. -/
theorem not_subsingleton_representing (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    ¬ (∀ μ ν : Measure ℝ,
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ →
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν → μ = ν) := by
  intro hall
  obtain ⟨μ, ν, hne, hμ, hν⟩ := exists_ne_hasHamburgerMoments h h0b h0
  exact hne (hall μ ν hμ hν)

end HTGeometry
