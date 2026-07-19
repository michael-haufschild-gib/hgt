import GaloisForLFunctions.HTGeometry.HamburgerExistence
import GaloisForLFunctions.HTGeometry.ChristoffelPointMass

/-!
# Atoms of the constructed measure

The representing measure built from a positive definite moment form inherits the atom bound that
holds for every representing measure: its mass at any point is at most the limit Christoffel
function there.

This is the first statement combining the construction with the variational theory — until now the
atom bound applied only to measures assumed to exist, and the construction produced a measure with
no information about its atoms.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A representing measure with controlled atoms exists.**  Combining the construction with the
variational bound: the measure produced from the moment sequence charges each point by at most the
limit Christoffel function. -/
theorem exists_finiteMeasure_atoms_le_christoffelLimit (h : PositiveMomentForm s) :
    ∃ nu : Measure ℝ, IsFiniteMeasure nu ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu ∧
      ∀ x : ℝ, nu.real {x} ≤ christoffelLimit s x := by
  obtain ⟨nu, hfin, hmom⟩ := exists_finiteMeasure_hasHamburgerMoments h
  exact ⟨nu, hfin, hmom,
    fun x => measureReal_singleton_le_christoffelLimit_of_hasMoments h hmom x⟩

/-- Where the limit Christoffel function vanishes, the constructed measure has no atom. -/
theorem exists_finiteMeasure_atomless_where_christoffelLimit_eq_zero
    (h : PositiveMomentForm s) :
    ∃ nu : Measure ℝ, IsFiniteMeasure nu ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu ∧
      ∀ x : ℝ, christoffelLimit s x = 0 → nu.real {x} = 0 := by
  obtain ⟨nu, hfin, hmom, hatom⟩ := exists_finiteMeasure_atoms_le_christoffelLimit h
  refine ⟨nu, hfin, hmom, fun x hx => ?_⟩
  exact le_antisymm (hx ▸ hatom x) measureReal_nonneg

end HTGeometry
