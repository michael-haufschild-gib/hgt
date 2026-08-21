import GaloisForLFunctions.HTGeometry.HomotopyEquivHomology
import Mathlib.Analysis.Convex.Star

/-!
# Star-shaped sets are contractible

A set star-shaped about one of its points is contracted to that point by the straight-line homotopy,
which stays inside the set by definition of star-convexity.  Hence the singular homology of a
star-shaped set vanishes in positive degrees.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight-line contraction of a star-shaped set onto its centre. -/
noncomputable def starHomotopy {S : Set E} {x₀ : E} (hx₀ : x₀ ∈ S) (hS : StarConvex ℝ x₀ S) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥S) (ContinuousMap.const ↥S ⟨x₀, hx₀⟩) where
  toFun := fun p => ⟨(1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • x₀, by
    have h := hS (p.2).2 (a := (p.1 : ℝ)) (b := 1 - (p.1 : ℝ)) (unitInterval.nonneg p.1)
      (by linarith [unitInterval.le_one p.1]) (by ring)
    rwa [add_comm] at h⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  map_zero_left := by
    intro y
    refine Subtype.ext ?_
    show (1 - (0 : ℝ)) • (y : E) + (0 : ℝ) • x₀ = (y : E)
    simp
  map_one_left := by
    intro y
    refine Subtype.ext ?_
    show (1 - (1 : ℝ)) • (y : E) + (1 : ℝ) • x₀ = x₀
    simp

/-- **A star-shaped set has no homology in positive degrees.** -/
theorem isZero_homology_starConvex {S : Set E} {x₀ : E} (hx₀ : x₀ ∈ S)
    (hS : StarConvex ℝ x₀ S) (k : ℕ) :
    Limits.IsZero ((singChainComplex R ↥S).homology (k + 1)) :=
  isZero_homology_of_homotopy_const R (starHomotopy hx₀ hS) k

end GaloisForLFunctions.HTGeometry
