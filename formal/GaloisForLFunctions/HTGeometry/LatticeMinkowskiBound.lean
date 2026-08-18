import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Minkowski's bound on the shortest vector of a lattice

Minkowski's convex body theorem, applied to a ball, bounds the length of a shortest nonzero lattice
vector by the covolume: a ball whose volume exceeds `2^n` times the covolume already contains a
nonzero lattice point.  This is the bound that makes the well-rounded locus of the space of lattices
compact, and hence the source of cocompactness in reduction theory.

* `exists_ne_zero_norm_le_of_covolume` : **a ball of large enough volume contains a nonzero lattice
  vector.**
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory MeasureTheory.Measure Module Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [IsAddHaarMeasure μ]

/-- **Minkowski's bound.**  A ball whose volume exceeds `2 ^ n` times the covolume of a lattice
contains a nonzero lattice vector. -/
theorem exists_ne_zero_norm_le_of_covolume {L : AddSubgroup E} [Countable L] {F : Set E}
    (fund : IsAddFundamentalDomain L F μ) {r : ℝ}
    (h : μ F * 2 ^ finrank ℝ E < μ (closedBall (0 : E) r)) :
    ∃ v ∈ L, v ≠ (0 : E) ∧ ‖v‖ ≤ r := by
  obtain ⟨x, hx, hmem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (μ := μ) (F := F) (s := closedBall (0 : E) r) fund
    (fun y hy => by simpa using hy) (convex_closedBall _ _) h
  refine ⟨(x : E), x.2, ?_, ?_⟩
  · simpa using fun hcon => hx (Subtype.ext hcon)
  · simpa [Metric.mem_closedBall, dist_zero_right] using hmem

end GaloisForLFunctions.HTGeometry
