import GaloisForLFunctions.HTGeometry.CompactIntervalL2Pairing
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Density in `L²` of a compact interval

Towards a countable Hilbert basis of `L²[-a,a]`, which mathlib does not provide: it has no
separability instance for `Lp` at all, and no isometry identifying `L²` of an interval with `L²` of
the circle where the Fourier basis lives.

The first step is density of the bounded continuous functions.  The measure is the restriction of
Lebesgue measure to a compact interval, so it is finite and weakly regular, which is exactly what
mathlib's density theorem needs — no compactness of the ambient space is required.

The `L²` norm of a bounded continuous function is controlled by its supremum norm times the square
root of the total mass, so uniform approximation on the interval suffices to approximate in `L²`.
This is what will let Stone–Weierstrass supply a countable total family.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- The measure of a compact symmetric interval is finite. -/
theorem intervalL2_measure_ne_top (a : ℝ) :
    (volume.restrict (Set.Icc (-a) a)) Set.univ ≠ ⊤ := by
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **The bounded continuous functions are dense in `L²` of a compact interval.**  The restricted
Lebesgue measure is finite and weakly regular, which is all mathlib's density theorem requires. -/
theorem denseRange_boundedContinuousToIntervalL2 (a : ℝ) :
    DenseRange (BoundedContinuousFunction.toLp (E := ℂ) 2
      (volume.restrict (Set.Icc (-a) a)) ℂ) :=
  BoundedContinuousFunction.toLp_denseRange _ _ ℂ (by norm_num)

/-- Every element of `L²` of the interval is a limit of bounded continuous functions. -/
theorem exists_boundedContinuous_close (a : ℝ) (f : IntervalL2 a) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : BoundedContinuousFunction ℝ ℂ,
      ‖BoundedContinuousFunction.toLp (E := ℂ) 2 (volume.restrict (Set.Icc (-a) a)) ℂ g - f‖
        < eps := by
  obtain ⟨y, hy, hclose⟩ :=
    Metric.mem_closure_iff.mp
      ((denseRange_boundedContinuousToIntervalL2 a).closure_eq ▸ Set.mem_univ f) eps heps
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, ?_⟩
  rw [hg, ← dist_eq_norm, dist_comm]
  exact hclose

end GaloisForLFunctions.HTGeometry
