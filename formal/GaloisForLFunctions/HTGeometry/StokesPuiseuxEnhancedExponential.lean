import GaloisForLFunctions.HTGeometry.StokesAnalyticWallEnhancedExponential

/-!
# Puiseux branch pairs as enhanced exponential objects

The coefficient-generated leading phase of every distinct finite Puiseux branch pair defines
actual ind-sheaf, derived, and generated enhanced-quotient objects. Its cellular wall labels land
on zero-level support through the analytic wall equivalence.
-/

open CategoryTheory Topology

namespace GaloisForLFunctions.IrregularStokes.AnalyticWall

open CompactIndSheaf EnhancedIndPullback EnhancedExponential CellularMicrolocal

/-- Actual dominance phase of a distinct coefficient-generated Puiseux branch pair. -/
noncomputable def branchPairStokesPhase {m K N : ℕ} (p : FinitePuiseuxFamily m K N)
    {i j : Fin m} (hij : i ≠ j) : Real.Angle → ℝ :=
  stokesPhase (branchPairLeadingCoefficient p hij) (p.contactNumerator i j)

/-- A branch-pair dominance phase is continuous on the real oriented boundary circle. -/
theorem continuous_branchPairStokesPhase {m K N : ℕ} (p : FinitePuiseuxFamily m K N)
    {i j : Fin m} (hij : i ≠ j) :
    Continuous (branchPairStokesPhase p hij) := by
  simpa only [branchPairStokesPhase] using
    continuous_stokesPhase_angle (branchPairLeadingCoefficient p hij)
      (p.contactNumerator i j)

/-- Ind-sheaf exponential object of an actual Puiseux branch-pair phase. -/
noncomputable def branchPairStokesPhaseExponentialIndSheaf {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :=
  compactifiedExponentialIndSheaf (TopCat.of Real.Angle) (branchPairStokesPhase p hij)
    (continuous_branchPairStokesPhase p hij)

/-- Unbounded derived exponential object of an actual Puiseux branch-pair phase. -/
noncomputable def branchPairStokesPhaseExponentialDerivedObject {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :=
  compactifiedExponentialDerivedObject (TopCat.of Real.Angle) (branchPairStokesPhase p hij)
    (continuous_branchPairStokesPhase p hij)

/-- Bounded derived exponential object of an actual Puiseux branch-pair phase. -/
noncomputable def branchPairStokesPhaseExponentialBoundedDerivedObject {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :=
  compactifiedExponentialBoundedDerivedObject (TopCat.of Real.Angle)
    (branchPairStokesPhase p hij) (continuous_branchPairStokesPhase p hij)

/-- Unbounded generated-enhanced exponential object of an actual Puiseux branch pair. -/
noncomputable def branchPairStokesPhaseExponentialEnhancedObject {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :=
  compactifiedExponentialEnhancedObject (TopCat.of Real.Angle) (branchPairStokesPhase p hij)
    (continuous_branchPairStokesPhase p hij)

/-- Bounded generated-enhanced exponential object of an actual Puiseux branch pair. -/
noncomputable def branchPairStokesPhaseExponentialBoundedEnhancedObject {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :=
  compactifiedExponentialBoundedEnhancedObject (TopCat.of Real.Angle)
    (branchPairStokesPhase p hij) (continuous_branchPairStokesPhase p hij)

/-- Every analytic wall of an actual Puiseux branch pair lies on zero-level support. -/
theorem branchPairAnalyticWall_mem_zeroLevel {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j)
    (θ : AnalyticStokesWall (branchPairLeadingCoefficient p hij)
      (p.contactNumerator i j)) :
    compactifiedExponentialEpigraph (branchPairStokesPhase p hij) (θ.1, (0 : ℝ)) := by
  simpa only [branchPairStokesPhase] using
    analyticStokesWall_mem_zeroLevel (branchPairLeadingCoefficient p hij)
      (p.contactNumerator i j) θ

/-- Every cellular wall label of an actual Puiseux branch pair lands on zero-level support under
the canonical analytic realization. -/
theorem branchPairLabelledWall_mem_zeroLevel {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j)
    (w : StokesWall (p.contactNumerator i j)) :
    compactifiedExponentialEpigraph (branchPairStokesPhase p hij)
      ((branchPairWallEquivAnalytic p hij w).1, (0 : ℝ)) :=
  branchPairAnalyticWall_mem_zeroLevel p hij (branchPairWallEquivAnalytic p hij w)

end GaloisForLFunctions.IrregularStokes.AnalyticWall
