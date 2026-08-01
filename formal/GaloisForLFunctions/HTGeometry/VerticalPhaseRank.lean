import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative
import GaloisForLFunctions.HTGeometry.HullJetPhaseRank

/-!
# Finite phase rank on a vertical line

The restriction of a strip almost periodic holomorphic function to the central line of the strip is
a bounded continuous almost periodic function, so it has a phase carrier.  If that carrier admits an
injective continuous jet sample into `ℂ^N` — the analytic input supplied by an algebraic differential
equation — its frequency group has rational rank at most `2N`.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The restriction of a strip almost periodic holomorphic function to the central line, packaged as
a bounded continuous function on `ℝ`. -/
noncomputable def verticalRestriction (F : ℂ → ℂ) {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) : ℝ →ᵇ ℂ :=
  toBC (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I))
    (continuous_line_restriction hR hF)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic (continuous_line_restriction hR hF)
      (isBohrAlmostPeriodic_line hR hap))

theorem verticalRestriction_apply (F : ℂ → ℂ) {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) (t : ℝ) :
    verticalRestriction F hR hF hap t = F ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

/-- **Finite phase rank of a strip almost periodic holomorphic function.**  If the phase carrier of
its restriction to the central line admits an injective continuous jet sample into `ℂ^N`, then the
rational rank of the frequency group is at most `2N`. -/
theorem rank_frequencies_le_of_vertical {F : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    [MeasurableSpace (BohrHull (verticalRestriction F hR hF hap))]
    [BorelSpace (BohrHull (verticalRestriction F hR hF hap))] {N : ℕ}
    {J : BohrHull (verticalRestriction F hR hF hap) → (Fin N → ℂ)}
    (hJcont : Continuous J) (hJinj : Function.Injective J) :
    Module.rank ℤ (bohrHullFrequencies (verticalRestriction F hR hF hap))
      ≤ ((2 * N : ℕ) : Cardinal) := by
  have hcont : Continuous fun t : ℝ => (verticalRestriction F hR hF hap) t :=
    continuous_line_restriction hR hF
  have hapline : IsBohrAlmostPeriodic fun t : ℝ => (verticalRestriction F hR hF hap) t :=
    isBohrAlmostPeriodic_line hR hap
  have huc : UniformContinuous fun t : ℝ => (verticalRestriction F hR hF hap) t :=
    uniformContinuous_of_isBohrAlmostPeriodic hcont hapline
  have htb : HasTotallyBoundedOrbit fun t : ℝ => (verticalRestriction F hR hF hap) t :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapline
  exact rank_bohrHullFrequencies_le_two_mul huc htb hJcont hJinj

end GaloisForLFunctions
