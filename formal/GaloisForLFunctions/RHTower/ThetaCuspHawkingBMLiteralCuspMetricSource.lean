import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCovectorEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalMetricSource

/-!
# Literal cusp scalar/vector inputs to the complete metric source

The complete infinite scalar cusp field and its actual area-form rotated gradient
supply the horizon fields. Their regularity, scalar equation, covariant divergence
and rough vector equation are conclusions. Substitution into the fundamental
metric recipe therefore needs no supplied angular regularity or field equation.

These local identities hold for every complex parameter. They do not assert
nonvanishing, global quotient admissibility, the reconstructed first-order Einstein
equation, nonlinear gauge completion, causal projection or Hawking-clock extinction.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
open ComplexCoordinateMetricTwoJet
namespace RHTower.D4BMLiteralCusp
noncomputable section

/-- The full pre-existing scalar cusp leg, including both Weyl terms and all modes. -/
def scalar (u : ℂ) : D4BMHorizon.Field :=
  fun z => d4BMCompletedEisensteinCuspLeg .scalar u (z 0) (z 1)

/-- The actual coexact covector of that same complete scalar field. -/
def vector (u : ℂ) : D4BMHorizon.Covector := D4BMHorizon.coexact (scalar u)

/-- Scalar eigenvalue in the sign convention `Delta S = -q S`. -/
def scalarQ (u : ℂ) : ℂ := 1 / 4 - u ^ (2 : ℕ)

/-- Radial square-root parameter matched to the actual cusp equation. -/
def radialMomentum (u : ℂ) : ℂ := -Complex.I * u

/-- The radial effective parameter is the derived scalar eigenvalue. -/
theorem scalarQ_eq_radialMomentum (u : ℂ) :
    scalarQ u = 1 / 4 + radialMomentum u ^ (2 : ℕ) := by
  simp [scalarQ, radialMomentum, mul_pow, Complex.I_sq, sub_eq_add_neg]

/-- Every finite scalar spatial jet is supplied by the literal infinite series. -/
theorem scalar_contDiffAt (u : ℂ) (k : ℕ) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    ContDiffAt ℝ k (scalar u) z := D4BMAngularSeries.cuspLeg_contDiffAt .scalar u k z hz

/-- Every finite vector jet follows from one further scalar derivative. -/
theorem vector_contDiffAt (u : ℂ) (k : ℕ) (z : D4BMHorizon.Point)
    (hz : 0 < z 1) (i : Fin 2) : ContDiffAt ℝ k (vector u i) z := by
  exact D4BMHorizon.coexact_contDiffAt (scalar_contDiffAt u (k + 1) z hz) i

/-- The scalar cusp equation uses the actual metric connection and inverse metric. -/
theorem scalar_equation (u : ℂ) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    D4BMHorizon.scalarLaplacian (scalar u) z = -scalarQ u * scalar u z := by
  rw [D4BMHorizon.scalarLaplacian_eq _ z hz]
  change D4BMAngularSeries.hyperbolicLaplacian
    (fun q => d4BMCompletedEisensteinCuspLeg .scalar u (q 0) (q 1)) z = _
  rw [D4BMAngularSeries.scalarCusp_hyperbolicLaplacian u z hz]
  dsimp [scalarQ, scalar]
  ring

/-- The literal coexact cusp covector is covariantly divergence-free. -/
theorem vector_divergence (u : ℂ) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    D4BMHorizon.divergence (vector u) z = 0 :=
  D4BMHorizon.coexact_divergence (scalar u) z hz (scalar_contDiffAt u 2 z hz)

/-- The previously defined vector spectral shift is now the actual field equation. -/
theorem vector_equation (u : ℂ) (z : D4BMHorizon.Point) (hz : 0 < z 1) (i : Fin 2) :
    D4BMHorizon.roughLaplacian (vector u) i z =
      -d4HyperbolicHodgePairedVectorEigenvalue (scalarQ u) * vector u i z :=
  D4BMHorizon.coexact_eigen_equation (scalar u) (scalarQ u) z hz
    (scalar_contDiffAt u 3 z hz) (scalar_equation u) i

/-- Complete fundamental metric fields with the matched literal scalar/vector inputs. -/
def perturbation (omega u aS aV : ℂ) : D4BMActualMetricSource.MetricField :=
  D4BMFundamentalMetric.perturbation omega (scalarQ u) aS aV (scalar u) (vector u)

/-- Explicit complete metric jet after substituting the literal cusp fields. -/
def fullJet (p : D4BMBackground.ExteriorPoint) (omega u aS aV : ℂ) :
    CoordinateMetricTwoJet 4 ℂ :=
  D4BMFundamentalMetric.fullJet p omega (scalarQ u) aS aV (scalar u) (vector u)

/-- Angular regularity is discharged for every primitive of the literal reconstruction. -/
theorem primitives_contDiffAt (p : D4BMBackground.ExteriorPoint) (omega u aS aV : ℂ)
    (b : D4BMMetricReconstruction.Primitive) :
    ContDiffAt ℝ 2 (D4BMFundamentalMetric.primitives omega aS aV (scalar u) (vector u) b) p.val :=
  D4BMFundamentalMetric.primitives_contDiffAt p omega aS aV (scalar u) (vector u)
    (scalar_contDiffAt u 2 _ p.property.2) (vector_contDiffAt u 2 _ p.property.2) b

/-- The literal metric reconstruction's full jet is its actual coordinate jet. -/
theorem fullJet_correct (p : D4BMBackground.ExteriorPoint) (omega u aS aV : ℂ) :
    fullJet p omega u aS aV = D4BMMetricReconstruction.ofMetricField
      (perturbation omega u aS aV) p.val :=
  D4BMFundamentalMetric.fullJet_correct p omega (scalarQ u) aS aV (scalar u) (vector u)
    (scalar_contDiffAt u 2 _ p.property.2) (vector_contDiffAt u 2 _ p.property.2)

/-- Actual direct quadratic/cubic Einstein coefficients with all literal inputs substituted. -/
theorem source_coefficients (p : D4BMBackground.ExteriorPoint) (omega u aS aV : ℂ)
    (i j : Fin 4) :
    let h := perturbation omega u aS aV
    let v := toSpace (fullJet p omega u aS aV)
    (iteratedDeriv 2 (D4BMActualMetricSource.source p h i j) 0 / 2 =
      secondVariation (D4BMActualMetricSource.backgroundSpace p) i j v v / 2) ∧
    (iteratedDeriv 3 (D4BMActualMetricSource.source p h i j) 0 / 6 =
      thirdVariation (D4BMActualMetricSource.backgroundSpace p) i j v v v / 6) :=
  D4BMFundamentalMetric.source_coefficients p omega (scalarQ u) aS aV (scalar u) (vector u)
    (scalar_contDiffAt u 2 _ p.property.2) (vector_contDiffAt u 2 _ p.property.2) i j

end
end RHTower.D4BMLiteralCusp
