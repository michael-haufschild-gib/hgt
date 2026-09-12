import GaloisForLFunctions.HTGeometry.ComplexMetricEinsteinConservation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralMetricBianchi

set_option autoImplicit false
namespace RHTower.D4BMLiteralConservation
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet Filter Topology
noncomputable section

/-- The original cosmological Einstein source as a field on the real coordinate chart. -/
def sourceField (h : MetricField) (ε : ℂ) : MetricField := fun x =>
  (ofMetricField (perturbedMetric h ε) x).einstein-(3 : ℂ) • perturbedMetric h ε x

/-- Every exterior component is exactly the already defined literal affine source. -/
theorem sourceField_apply (p : ExteriorPoint) (h : MetricField) (ε : ℂ) (i j : Fin 4) :
    sourceField h ε p.val i j = source p h i j ε := rfl

/-- Conservation is applied to the original source, including its fixed cosmological term. -/
theorem sourceField_eq_literalEinstein (h : MetricField) (ε : ℂ) :
    sourceField h ε = ComplexMetricField.literalEinstein (perturbedMetric h ε) (-3) := by
  ext x i j
  change (ofMetricField (perturbedMetric h ε) x).einstein i j-3*perturbedMetric h ε x i j =
    (ofMetricField (perturbedMetric h ε) x).einstein i j+(-3)*perturbedMetric h ε x i j
  ring

/-- Symmetry of the actual complete literal cusp perturbation. -/
theorem literal_symm (omega u aS aV : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    D4BMLiteralCusp.perturbation omega u aS aV x i j =
      D4BMLiteralCusp.perturbation omega u aS aV x j i := by
  let a := fun b => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) b x
  have hs := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) i j)
  rw [covariantMetricExpression_eval,covariantMetricExpression_eval] at hs
  exact hs

/-- Symmetry is inherited by the complete amplitude-dependent literal metric. -/
theorem metric_symm (omega u aS aV ε : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x i j =
      perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x j i := by
  have hb : metric (x 1) (x 3) i j = metric (x 1) (x 3) j i := by
    by_cases hij : i = j
    · subst j; rfl
    · simp [metric,hij,Ne.symm hij]
  change metric (x 1) (x 3) i j+ε*D4BMLiteralCusp.perturbation omega u aS aV x i j = _
  rw [hb,literal_symm omega u aS aV x i j]
  rfl

/-- The original full source is covariantly conserved on a genuine amplitude neighborhood.
Literal field regularity, symmetry and background nondegeneracy are discharged here. -/
theorem literal_source_conservation_near_zero (p : ExteriorPoint) (omega u aS aV : ℂ) :
    ∀ᶠ ε : ℂ in 𝓝 0, ∀ j : Fin 4,
      ComplexMetricField.tensorDivergence
        (perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε)
        (sourceField (D4BMLiteralCusp.perturbation omega u aS aV) ε) p.val j = 0 := by
  let h := D4BMLiteralCusp.perturbation omega u aS aV
  have hd : Continuous (fun ε : ℂ => (perturbedMetric h ε p.val).det) := by
    simp only [Matrix.det_apply',perturbedMetric,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  have h0 : (perturbedMetric h 0 p.val).det ≠ 0 := by
    simpa [perturbedMetric] using exterior_metric_det_ne_zero p
  filter_upwards [hd.continuousAt.eventually_ne h0] with ε hε
  intro j
  rw [sourceField_eq_literalEinstein]
  exact ComplexMetricField.literalEinstein_divergence (perturbedMetric h ε) (-3) p.val
    (fun i j => (exterior_metric_contDiffAt p i j).add
      (contDiffAt_const.mul (D4BMLiteralMetricBianchi.literal_contDiffAt 3 p omega u aS aV i j)))
    hε (metric_symm omega u aS aV ε) j

end
end RHTower.D4BMLiteralConservation
