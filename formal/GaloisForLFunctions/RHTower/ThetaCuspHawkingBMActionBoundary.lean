import GaloisForLFunctions.HTGeometry.ComplexMetricActionVariation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralMetricBianchi

set_option autoImplicit false
namespace RHTower.D4BMActionBoundary
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexMetricField EinsteinActionBoundary ComplexMetricActionBoundary
open Filter Topology
noncomputable section

private theorem literal_symmetry (omega u aS aV : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    D4BMLiteralCusp.perturbation omega u aS aV x i j =
      D4BMLiteralCusp.perturbation omega u aS aV x j i := by
  let a := fun b => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) b x
  have hs := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) i j)
  rw [covariantMetricExpression_eval, covariantMetricExpression_eval] at hs
  exact hs

private theorem metric_symmetry (omega u aS aV ε : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x i j =
      perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x j i := by
  have hb : metric (x 1) (x 3) i j = metric (x 1) (x 3) j i := by
    by_cases hij : i = j
    · subst j; rfl
    · simp [metric, hij, Ne.symm hij]
  change metric (x 1) (x 3) i j + ε * D4BMLiteralCusp.perturbation omega u aS aV x i j = _
  rw [hb, literal_symmetry omega u aS aV x i j]
  rfl

/-- Actual local action variation for the literal BM metric and an independent literal testing
field, throughout a nondegenerate amplitude neighborhood. Every regularity and symmetry premise is
discharged. The full original source and all four boundary-current directions remain. -/
theorem literal_action_boundary_near_zero (p : ExteriorPoint)
    (omega u aS aV omegaTest uTest bS bV : ℂ) :
    let H := D4BMLiteralCusp.perturbation omega u aS aV
    let M := D4BMLiteralCusp.perturbation omegaTest uTest bS bV
    ∀ᶠ ε : ℂ in 𝓝 0,
      deriv (fieldDensityPath (perturbedMetric H ε) M p.val (-3)) 0 =
        -(∑ i, ∑ j, ((perturbedMetric H ε p.val)⁻¹ * M p.val *
          ((perturbedMetric H ε p.val)⁻¹).transpose) i j * source p H i j ε) +
        ∑ a, ScalarTwoJet.coordDeriv a (fun y => localVolume (perturbedMetric H ε) p.val y *
          current (twoJet (perturbedMetric H ε) y) (twoJet M y) a) p.val := by
  dsimp only
  let H := D4BMLiteralCusp.perturbation omega u aS aV
  let M := D4BMLiteralCusp.perturbation omegaTest uTest bS bV
  have hd : Continuous (fun ε : ℂ => (perturbedMetric H ε p.val).det) := by
    simp only [Matrix.det_apply', perturbedMetric, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h0 : (perturbedMetric H 0 p.val).det ≠ 0 := by
    simpa [perturbedMetric] using exterior_metric_det_ne_zero p
  filter_upwards [hd.continuousAt.eventually_ne h0] with ε hε
  have he := density_first_variation (perturbedMetric H ε) M p.val (-3)
    (fun i j => (exterior_metric_contDiffAt p i j).add
      (contDiffAt_const.mul (D4BMLiteralMetricBianchi.literal_contDiffAt 3 p omega u aS aV i j)))
    (D4BMLiteralMetricBianchi.literal_contDiffAt 3 p omegaTest uTest bS bV) hε
    (metric_symmetry omega u aS aV ε)
  convert! he using 1
  simp only [source, sub_eq_add_neg, neg_mul]
  rfl

end
end RHTower.D4BMActionBoundary
