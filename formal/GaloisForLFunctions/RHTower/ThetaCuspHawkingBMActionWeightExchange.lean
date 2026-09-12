import GaloisForLFunctions.HTGeometry.CoordinateMetricVolumeTrace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullLinearEinsteinEquation

/-!
# Exchange of the actual volume-weighted Einstein test fields

For independent full literal scalar/vector fields, swapping the field variation and test
cancels both inverse-metric derivative terms and leaves an exact volume-trace wedge. The same
identity is the first derivative of complete cubic metric paths with arbitrary correction
matrices, and its contraction retains every entry of a tensor residual. The vector sector has
zero volume trace; the remaining defect depends on the scalar part of each field.

This is a local identity for the changing action weight. Cyclicity of the complete nonlinear
source also involves the solved correction equations and the differentiated boundary current.
-/

set_option autoImplicit false

namespace RHTower.D4BMActionWeightExchange
open GaloisForLFunctions.HTGeometry
open MetricPathDensity
open D4BMBackground D4BMMetricReconstruction
noncomputable section

private theorem slope_exchange {d : ℕ} (G H M : Matrix (Fin d) (Fin d) ℂ)
    (hG : G.det ≠ 0) (hGs : G.transpose = G)
    (hH : H.transpose = H) (hM : M.transpose = M) :
    testWeightSlope G H M - testWeightSlope G M H =
      ((G⁻¹ * H).trace / 2) • (G⁻¹ * M * (G⁻¹).transpose) -
      ((G⁻¹ * M).trace / 2) • (G⁻¹ * H * (G⁻¹).transpose) := by
  have hi : (G⁻¹).transpose = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGs]
  have hc (N : Matrix (Fin d) (Fin d) ℂ) :
      determinantSlope G N / (2 * G.det) = (G⁻¹ * N).trace / 2 := by
    rw [determinantSlope_eq_det_mul_trace G N hG]
    field_simp
  simp only [testWeightSlope, hc, Matrix.transpose_mul, hi, hH, hM]
  noncomm_ring

private theorem literal_symmetric (omega u aS aV : ℂ) (x : Fin 4 → ℝ) :
    (D4BMLiteralCusp.perturbation omega u aS aV x).transpose =
      D4BMLiteralCusp.perturbation omega u aS aV x := by
  ext i j
  let a := fun b => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) b x
  have h := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) j i)
  rw [covariantMetricExpression_eval, covariantMetricExpression_eval] at h
  exact h

/-- Exchanging independent literal scalar/vector fields in the actual changing test weight
leaves precisely the volume-trace wedge. Both inverse-metric derivatives cancel. -/
theorem literal_weight_exchange (p : ExteriorPoint)
    (omega u aS aV omegaTest uTest bS bV : ℂ) :
    let G := metric (p.val 1) (p.val 3)
    let H := D4BMLiteralCusp.perturbation omega u aS aV p.val
    let M := D4BMLiteralCusp.perturbation omegaTest uTest bS bV p.val
    testWeightSlope G H M - testWeightSlope G M H =
      ((G⁻¹ * H).trace / 2) • (G⁻¹ * M * (G⁻¹).transpose) -
      ((G⁻¹ * M).trace / 2) • (G⁻¹ * H * (G⁻¹).transpose) := by
  apply slope_exchange _ _ _ (exterior_metric_det_ne_zero p)
    _ (literal_symmetric omega u aS aV p.val)
    (literal_symmetric omegaTest uTest bS bV p.val)
  ext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [metric, h, Ne.symm h]

/-- The exchange law is the derivative of the full cubic metric paths. Arbitrary quadratic
and cubic corrections in either path are retained; neither affects this first weight derivative. -/
theorem literal_corrected_weight_exchange (p : ExteriorPoint)
    (omega u aS aV omegaTest uTest bS bV : ℂ)
    (K L KT LT : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    let G := metric (p.val 1) (p.val 3)
    let H := D4BMLiteralCusp.perturbation omega u aS aV p.val
    let M := D4BMLiteralCusp.perturbation omegaTest uTest bS bV p.val
    deriv (fun t => testWeight G H K L M t i j) 0 -
        deriv (fun t => testWeight G M KT LT H t i j) 0 =
      (G⁻¹ * H).trace / 2 * (G⁻¹ * M * (G⁻¹).transpose) i j -
      (G⁻¹ * M).trace / 2 * (G⁻¹ * H * (G⁻¹).transpose) i j := by
  dsimp only
  rw [(testWeight_hasDerivAt _ _ K L _ (exterior_metric_det_ne_zero p) i j).deriv,
    (testWeight_hasDerivAt _ _ KT LT _ (exterior_metric_det_ne_zero p) i j).deriv]
  exact congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A i j)
    (literal_weight_exchange p omega u aS aV omegaTest uTest bS bV)

/-- Exact contraction of the exchange defect with any tensor residual. No scalar,
vector or retained spin-two entry of the residual is discarded. -/
theorem literal_weight_residual_exchange (p : ExteriorPoint)
    (omega u aS aV omegaTest uTest bS bV : ℂ)
    (R : Matrix (Fin 4) (Fin 4) ℂ) :
    let G := metric (p.val 1) (p.val 3)
    let H := D4BMLiteralCusp.perturbation omega u aS aV p.val
    let M := D4BMLiteralCusp.perturbation omegaTest uTest bS bV p.val
    (∑ i, ∑ j, (testWeightSlope G H M i j - testWeightSlope G M H i j) * R i j) =
      (G⁻¹ * H).trace / 2 * (∑ i, ∑ j, (G⁻¹ * M * (G⁻¹).transpose) i j * R i j) -
      (G⁻¹ * M).trace / 2 * (∑ i, ∑ j, (G⁻¹ * H * (G⁻¹).transpose) i j * R i j) := by
  dsimp only
  have he := literal_weight_exchange p omega u aS aV omegaTest uTest bS bV
  have hc := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => ∑ i, ∑ j, A i j * R i j) he
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum] using hc

/-- The literal vector reconstruction has zero volume trace at the original metric,
for every frequency and every full infinite-series angular parameter. -/
theorem literal_vector_trace (p : ExteriorPoint) (omega u aV : ℂ) :
    ((metric (p.val 1) (p.val 3))⁻¹ *
      D4BMLiteralCusp.perturbation omega u 0 aV p.val).trace = 0 := by
  have hd (i : Fin 4) : D4BMLiteralCusp.perturbation omega u 0 aV p.val i i = 0 := by
    fin_cases i <;>
      simp [D4BMLiteralCusp.perturbation, D4BMFundamentalMetric.perturbation,
        D4BMFundamentalMetric.primitives, primitiveFields, covariantMetric, covariantMetricFromOrbits,
        d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
        d4KIScalarMasslessTopologicalY, d4KIScalarMasslessTopologicalZtilde]
  have hr : (p.val 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^2 - 1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^2 - 1 ≠ 0)
  rw [metric_inverse _ _ hr hy hf]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, hd, mul_zero,
    Finset.sum_const_zero]

/-- Only the scalar component of the full independent-amplitude field changes the volume
at first order; the vector amplitude contributes no trace. -/
theorem literal_trace_scalar (p : ExteriorPoint) (omega u aS aV : ℂ) :
    ((metric (p.val 1) (p.val 3))⁻¹ *
      D4BMLiteralCusp.perturbation omega u aS aV p.val).trace =
    ((metric (p.val 1) (p.val 3))⁻¹ *
      D4BMLiteralCusp.perturbation omega u aS 0 p.val).trace := by
  rw [D4BMFullLinearEquation.literal_perturbation_split omega u aS aV]
  simp only [Matrix.mul_add, Matrix.trace_add, literal_vector_trace, add_zero]

/-- Vector/vector exchange has no volume-trace defect; this statement concerns the actual
changing metric weight, not the bulk source or its boundary current. -/
theorem literal_vector_weight_exchange (p : ExteriorPoint)
    (omega u aV omegaTest uTest bV : ℂ) :
    let G := metric (p.val 1) (p.val 3)
    let H := D4BMLiteralCusp.perturbation omega u 0 aV p.val
    let M := D4BMLiteralCusp.perturbation omegaTest uTest 0 bV p.val
    testWeightSlope G H M = testWeightSlope G M H := by
  have he := literal_weight_exchange p omega u 0 aV omegaTest uTest 0 bV
  dsimp only at he ⊢
  rw [literal_vector_trace, literal_vector_trace] at he
  simpa only [zero_div, zero_smul, sub_zero, sub_eq_zero] using he

/-- Pairing a full literal scalar/vector source with a literal vector test leaves exactly
the source's volume trace times its original raised test tensor. -/
theorem literal_vector_test_weight_exchange (p : ExteriorPoint)
    (omega u aS aV omegaTest uTest bV : ℂ) :
    let G := metric (p.val 1) (p.val 3)
    let H := D4BMLiteralCusp.perturbation omega u aS aV p.val
    let M := D4BMLiteralCusp.perturbation omegaTest uTest 0 bV p.val
    testWeightSlope G H M - testWeightSlope G M H =
      ((G⁻¹ * H).trace / 2) • (G⁻¹ * M * (G⁻¹).transpose) := by
  have he := literal_weight_exchange p omega u aS aV omegaTest uTest 0 bV
  dsimp only at he ⊢
  rw [literal_vector_trace] at he
  simpa only [zero_div, zero_smul, sub_zero] using he

end
end RHTower.D4BMActionWeightExchange
