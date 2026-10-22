import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorLinearEinsteinEquation

namespace RHTower.D4BMFullLinearEquation
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- Complete actual metric jets preserve addition of C2 perturbation fields. -/
theorem fieldSpace_add (p : ExteriorPoint) (h k : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val) :
    toSpace (ofMetricField (fun x => h x + k x) p.val) =
      toSpace (ofMetricField h p.val) + toSpace (ofMetricField k p.val) := by
  have hs (i j : Fin 4) := ScalarTwoJet.ofField_add (hh i j) (hk i j)
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext l i j
      exact congrArg (fun J => J.first l) (hs i j)
    · funext l m i j
      exact congrArg (fun J => J.second l m) (hs i j)

/-- The actual first amplitude derivative is additive, including the cosmological term. -/
theorem source_first_add (p : ExteriorPoint) (h k : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val) (i j : Fin 4) :
    deriv (source p (fun x => h x + k x) i j) 0 =
      deriv (source p h i j) 0 + deriv (source p k i j) 0 := by
  have hsum : ∀ i j, ContDiffAt ℝ 2 (fun x => (h x + k x) i j) p.val :=
    fun i j => (hh i j).add (hk i j)
  rw [(D4BMLinearizedEinsteinSource.source_hasDerivAt p _ hsum i j).deriv,
    (D4BMLinearizedEinsteinSource.source_hasDerivAt p h hh i j).deriv,
    (D4BMLinearizedEinsteinSource.source_hasDerivAt p k hk i j).deriv]
  simp only [D4BMLinearizedEinsteinSource.residual,
    CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv (actualJet p) _ (exterior_metric_det_ne_zero p)]
  rw [fieldSpace_add p h k hh hk, map_add]
  change _ + (-3) * (h p.val i j + k p.val i j) =
    (_ + (-3) * h p.val i j) + (_ + (-3) * k p.val i j)
  ring

/-- The literal full KI perturbation is exactly the sum of its two parity sectors. -/
theorem literal_perturbation_split (omega u aS aV : ℂ) :
    D4BMLiteralCusp.perturbation omega u aS aV = fun x =>
      D4BMLiteralCusp.perturbation omega u aS 0 x +
        D4BMLiteralCusp.perturbation omega u 0 aV x := by
  funext x
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [D4BMLiteralCusp.perturbation, D4BMFundamentalMetric.perturbation,
    D4BMFundamentalMetric.primitives, primitiveFields, covariantMetric, covariantMetricFromOrbits,
    d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
    d4KIScalarMasslessTopologicalY, d4KIScalarMasslessTopologicalZtilde,
    d4KIVectorGaugeInvariantOrbitOfBMMaster, deriv_const_mul_field]

/-- Actual C2 regularity of every full literal perturbation component. -/
theorem literal_contDiffAt (p : ExteriorPoint) (omega u aS aV : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => D4BMLiteralCusp.perturbation omega u aS aV x i j) p.val := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  let a := D4BMFundamentalMetric.primitives omega aS aV (D4BMLiteralCusp.scalar u)
    (D4BMLiteralCusp.vector u)
  have ha := D4BMLiteralCusp.primitives_contDiffAt p omega u aS aV
  have hs := ((covariantMetricExpression omega (D4BMLiteralCusp.scalarQ u) i j).eval_jet_correct ha
    (covariantMetricExpression_regular omega (D4BMLiteralCusp.scalarQ u)
      (fun b => a b p.val) hr hf i j)).1
  have he : (fun x => (covariantMetricExpression omega (D4BMLiteralCusp.scalarQ u) i j).eval
      (fun b => a b x)) = fun x => D4BMLiteralCusp.perturbation omega u aS aV x i j := by
    funext x
    exact covariantMetricExpression_eval omega (D4BMLiteralCusp.scalarQ u) (fun b => a b x) i j
  rwa [he] at hs

/-- The full literal scalar-plus-vector metric has zero first Einstein source at
its fundamental plus branch, with independent amplitudes and no field-equation premises. -/
theorem literal_plus_source_first_zero (u aS aV : ℂ) (p : ExteriorPoint) (i j : Fin 4) :
    deriv (source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u))
        u aS aV) i j) 0 = 0 := by
  rw [literal_perturbation_split,
    source_first_add p _ _ (literal_contDiffAt p _ u aS 0) (literal_contDiffAt p _ u 0 aV),
    D4BMScalarLinearEquation.literal_plus_source_first_zero,
    D4BMVectorLinearEquation.literal_plus_source_first_zero]
  exact zero_add 0

/-- The full literal scalar-plus-vector metric has zero first Einstein source at
its fundamental minus branch, with independent amplitudes and no field-equation premises. -/
theorem literal_minus_source_first_zero (u aS aV : ℂ) (p : ExteriorPoint) (i j : Fin 4) :
    deriv (source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u))
        u aS aV) i j) 0 = 0 := by
  rw [literal_perturbation_split,
    source_first_add p _ _ (literal_contDiffAt p _ u aS 0) (literal_contDiffAt p _ u 0 aV),
    D4BMScalarLinearEquation.literal_minus_source_first_zero,
    D4BMVectorLinearEquation.literal_minus_source_first_zero]
  exact zero_add 0

end
end RHTower.D4BMFullLinearEquation
