import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCubicPath
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullLinearEinsteinEquation

set_option autoImplicit false

/-!
# Actual corrected metric source on the BM exterior

All coefficients come from the Einstein contraction of the complete spatial jet of
`g + ε h + ε² k + ε³ l`. The correction fields remain explicit. These identities
specify their forced equations; they do not assert solvability or causal admission.
-/

namespace RHTower.D4BMCorrectedMetricSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- The corrected field itself, before taking any coordinate derivatives. -/
def correctedMetric (h k l : MetricField) (ε : ℂ) : MetricField :=
  fun x => metric (x 1) (x 3) + ε • h x + ε^2 • k x + ε^3 • l x

/-- Literal cosmological Einstein source of the corrected field's complete spatial jet. -/
def source (p : ExteriorPoint) (h k l : MetricField) (i j : Fin 4) (ε : ℂ) : ℂ :=
  let J := ofMetricField (correctedMetric h k l ε) p.val
  J.einstein i j - 3 * J.metric i j

/-- Complete actual spatial jets commute with constant complex scaling. -/
theorem fieldSpace_smul (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (c : ℂ) :
    toSpace (ofMetricField (fun x => c • h x) p.val) = c • fieldSpace p h := by
  have hs (i j : Fin 4) :
      ScalarTwoJet.ofField (fun x => c * h x i j) p.val =
        ScalarTwoJet.mul (ScalarTwoJet.constant c) (ScalarTwoJet.ofField (fun x => h x i j) p.val) := by
    rw [ScalarTwoJet.ofField_mul contDiffAt_const (hh i j), ScalarTwoJet.ofField_constant]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext a i j
      change (ScalarTwoJet.ofField (fun x => c * h x i j) p.val).first a = _
      rw [hs]
      simp [ScalarTwoJet.mul, ScalarTwoJet.constant, fieldSpace, toSpace, ofMetricField]
      rfl
    · funext a b i j
      change (ScalarTwoJet.ofField (fun x => c * h x i j) p.val).second a b = _
      rw [hs]
      simp [ScalarTwoJet.mul, ScalarTwoJet.constant, fieldSpace, toSpace, ofMetricField]
      rfl

/-- The complete spatial jet of the actual corrected field is the cubic jet path. -/
theorem correctedMetric_jet (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (ε : ℂ) :
    toSpace (ofMetricField (correctedMetric h k l ε) p.val) =
      ComplexCubicPath.path (backgroundSpace p) (fieldSpace p h) (fieldSpace p k) (fieldSpace p l) ε := by
  have ha (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => perturbedMetric h ε x i j) p.val :=
    (exterior_metric_contDiffAt p i j).add (contDiffAt_const.mul (hh i j))
  have hb (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => (ε^2 • k x) i j) p.val :=
    contDiffAt_const.mul (hk i j)
  have hc (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => (ε^3 • l x) i j) p.val :=
    contDiffAt_const.mul (hl i j)
  change toSpace (ofMetricField (fun x => (perturbedMetric h ε x + ε^2 • k x) + ε^3 • l x) p.val) = _
  rw [D4BMFullLinearEquation.fieldSpace_add p
      (fun x => perturbedMetric h ε x + ε^2 • k x) (fun x => ε^3 • l x)
      (fun i j => (ha i j).add (hb i j)) hc,
    D4BMFullLinearEquation.fieldSpace_add p (perturbedMetric h ε) (fun x => ε^2 • k x) ha hb,
    perturbedMetric_jet p h hh, fieldSpace_smul p k hk, fieldSpace_smul p l hl]
  rfl

/-- Exact source equality follows from complete spatial jets, not assigned coefficient arrays. -/
theorem source_eq (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    source p h k l i j = CubicSource.source (actualJet p) (ofMetricField h p.val)
      (ofMetricField k p.val) (ofMetricField l p.val) (-3) i j := by
  funext ε
  change einsteinComponent i j (toSpace (ofMetricField (correctedMetric h k l ε) p.val)) -
    3 * (toSpace (ofMetricField (correctedMetric h k l ε) p.val)).1 i j = _
  rw [correctedMetric_jet p h k l hh hk hl]
  simp only [CubicSource.source, CubicSource.jet, einsteinComponent, backgroundSpace,
    fieldSpace, sub_eq_add_neg, neg_mul]
  rfl

/-- Every corrected metric path starts at the actual vacuum background. -/
theorem source_zero (p : ExteriorPoint) (h k l : MetricField) (i j : Fin 4) :
    source p h k l i j 0 = 0 := by
  have he : correctedMetric h k l 0 = fun x => metric (x 1) (x 3) := by
    funext x
    simp [correctedMetric]
  unfold source
  rw [he]
  exact exterior_vacuum p i j

/-- The first source coefficient agrees with the previously proved actual affine source. -/
theorem source_first (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    deriv (source p h k l i j) 0 = deriv (D4BMActualMetricSource.source p h i j) 0 := by
  rw [source_eq p h k l hh hk hl,
    CubicSource.linear_coefficient _ _ _ _ (exterior_metric_det_ne_zero p),
    (D4BMLinearizedEinsteinSource.source_hasDerivAt p h hh i j).deriv]
  rfl

/-- Full quadratic coefficient: correction residual plus actual quadratic Einstein source. -/
theorem source_quadratic (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 2 (source p h k l i j) 0 / 2 =
      D4BMLinearizedEinsteinSource.residual p (ofMetricField k p.val) i j +
        secondVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) / 2 := by
  rw [source_eq p h k l hh hk hl,
    CubicSource.quadratic_coefficient _ _ _ _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Full cubic coefficient: cubic correction residual, quadratic-correction coupling,
and the direct cubic Einstein term. -/
theorem source_cubic (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 3 (source p h k l i j) 0 / 6 =
      D4BMLinearizedEinsteinSource.residual p (ofMetricField l p.val) i j +
        secondVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p k) +
        thirdVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) (fieldSpace p h) / 6 := by
  rw [source_eq p h k l hh hk hl,
    CubicSource.cubic_coefficient _ _ _ _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Quadratic cancellation is exactly the forced equation for the actual quadratic field. -/
theorem source_quadratic_zero_iff (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 2 (source p h k l i j) 0 / 2 = 0 ↔
      D4BMLinearizedEinsteinSource.residual p (ofMetricField k p.val) i j =
        -(secondVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) / 2) := by
  rw [source_quadratic p h k l hh hk hl]
  constructor <;> intro he <;> linear_combination he

/-- Cubic cancellation is exactly the forced equation retaining the quadratic correction. -/
theorem source_cubic_zero_iff (p : ExteriorPoint) (h k l : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 3 (source p h k l i j) 0 / 6 = 0 ↔
      D4BMLinearizedEinsteinSource.residual p (ofMetricField l p.val) i j =
        -(secondVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p k) +
          thirdVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) (fieldSpace p h) / 6) := by
  rw [source_cubic p h k l hh hk hl]
  constructor <;> intro he <;> linear_combination he

/-- The literal full plus-branch field retains its proved first equation under correction. -/
theorem literal_plus_source_first_zero (u aS aV : ℂ) (p : ExteriorPoint) (k l : MetricField)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    deriv (source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u))
        u aS aV) k l i j) 0 = 0 := by
  rw [source_first p _ k l (D4BMFullLinearEquation.literal_contDiffAt p _ u aS aV) hk hl,
    D4BMFullLinearEquation.literal_plus_source_first_zero]

/-- The literal full minus-branch field retains its proved first equation under correction. -/
theorem literal_minus_source_first_zero (u aS aV : ℂ) (p : ExteriorPoint) (k l : MetricField)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) (i j : Fin 4) :
    deriv (source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u))
        u aS aV) k l i j) 0 = 0 := by
  rw [source_first p _ k l (D4BMFullLinearEquation.literal_contDiffAt p _ u aS aV) hk hl,
    D4BMFullLinearEquation.literal_minus_source_first_zero]

end
end RHTower.D4BMCorrectedMetricSource
