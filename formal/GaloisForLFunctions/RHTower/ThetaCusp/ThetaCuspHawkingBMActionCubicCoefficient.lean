import GaloisForLFunctions.HTGeometry.CoordinateEinsteinPairedCubicSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCorrectedMetricSource

set_option autoImplicit false

namespace RHTower.D4BMActionSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet MetricPathDensity
noncomputable section
local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- Actual corrected Einstein source contracted with the varying raised test and volume ratio. -/
def pairedSource (p : ExteriorPoint) (h k l : MetricField) (M : Mat) (t : ℂ) : ℂ :=
  ∑ i, ∑ j, testWeight (actualJet p).metric (h p.val) (k p.val) (l p.val) M t i j *
    D4BMCorrectedMetricSource.source p h k l i j t

/-- Complete field jets identify the bulk pairing with the original rational metric-path contraction. -/
theorem pairedSource_eq (p : ExteriorPoint) (h k l : MetricField) (M : Mat)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) :
    pairedSource p h k l M = CubicSource.pairedSource (actualJet p)
      (ofMetricField h p.val) (ofMetricField k p.val) (ofMetricField l p.val) (-3) M := by
  funext t
  unfold pairedSource CubicSource.pairedSource
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D4BMCorrectedMetricSource.source_eq p h k l hh hk hl]
  rfl

/-- Exact complete-field cubic identity before solving the quadratic correction equation. -/
theorem pairedSource_cubic (p : ExteriorPoint) (h k l : MetricField) (M : Mat)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val)
    (hfirst : ∀ i j, deriv (D4BMActualMetricSource.source p h i j) 0 = 0) :
    iteratedDeriv 3 (pairedSource p h k l M) 0 / 6 =
      ∑ i, ∑ j,
        (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          (iteratedDeriv 3 (D4BMCorrectedMetricSource.source p h k l i j) 0 / 6) +
        testWeightSlope (actualJet p).metric (h p.val) M i j *
          (iteratedDeriv 2 (D4BMCorrectedMetricSource.source p h k l i j) 0 / 2)) := by
  have hzero (i j : Fin 4) : (actualJet p).einstein i j + (-3 : ℂ) * (actualJet p).metric i j = 0 := by
    simpa only [neg_mul, sub_eq_add_neg] using exterior_vacuum p i j
  have hone (i j : Fin 4) : CoordinateMetricTwoJet.Linearization.cosmological
      (actualJet p) (ofMetricField h p.val) (-3) i j = 0 := by
    change D4BMLinearizedEinsteinSource.residual p (ofMetricField h p.val) i j = 0
    rw [← (D4BMLinearizedEinsteinSource.source_hasDerivAt p h hh i j).deriv]
    exact hfirst i j
  rw [pairedSource_eq p h k l M hh hk hl,
    CubicSource.pairedSource_cubic _ _ _ _ (exterior_metric_det_ne_zero p) (-3) M hzero hone]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D4BMCorrectedMetricSource.source_eq p h k l hh hk hl,
    CubicSource.cubic_coefficient _ _ _ _ (exterior_metric_det_ne_zero p),
    CubicSource.quadratic_coefficient _ _ _ _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Both literal fundamental branches with independent scalar and vector amplitudes. -/
def literalField (branch : Bool) (u aS aV : ℂ) : MetricField :=
  D4BMLiteralCusp.perturbation
    (if branch then d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u)
      else d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u)) u aS aV

/-- The literal BM source discharges every linear field-equation premise in the cubic pairing.
The full quadratic residual remains, including every scalar and vector component. -/
theorem literal_pairedSource_cubic (branch : Bool) (u aS aV : ℂ) (p : ExteriorPoint)
    (k l : MetricField) (M : Mat)
    (hk : ∀ i j, ContDiffAt ℝ 2 (fun x => k x i j) p.val)
    (hl : ∀ i j, ContDiffAt ℝ 2 (fun x => l x i j) p.val) :
    iteratedDeriv 3 (pairedSource p (literalField branch u aS aV) k l M) 0 / 6 =
      ∑ i, ∑ j,
        (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          (iteratedDeriv 3 (D4BMCorrectedMetricSource.source p (literalField branch u aS aV) k l i j) 0 / 6) +
        testWeightSlope (actualJet p).metric (literalField branch u aS aV p.val) M i j *
          (iteratedDeriv 2 (D4BMCorrectedMetricSource.source p (literalField branch u aS aV) k l i j) 0 / 2)) := by
  refine pairedSource_cubic p _ k l M ?_ hk hl ?_
  · exact D4BMFullLinearEquation.literal_contDiffAt p _ u aS aV
  · intro i j
    cases branch
    · exact D4BMFullLinearEquation.literal_minus_source_first_zero u aS aV p i j
    · exact D4BMFullLinearEquation.literal_plus_source_first_zero u aS aV p i j

/-- Premise-free specialization to the original affine scalar/vector BM metric, on either branch. -/
theorem literal_affine_pairedSource_cubic (branch : Bool) (u aS aV : ℂ) (p : ExteriorPoint) (M : Mat) :
    iteratedDeriv 3 (pairedSource p (literalField branch u aS aV) (fun _ => 0) (fun _ => 0) M) 0 / 6 =
      ∑ i, ∑ j,
        (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          (iteratedDeriv 3 (D4BMCorrectedMetricSource.source p (literalField branch u aS aV)
            (fun _ => 0) (fun _ => 0) i j) 0 / 6) +
        testWeightSlope (actualJet p).metric (literalField branch u aS aV p.val) M i j *
          (iteratedDeriv 2 (D4BMCorrectedMetricSource.source p (literalField branch u aS aV)
            (fun _ => 0) (fun _ => 0) i j) 0 / 2)) :=
  literal_pairedSource_cubic branch u aS aV p _ _ M
    (fun _ _ => contDiffAt_const) (fun _ _ => contDiffAt_const)

end
end RHTower.D4BMActionSource
