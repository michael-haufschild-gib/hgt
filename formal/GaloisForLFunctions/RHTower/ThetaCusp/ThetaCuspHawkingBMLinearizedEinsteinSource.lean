import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMetricSource

/-!
# Explicit first variation of the literal BM Einstein source

The complete coordinate contraction equals the actual amplitude derivative of the
affinely perturbed metric field. Its vanishing is the remaining first-order tensor
equation, rather than an assumption in the nonlinear source construction.
-/

namespace RHTower.D4BMLinearizedEinsteinSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- Full linearized cosmological residual on the actual vacuum background. -/
def residual (p : ExteriorPoint) (K : CoordinateMetricTwoJet 4 ℂ) (i j : Fin 4) : ℂ :=
  CoordinateMetricTwoJet.Linearization.cosmological (actualJet p) K (-3) i j

private theorem affine_cosmological_eq (J K : CoordinateMetricTwoJet 4 ℂ)
    (i j : Fin 4) (ε : ℂ) :
    einsteinComponent i j (toSpace J + ε • toSpace K) -
      3 * (toSpace J + ε • toSpace K).1 i j =
    (CoordinateMetricTwoJet.Linearization.affine J K ε).einstein i j +
      (-3) * (CoordinateMetricTwoJet.Linearization.affine J K ε).metric i j := by
  change (CoordinateMetricTwoJet.Linearization.affine J K ε).einstein i j -
    3 * (CoordinateMetricTwoJet.Linearization.affine J K ε).metric i j = _
  ring

/-- The explicit contraction is the actual first derivative of the field source. -/
theorem source_hasDerivAt (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4) :
    HasDerivAt (source p h i j) (residual p (ofMetricField h p.val) i j) 0 := by
  have hd := CoordinateMetricTwoJet.Linearization.cosmological_hasDerivAt
    (actualJet p) (ofMetricField h p.val) (exterior_metric_det_ne_zero p) (-3) i j
  have he : source p h i j = fun ε =>
      (CoordinateMetricTwoJet.Linearization.affine (actualJet p) (ofMetricField h p.val) ε).einstein i j +
      (-3) * (CoordinateMetricTwoJet.Linearization.affine (actualJet p) (ofMetricField h p.val) ε).metric i j := by
    funext ε
    rw [source_eq p h hh i j ε]
    exact affine_cosmological_eq (actualJet p) (ofMetricField h p.val) i j ε
  rw [he]
  exact hd

/-- The outstanding first-order equation is exactly vanishing of the finite contraction. -/
theorem source_first_zero_iff (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4) :
    deriv (source p h i j) 0 = 0 ↔ residual p (ofMetricField h p.val) i j = 0 := by
  rw [(source_hasDerivAt p h hh i j).deriv]

/-- Full reconstruction supplies the actual metric jet in the first variation. -/
theorem reconstructed_source_hasDerivAt (p : ExteriorPoint) (omega q : ℂ)
    (a : Primitive → (Fin 4 → ℝ) → ℂ)
    (ha : ∀ b, ContDiffAt ℝ 2 (a b) p.val)
    (hr : a .radius p.val ≠ 0) (hf : (a .radius p.val)^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    HasDerivAt (source p (fun x => covariantMetric omega q (fun b => a b x)) i j)
      (residual p (metricJet omega q (fun b => ScalarTwoJet.ofField (a b) p.val)) i j) 0 := by
  rw [metricJet_correct omega q ha hr hf]
  apply source_hasDerivAt
  intro k l
  have hs := ((covariantMetricExpression omega q k l).eval_jet_correct ha
    (covariantMetricExpression_regular omega q (fun b => a b p.val) hr hf k l)).1
  have he : (fun x => (covariantMetricExpression omega q k l).eval (fun b => a b x)) =
      fun x => covariantMetric omega q (fun b => a b x) k l := by
    funext x
    exact covariantMetricExpression_eval omega q (fun b => a b x) k l
  rwa [he] at hs

/-- The literal fundamental profiles and fixed horizon geometry enter the first variation,
with no independent radial smoothness or assigned derivative arrays. -/
theorem fundamental_source_hasDerivAt (p : ExteriorPoint) (omega q aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ i, ContDiffAt ℝ 2 (V i) (angularPoint p.val)) (i j : Fin 4) :
    HasDerivAt (source p (D4BMFundamentalMetric.perturbation omega q aS aV S V) i j)
      (residual p (D4BMFundamentalMetric.fullJet p omega q aS aV S V) i j) 0 := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have hfR : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast hfR
  exact reconstructed_source_hasDerivAt p omega q
    (D4BMFundamentalMetric.primitives omega aS aV S V)
    (D4BMFundamentalMetric.primitives_contDiffAt p omega aS aV S V hS hV) hr hf i j

end
end RHTower.D4BMLinearizedEinsteinSource
