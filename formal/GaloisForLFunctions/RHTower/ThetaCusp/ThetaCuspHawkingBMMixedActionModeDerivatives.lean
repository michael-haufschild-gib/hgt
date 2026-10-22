import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedCorrectedSource

set_option autoImplicit false
set_option maxSynthPendingDepth 128

namespace RHTower.D4BMMixedActionData
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource D4BMMixedCorrectedSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- All mode slots retain their actual spatial regularity under the polynomial mode path. -/
theorem fieldPath_smooth (p : ExteriorPoint) (H : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val) (z : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => fieldPath H z x i j) p.val :=
  (((hH 0 i j).add (contDiffAt_const.mul (hH 1 i j))).add
    (contDiffAt_const.mul (hH 2 i j))).add (contDiffAt_const.mul (hH 3 i j))

@[simp] theorem fieldPath_at_zero (H : Fin 4 → MetricField) : fieldPath H 0 = H 0 := by
  funext x
  simp [fieldPath]

/-- Actual complete field jets differentiate through the independent mode parameter. -/
theorem fieldPath_jet_hasDerivAt (p : ExteriorPoint) (H : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val) :
    HasDerivAt (fun z => fieldSpace p (fieldPath H z)) (fieldSpace p (H 1)) 0 := by
  have he : (fun z => fieldSpace p (fieldPath H z)) = ComplexCubicPath.path
      (fieldSpace p (H 0)) (fieldSpace p (H 1)) (fieldSpace p (H 2)) (fieldSpace p (H 3)) := by
    funext z
    exact fieldPath_jet p H hH z
  rw [he]
  simpa [ComplexCubicPath.velocity] using ComplexCubicPath.path_hasDerivAt
    (fieldSpace p (H 0)) (fieldSpace p (H 1)) (fieldSpace p (H 2)) (fieldSpace p (H 3)) 0

private def metricProjection (i j : Fin 4) : ComplexMetricTwoJetSpace 4 →L[ℂ] ℂ where
  toFun := fun q => q.1 i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := by fun_prop

private def linear (p : ExteriorPoint) (i j : Fin 4) : ComplexMetricTwoJetSpace 4 →L[ℂ] ℂ :=
  fderiv ℂ (einsteinComponent i j) (backgroundSpace p) + (-3 : ℂ) • metricProjection i j

private theorem linear_residual (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) :
    linear p i j (fieldSpace p h) = D4BMLinearizedEinsteinSource.residual p (ofMetricField h p.val) i j := by
  rw [D4BMLinearizedEinsteinSource.residual, CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv (actualJet p) _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Genuine linearized solutions remain solutions throughout the independent mode path. -/
theorem fieldPath_source_first_zero (p : ExteriorPoint) (H : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hfirst : ∀ a i j, deriv (source p (H a) i j) 0 = 0) (z : ℂ) (i j : Fin 4) :
    deriv (source p (fieldPath H z) i j) 0 = 0 := by
  have hz (a : Fin 4) : linear p i j (fieldSpace p (H a)) = 0 := by
    rw [linear_residual, ← (D4BMLinearizedEinsteinSource.source_hasDerivAt p (H a) (hH a) i j).deriv]
    exact hfirst a i j
  rw [(D4BMLinearizedEinsteinSource.source_hasDerivAt p _ (fieldPath_smooth p H hH z) i j).deriv,
    ← linear_residual, fieldPath_jet p H hH z]
  simp [ComplexCubicPath.path, hz]

/-- The mixed derivative of the full quadratic coefficient contains the mixed correction and
one symmetric bilinear source, with the original factor of one half discharged. -/
theorem quadratic_mode_hasDerivAt (p : ExteriorPoint) (H K L : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val) (i j : Fin 4) :
    HasDerivAt (fun z => iteratedDeriv 2 (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 2)
      (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 1) p.val) i j +
        secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 1))) 0 := by
  let B := secondVariation (backgroundSpace p) i j
  have dh := fieldPath_jet_hasDerivAt p H hH
  have dk := fieldPath_jet_hasDerivAt p K hK
  have hd := ((linear p i j).hasFDerivAt.comp_hasDerivAt 0 dk).add
    ((((hasDerivAt_const (0 : ℂ) B).clm_apply dh).clm_apply dh).div_const 2)
  have he : (fun z => iteratedDeriv 2 (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 2) = fun z =>
      linear p i j (fieldSpace p (fieldPath K z)) +
        B (fieldSpace p (fieldPath H z)) (fieldSpace p (fieldPath H z)) / 2 := by
    funext z
    rw [D4BMCorrectedMetricSource.source_quadratic p _ _ _ (fieldPath_smooth p H hH z)
      (fieldPath_smooth p K hK z) (fieldPath_smooth p L hL z), linear_residual]
  rw [he]
  convert! hd using 1
  simp only [fieldPath_at_zero, zero_apply, zero_add, linear_residual]
  dsimp [B]
  rw [secondVariation_symm (backgroundSpace p) (exterior_metric_det_ne_zero p) i j
    (fieldSpace p (H 1)) (fieldSpace p (H 0))]
  ring

/-- Actual cubic source regularity in the independent mode parameter, before any projection. -/
theorem cubic_mode_differentiableAt (p : ExteriorPoint) (H K L : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val) (i j : Fin 4) :
    DifferentiableAt ℂ (fun z => iteratedDeriv 3 (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 6) 0 := by
  let B := secondVariation (backgroundSpace p) i j
  let C := thirdVariation (backgroundSpace p) i j
  have dh := fieldPath_jet_hasDerivAt p H hH
  have dk := fieldPath_jet_hasDerivAt p K hK
  have dl := fieldPath_jet_hasDerivAt p L hL
  have hd := (((linear p i j).hasFDerivAt.comp_hasDerivAt 0 dl).add
    (((hasDerivAt_const (0 : ℂ) B).clm_apply dh).clm_apply dk)).add
    (((((hasDerivAt_const (0 : ℂ) C).clm_apply dh).clm_apply dh).clm_apply dh).div_const 6)
  have he : (fun z => iteratedDeriv 3 (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 6) = fun z =>
      linear p i j (fieldSpace p (fieldPath L z)) +
        B (fieldSpace p (fieldPath H z)) (fieldSpace p (fieldPath K z)) +
        C (fieldSpace p (fieldPath H z)) (fieldSpace p (fieldPath H z))
          (fieldSpace p (fieldPath H z)) / 6 := by
    funext z
    rw [D4BMCorrectedMetricSource.source_cubic p _ _ _ (fieldPath_smooth p H hH z)
      (fieldPath_smooth p K hK z) (fieldPath_smooth p L hL z), linear_residual]
  rw [he]
  exact hd.differentiableAt

end
end RHTower.D4BMMixedActionData
