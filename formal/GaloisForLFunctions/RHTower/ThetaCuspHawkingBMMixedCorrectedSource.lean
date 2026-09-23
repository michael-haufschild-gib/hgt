import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCorrectedMetricSource

set_option autoImplicit false
set_option maxSynthPendingDepth 128

/-!
# Actual corrected mixed cubic Einstein coefficient

This extracts the coefficient of ε³ z from the actual two-parameter metric source.
For H=(p,m,0,0), K=(k₊₊,k₊₋,k₋₋,0), and L=(l₊₊₊,l₊₊₋,l₊₋₋,l₋₋₋),
this is exactly the ++- grade. All correction slots remain in the family; the
coefficient calculation proves which slots can contribute. No causal response,
boundary condition, spin-two projection, or left-cokernel annihilation is assumed.
-/

namespace RHTower.D4BMMixedCorrectedSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- Four actual field coefficients combined along the independent mode parameter. -/
def fieldPath (H : Fin 4 → MetricField) (z : ℂ) : MetricField :=
  fun x => H 0 x + z • H 1 x + z^(2 : ℕ) • H 2 x + z^(3 : ℕ) • H 3 x

private theorem fieldPath_smooth (p : ExteriorPoint) (H : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val) (z : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => fieldPath H z x i j) p.val :=
  (((hH 0 i j).add (contDiffAt_const.mul (hH 1 i j))).add
    (contDiffAt_const.mul (hH 2 i j))).add (contDiffAt_const.mul (hH 3 i j))

private theorem fieldPath_zero (H : Fin 4 → MetricField) : fieldPath H 0 = H 0 := by
  funext x
  simp [fieldPath]

/-- Every spatial derivative in the mode family comes from the actual field coefficients. -/
theorem fieldPath_jet (p : ExteriorPoint) (H : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val) (z : ℂ) :
    fieldSpace p (fieldPath H z) = ComplexCubicPath.path
      (fieldSpace p (H 0)) (fieldSpace p (H 1)) (fieldSpace p (H 2)) (fieldSpace p (H 3)) z := by
  have hs (a : Fin 4) (c : ℂ) (i j : Fin 4) :
      ContDiffAt ℝ 2 (fun x => (c • H a x) i j) p.val := contDiffAt_const.mul (hH a i j)
  change toSpace (ofMetricField (fun x => H 0 x + z • H 1 x + z^(2 : ℕ) • H 2 x + z^(3 : ℕ) • H 3 x) p.val) = _
  rw [D4BMFullLinearEquation.fieldSpace_add p
      (fun x => H 0 x + z • H 1 x + z^(2 : ℕ) • H 2 x) (fun x => z^(3 : ℕ) • H 3 x)
      (fun i j => ((hH 0 i j).add (hs 1 z i j)).add (hs 2 (z^(2 : ℕ)) i j)) (hs 3 (z^(3 : ℕ))),
    D4BMFullLinearEquation.fieldSpace_add p
      (fun x => H 0 x + z • H 1 x) (fun x => z^(2 : ℕ) • H 2 x)
      (fun i j => (hH 0 i j).add (hs 1 z i j)) (hs 2 (z^(2 : ℕ))),
    D4BMFullLinearEquation.fieldSpace_add p (H 0) (fun x => z • H 1 x) (hH 0) (hs 1 z),
    D4BMCorrectedMetricSource.fieldSpace_smul p (H 1) (hH 1),
    D4BMCorrectedMetricSource.fieldSpace_smul p (H 2) (hH 2),
    D4BMCorrectedMetricSource.fieldSpace_smul p (H 3) (hH 3)]
  rfl

private theorem fieldPath_jet_deriv (p : ExteriorPoint) (H : Fin 4 → MetricField)
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

private theorem linear_eq (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) :
    linear p i j (fieldSpace p h) = D4BMLinearizedEinsteinSource.residual p (ofMetricField h p.val) i j := by
  rw [D4BMLinearizedEinsteinSource.residual, CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv (actualJet p) _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Actual ε³ z coefficient of the complete Einstein source of the two-parameter field. -/
def mixedCoefficient (p : ExteriorPoint) (H K L : Fin 4 → MetricField) (i j : Fin 4) : ℂ :=
  deriv (fun z => iteratedDeriv 3 (D4BMCorrectedMetricSource.source p
    (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 6) 0

/-- Exact mixed cubic coefficient, including the actual cubic correction's linear residual. -/
theorem cubic_mixed_coefficient (p : ExteriorPoint) (H K L : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val) (i j : Fin 4) :
    mixedCoefficient p H K L i j =
      D4BMLinearizedEinsteinSource.residual p (ofMetricField (L 1) p.val) i j +
        secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (K 1)) +
        secondVariation (backgroundSpace p) i j (fieldSpace p (H 1)) (fieldSpace p (K 0)) +
        thirdVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 0))
          (fieldSpace p (H 1)) / 2 := by
  let B := secondVariation (backgroundSpace p) i j
  let C := thirdVariation (backgroundSpace p) i j
  have dh := fieldPath_jet_deriv p H hH
  have dk := fieldPath_jet_deriv p K hK
  have dl := fieldPath_jet_deriv p L hL
  have hb := ((hasDerivAt_const (0 : ℂ) B).clm_apply dh).clm_apply dk
  have hc := (((hasDerivAt_const (0 : ℂ) C).clm_apply dh).clm_apply dh).clm_apply dh
  have hl := (linear p i j).hasFDerivAt.comp_hasDerivAt 0 dl
  have hd := (hl.add hb).add (hc.div_const 6)
  have he : (fun z => iteratedDeriv 3 (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / 6) = fun z =>
      linear p i j (fieldSpace p (fieldPath L z)) +
        B (fieldSpace p (fieldPath H z)) (fieldSpace p (fieldPath K z)) +
        C (fieldSpace p (fieldPath H z)) (fieldSpace p (fieldPath H z))
          (fieldSpace p (fieldPath H z)) / 6 := by
    funext z
    rw [D4BMCorrectedMetricSource.source_cubic p _ _ _ (fieldPath_smooth p H hH z)
      (fieldPath_smooth p K hK z) (fieldPath_smooth p L hL z), linear_eq]
  unfold mixedCoefficient
  rw [he]
  calc
    _ = _ := hd.deriv
    _ = _ := by
      simp only [fieldPath_zero, zero_apply, zero_add, add_apply]
      rw [linear_eq]
      change _ + (B (fieldSpace p (H 1)) (fieldSpace p (K 0)) +
          B (fieldSpace p (H 0)) (fieldSpace p (K 1))) +
        ((C (fieldSpace p (H 1)) (fieldSpace p (H 0)) (fieldSpace p (H 0)) +
          C (fieldSpace p (H 0)) (fieldSpace p (H 1)) (fieldSpace p (H 0))) +
          C (fieldSpace p (H 0)) (fieldSpace p (H 0)) (fieldSpace p (H 1))) / 6 = _
      dsimp [C]
      rw [thirdVariation_symm_left (backgroundSpace p) (exterior_metric_det_ne_zero p) i j
          (fieldSpace p (H 1)) (fieldSpace p (H 0)) (fieldSpace p (H 0)),
        thirdVariation_symm_right (backgroundSpace p) (exterior_metric_det_ne_zero p) i j
          (fieldSpace p (H 0)) (fieldSpace p (H 1)) (fieldSpace p (H 0))]
      dsimp [B]
      ring

/-- Vanishing of the actual mixed coefficient is precisely its forced correction equation. -/
theorem cubic_mixed_zero_iff (p : ExteriorPoint) (H K L : Fin 4 → MetricField)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val) (i j : Fin 4) :
    mixedCoefficient p H K L i j = 0 ↔
      D4BMLinearizedEinsteinSource.residual p (ofMetricField (L 1) p.val) i j =
        -(secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (K 1)) +
          secondVariation (backgroundSpace p) i j (fieldSpace p (H 1)) (fieldSpace p (K 0)) +
          thirdVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 0))
            (fieldSpace p (H 1)) / 2) := by
  rw [cubic_mixed_coefficient p H K L hH hK hL]
  constructor <;> intro he <;> linear_combination he

end
end RHTower.D4BMMixedCorrectedSource
