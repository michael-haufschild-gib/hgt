import GaloisForLFunctions.RHTower.DeningerGammaSixCofinalFullGradeSoninTransport
import GaloisForLFunctions.RHTower.SemilocalEulerPhasePolarization

/-!
# Target-free Gamma-six lift of the Sonin exterior

The full-grade Gamma-six source already carries a literal two-sheet exterior at every Wold depth.
Its source-positive calibration identifies the resulting orientation Gram with the fixed `(2,3)`
Sonin commutator.  This module performs that calibration before any Xi divisor is selected.

The normalized operator-valued lift is exactly stationary in depth.  Consequently its operator
norm and Calkin norm are stationary, it has an unconditional depth-uniform Calkin upper bound, and
the cofinal infinite completion is the same fixed Sonin operator.  Reflection negates the lift,
while compactness occurs exactly at neutral horizontal grade.

This is a fixed-pair theorem.  It does not assert the all-prime finite-packet bound required by the
Xi prime-seam endpoint.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Source-positive normalization of the literal Gamma-six orientation Gram.  Prime labels,
valuation depth, both reflection sheets, and the physical Sonin receiver are present before any
Xi divisor specialization. -/
def deningerGammaSixTargetFreeSoninExteriorLift
    (g : ℝ) (m : MobiusHonestDepth) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  (((2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ)⁻¹) •
    ((routeRCrossPrimeStokesGauge 2 3 g : ℂ) •
      finiteArchimedeanEulerOrientationGram 1
        (fun i ↦ (primeTwoThreePacket i : ℝ))
        (deningerGammaSixCofinalFullGradeGammaPacket g m))

/-- Exact target-free lift law.  Normalizing by the positive source calibration removes every
depth-dependent scalar and leaves the fixed Sonin exterior commutator. -/
theorem deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin
    (g : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixTargetFreeSoninExteriorLift g m =
      routeRTwoThreeStokesSoninCommutator 1 g := by
  rw [deningerGammaSixTargetFreeSoninExteriorLift,
    deningerGammaSixCofinalFullGradeGamma_orientationGram_eq_soninCommutator]
  rw [smul_smul]
  have hcalibration :
      (((2 * deningerGammaSixCofinalGammaSoninCalibration m : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num)
        (deningerGammaSixCofinalGammaSoninCalibration_pos m).ne')
  rw [inv_mul_cancel₀ hcalibration, one_smul]

/-- Reflection swaps the two source curvature channels, hence negates their Sonin exterior. -/
theorem routeRTwoThreeStokesSoninCommutator_neg_grade (g : ℝ) :
    routeRTwoThreeStokesSoninCommutator 1 (-g) =
      -routeRTwoThreeStokesSoninCommutator 1 g := by
  rw [routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram,
    routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram]
  have hpacket : routeRTwoThreeStokesCurvaturePacket (-g) =
      fun i => (-1 : ℂ) * routeRTwoThreeStokesCurvaturePacket g i +
        ((routeRCrossPrimeStokesCurvature 2 3 g +
          routeRCrossPrimeStokesCurvature 2 3 (-g) : ℝ) : ℂ) * 1 := by
    funext i
    fin_cases i <;>
      simp [routeRTwoThreeStokesCurvaturePacket]
  rw [hpacket,
    finiteArchimedeanEulerOrientationGram_linearCombination]
  have hconstant :
      finiteArchimedeanEulerOrientationGram 1
        (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ => (1 : ℂ)) = 0 := by
    have hmatrix : finiteEulerOrientationMatrix (fun _ : Fin 2 => (1 : ℂ)) = 0 := by
      ext i j
      simp [finiteEulerOrientationMatrix]
    rw [finiteArchimedeanEulerOrientationGram, hmatrix]
    simp [finiteArchimedeanPrimeEulerGramCombination]
  rw [hconstant, smul_zero, add_zero]
  simp

/-- Horizontal reflection is an exact odd grading on every finite source depth. -/
theorem deningerGammaSixTargetFreeSoninExteriorLift_neg_grade
    (g : ℝ) (m : MobiusHonestDepth) :
    deningerGammaSixTargetFreeSoninExteriorLift (-g) m =
      -deningerGammaSixTargetFreeSoninExteriorLift g m := by
  rw [deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin,
    deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin,
    routeRTwoThreeStokesSoninCommutator_neg_grade]

/-- Calkin norm is exactly independent of Gamma-six depth. -/
theorem essentialNorm_deningerGammaSixTargetFreeSoninExteriorLift
    (g : ℝ) (m : MobiusHonestDepth) :
    essentialNorm (deningerGammaSixTargetFreeSoninExteriorLift g m) =
      essentialNorm (routeRTwoThreeStokesSoninCommutator 1 g) := by
  rw [deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin]

/-- Unconditional uniform Calkin upper bound over every cofinal Gamma-six depth.  The bound is the
ordinary operator norm of the fixed Sonin receiver, so no compactness premise is hidden. -/
theorem deningerGammaSixTargetFreeSoninExteriorLift_uniformCalkinBound :
    ∀ g : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : MobiusHonestDepth,
      essentialNorm (deningerGammaSixTargetFreeSoninExteriorLift g m) ≤ C := by
  intro g
  refine ⟨‖routeRTwoThreeStokesSoninCommutator 1 g‖, norm_nonneg _, ?_⟩
  intro m
  rw [essentialNorm_deningerGammaSixTargetFreeSoninExteriorLift]
  simpa using essentialNorm_le
    (routeRTwoThreeStokesSoninCommutator 1 g) 0 isCompactOperator_zero

/-- The fixed reflection-odd Calkin floor survives at every source depth. -/
theorem deningerGammaSixTargetFreeSoninExteriorLift_calkinLower
    (g : ℝ) (m : MobiusHonestDepth) :
    |routeRCrossPrimeStokesOddCurvature 2 3 g| / Real.sqrt 6 ≤
      essentialNorm (deningerGammaSixTargetFreeSoninExteriorLift g m) := by
  rw [essentialNorm_deningerGammaSixTargetFreeSoninExteriorLift]
  exact abs_routeRTwoThreeStokesOddCurvature_div_sqrt_six_le_essentialNorm
    (by norm_num) g

/-- The normalized depth lift is compact exactly at neutral horizontal grade. -/
theorem deningerGammaSixTargetFreeSoninExteriorLift_isCompactOperator_iff
    (g : ℝ) (m : MobiusHonestDepth) :
    IsCompactOperator (deningerGammaSixTargetFreeSoninExteriorLift g m) ↔ g = 0 := by
  rw [deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin]
  exact routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff
    (by norm_num) g

/-- Infinite cofinal completion is automatic: the normalized lift is already the same operator at
every finite depth. -/
theorem tendsto_deningerGammaSixTargetFreeSoninExteriorLift (g : ℝ) :
    Tendsto
      (fun n : ℕ => deningerGammaSixTargetFreeSoninExteriorLift g
        (deningerGammaSixShellHonestDepth n))
      atTop (nhds (routeRTwoThreeStokesSoninCommutator 1 g)) := by
  simpa only [deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin] using
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => routeRTwoThreeStokesSoninCommutator 1 g)
      atTop (nhds (routeRTwoThreeStokesSoninCommutator 1 g)))

/-- Closed capstone: target-free lift, odd reflection, exact Calkin stationarity, uniform Calkin
upper bound, non-erasure, and infinite completion hold simultaneously without assumptions. -/
theorem DAC_DENINGER_GAMMA_SIX_TARGET_FREE_SONIN_EXTERIOR_LIFT :
    (∀ (g : ℝ) (m : MobiusHonestDepth),
      deningerGammaSixTargetFreeSoninExteriorLift g m =
        routeRTwoThreeStokesSoninCommutator 1 g) ∧
    (∀ (g : ℝ) (m : MobiusHonestDepth),
      deningerGammaSixTargetFreeSoninExteriorLift (-g) m =
        -deningerGammaSixTargetFreeSoninExteriorLift g m) ∧
    (∀ (g : ℝ) (m : MobiusHonestDepth),
      essentialNorm (deningerGammaSixTargetFreeSoninExteriorLift g m) =
        essentialNorm (routeRTwoThreeStokesSoninCommutator 1 g)) ∧
    (∀ g : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : MobiusHonestDepth,
      essentialNorm (deningerGammaSixTargetFreeSoninExteriorLift g m) ≤ C) ∧
    (∀ (g : ℝ) (m : MobiusHonestDepth),
      IsCompactOperator (deningerGammaSixTargetFreeSoninExteriorLift g m) ↔ g = 0) ∧
    (∀ g : ℝ,
      Tendsto
        (fun n : ℕ => deningerGammaSixTargetFreeSoninExteriorLift g
          (deningerGammaSixShellHonestDepth n))
        atTop (nhds (routeRTwoThreeStokesSoninCommutator 1 g))) := by
  exact ⟨deningerGammaSixTargetFreeSoninExteriorLift_eq_sonin,
    deningerGammaSixTargetFreeSoninExteriorLift_neg_grade,
    essentialNorm_deningerGammaSixTargetFreeSoninExteriorLift,
    deningerGammaSixTargetFreeSoninExteriorLift_uniformCalkinBound,
    deningerGammaSixTargetFreeSoninExteriorLift_isCompactOperator_iff,
    tendsto_deningerGammaSixTargetFreeSoninExteriorLift⟩

end

end RHTower
