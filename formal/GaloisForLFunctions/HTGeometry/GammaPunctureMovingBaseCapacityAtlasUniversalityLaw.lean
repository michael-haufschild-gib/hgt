import GaloisForLFunctions.HTGeometry.GammaMovingBaseCapacityCongruence
import GaloisForLFunctions.HTGeometry.GammaPunctureLaurentCover

/-!
# Gamma puncture--moving-base capacity atlas

The source puncture coordinate of an actual inverse-Gamma sheet is exactly the target coordinate
of the common normalized pole collar.  After pole-centering and factorial normalization, the
actual sheet is therefore the selected collar branch itself.  This transports the intrinsic
moving-base Möbius chart, its uniform capacity congruence, and its asymptotic isometry directly to
the genuine Gamma inverse sheet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex Filter Topology

/-- Pole-centered, factorially normalized actual inverse-Gamma sheet over the source puncture. -/
def gammaPunctureNormalizedSheet (n : ℕ) (z : ℂ) : ℂ :=
  (gammaExteriorInverseBranch n (gammaPunctureExteriorLift z) + (n : ℂ)) /
    reciprocalGammaFactorialScale n

/-- The source-puncture normalization of the actual inverse sheet is exactly the common-collar
branch at the positive Laurent coordinate. -/
theorem gammaPunctureNormalizedSheet_eq_branch (n : ℕ) (z : ℂ) :
    gammaPunctureNormalizedSheet n z =
      gammaCommonInverseCollar.branch n (gammaPunctureCoordinate z) := by
  have hscale : reciprocalGammaFactorialScale n ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  rw [gammaPunctureNormalizedSheet, gammaExteriorInverseBranch,
    ← gammaPunctureCoordinate_eq_neg_inv_exteriorLift]
  field_simp [hscale]
  ring

/-- **Puncture--moving-base chart law.**  The intrinsic moving-base coordinate is the exact
Möbius transform of the pole-normalized actual Gamma sheet. -/
theorem gammaMovingBaseTransition_puncture_eq_mobius_normalizedSheet
    (n : ℕ) (z : ℂ) :
    gammaMovingBaseTransition n (gammaPunctureCoordinate z) =
      mobiusTangentGerm (gammaMovingBaseShell n)
        (gammaPunctureNormalizedSheet n z) := by
  rw [gammaPunctureNormalizedSheet_eq_branch]
  rfl

/-- The normalized actual sheet is invariant under the puncture deck translation. -/
theorem gammaPunctureNormalizedSheet_shift (n : ℕ) (z : ℂ) :
    gammaPunctureNormalizedSheet n
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureNormalizedSheet n z := by
  rw [gammaPunctureNormalizedSheet, gammaPunctureNormalizedSheet,
    gammaExteriorInverseBranch_puncture_shift]

/-- The transported moving-base coordinate is also puncture-deck invariant. -/
theorem gammaMovingBaseTransition_puncture_shift (n : ℕ) (z : ℂ) :
    gammaMovingBaseTransition n
        (gammaPunctureCoordinate
          (z + 2 * (Real.pi : ℂ) * Complex.I)) =
      gammaMovingBaseTransition n (gammaPunctureCoordinate z) := by
  rw [gammaPunctureCoordinate_shift]

/-- **Actual-sheet capacity law.**  On the common puncture collar, the moving-base tangent metric
of the genuine Gamma sheet is uniformly congruent to its pole-normalized tangent metric, with
absolute constants independent of pole depth. -/
theorem gammaPunctureNormalizedSheet_capacity_congruent
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {z v : ℂ}
    (hz : gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) (1 / 4))
    (hshell : ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ)) :
    (16 / 81 : ℝ) * ‖v‖ ^ 2 ≤
        ‖(1 - gammaMovingBaseShell n * gammaPunctureNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ∧
      ‖(1 - gammaMovingBaseShell n * gammaPunctureNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ≤
        16 * ‖v‖ ^ 2 := by
  rw [gammaPunctureNormalizedSheet_eq_branch]
  exact gammaMovingBaseTransition_capacity_congruent hn hz hshell

/-- The actual-sheet tangent comparison is asymptotically isometric at every fixed point of the
common puncture collar. -/
theorem tendsto_gammaPunctureNormalizedSheet_tangentFactor_one
    {z : ℂ}
    (hz : gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    Tendsto
      (fun n : ℕ =>
        (1 - gammaMovingBaseShell n * gammaPunctureNormalizedSheet n z)⁻¹ ^ 2)
      atTop (nhds 1) := by
  simpa only [gammaPunctureNormalizedSheet_eq_branch] using
    tendsto_gammaMovingBaseTangentFactor_one hz

end

end GaloisForLFunctions.HTGeometry
