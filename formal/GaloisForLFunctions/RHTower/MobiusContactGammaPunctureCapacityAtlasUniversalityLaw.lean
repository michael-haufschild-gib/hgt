import GaloisForLFunctions.HTGeometry.GammaPunctureMovingBaseCapacityAtlasUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma-puncture capacity-atlas universality

The oriented finite Möbius contact-charge defect is the exact normalization of the genuine
inverse-Gamma puncture sheet.  The complete moving-base, deck, capacity, and asymptotic atlas
therefore has an arithmetic boundary-charge coordinate.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The actual inverse-Gamma puncture sheet normalized by the oriented finite Möbius contact-charge
defect. -/
def gammaPunctureMobiusContactNormalizedSheet (n : ℕ) (z : ℂ) : ℂ :=
  (gammaExteriorInverseBranch n (gammaPunctureExteriorLift z) + (n : ℂ)) /
    ((-2 - mobiusGammaContactPartialCharge n) / 2)

/-- Contact-charge normalization is exactly the intrinsic factorial puncture normalization. -/
theorem gammaPunctureMobiusContactNormalizedSheet_eq
    (n : ℕ) (z : ℂ) :
    gammaPunctureMobiusContactNormalizedSheet n z =
      gammaPunctureNormalizedSheet n z := by
  rw [gammaPunctureMobiusContactNormalizedSheet, gammaPunctureNormalizedSheet,
    mobiusContactGammaFactorialScale_eq]

/-- The contact-normalized actual sheet is the selected common-collar branch. -/
theorem gammaPunctureMobiusContactNormalizedSheet_eq_branch
    (n : ℕ) (z : ℂ) :
    gammaPunctureMobiusContactNormalizedSheet n z =
      gammaCommonInverseCollar.branch n (gammaPunctureCoordinate z) := by
  rw [gammaPunctureMobiusContactNormalizedSheet_eq,
    gammaPunctureNormalizedSheet_eq_branch]

/-- The intrinsic moving-base chart is the Möbius transform of the contact-normalized sheet. -/
theorem gammaMovingBaseTransition_puncture_eq_mobius_contactNormalizedSheet
    (n : ℕ) (z : ℂ) :
    gammaMovingBaseTransition n (gammaPunctureCoordinate z) =
      mobiusTangentGerm (gammaMovingBaseShell n)
        (gammaPunctureMobiusContactNormalizedSheet n z) := by
  rw [gammaPunctureMobiusContactNormalizedSheet_eq]
  exact gammaMovingBaseTransition_puncture_eq_mobius_normalizedSheet n z

/-- Arithmetic contact normalization preserves the puncture deck symmetry. -/
theorem gammaPunctureMobiusContactNormalizedSheet_shift
    (n : ℕ) (z : ℂ) :
    gammaPunctureMobiusContactNormalizedSheet n
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureMobiusContactNormalizedSheet n z := by
  rw [gammaPunctureMobiusContactNormalizedSheet_eq,
    gammaPunctureMobiusContactNormalizedSheet_eq,
    gammaPunctureNormalizedSheet_shift]

/-- Contact-charge-normalized actual sheets obey absolute pole-depth-independent capacity bounds. -/
theorem gammaPunctureMobiusContactNormalizedSheet_capacity_congruent
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {z v : ℂ}
    (hz : gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) (1 / 4))
    (hshell : ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ)) :
    (16 / 81 : ℝ) * ‖v‖ ^ 2 ≤
        ‖(1 - gammaMovingBaseShell n *
          gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ∧
      ‖(1 - gammaMovingBaseShell n *
          gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ≤
        16 * ‖v‖ ^ 2 := by
  rw [gammaPunctureMobiusContactNormalizedSheet_eq]
  exact gammaPunctureNormalizedSheet_capacity_congruent hn hz hshell

/-- The contact-normalized tangent comparison is asymptotically isometric. -/
theorem tendsto_gammaPunctureMobiusContactNormalizedSheet_tangentFactor_one
    {z : ℂ}
    (hz : gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    Tendsto
      (fun n : ℕ =>
        (1 - gammaMovingBaseShell n *
          gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2)
      atTop (nhds 1) := by
  simpa only [gammaPunctureMobiusContactNormalizedSheet_eq] using
    tendsto_gammaPunctureNormalizedSheet_tangentFactor_one hz

/-- **Möbius-contact Gamma-puncture complete atlas universality law.**  At every pole and puncture,
the contact-normalized actual sheet is the collar branch, obeys the intrinsic Möbius chart, and is
deck invariant. -/
theorem gammaPunctureMobiusContact_completeAtlasUniversality :
    ∀ n : ℕ, ∀ z : ℂ,
      gammaPunctureMobiusContactNormalizedSheet n z =
          gammaCommonInverseCollar.branch n (gammaPunctureCoordinate z) ∧
        gammaMovingBaseTransition n (gammaPunctureCoordinate z) =
          mobiusTangentGerm (gammaMovingBaseShell n)
            (gammaPunctureMobiusContactNormalizedSheet n z) ∧
        gammaPunctureMobiusContactNormalizedSheet n
            (z + 2 * (Real.pi : ℂ) * Complex.I) =
          gammaPunctureMobiusContactNormalizedSheet n z := by
  intro n z
  exact ⟨gammaPunctureMobiusContactNormalizedSheet_eq_branch n z,
    gammaMovingBaseTransition_puncture_eq_mobius_contactNormalizedSheet n z,
    gammaPunctureMobiusContactNormalizedSheet_shift n z⟩

end

end GaloisForLFunctions.RHTower
