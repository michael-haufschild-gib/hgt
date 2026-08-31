import GaloisForLFunctions.HTGeometry.DirectionalWilsonReciprocity
import GaloisForLFunctions.HTGeometry.FDNLS.Bogoliubov
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra

/-!
# Rabi--Hatano--Nelson applications in HTGeometry

The paper's scalar directional links are installed in the corpus's Wilson-loop framework.  Its
slow-spin feedback pairing is also identified with the Hermitian pairing already used by the FDNLS
Bogoliubov linearization.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RabiHatanoNelson

/-! ## Directional Wilson loops -/

/-- Scalar paper hopping embedded around an oriented four-link plaquette. -/
def rabiHatanoNelsonPlaquetteLink (J κ : ℝ) (i j : Fin 4) : Matrix (Fin 1) (Fin 1) ℂ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  then !![((J + κ : ℝ) : ℂ)]
  else !![((J - κ : ℝ) : ℂ)]

/-- Passive reverse-adjoint reciprocity of the paper plaquette holds exactly at zero directional
hopping. -/
theorem rabiHatanoNelsonPlaquetteLink_reverseAdjoint_iff (J κ : ℝ) :
    (∀ i j, rabiHatanoNelsonPlaquetteLink J κ j i =
      (rabiHatanoNelsonPlaquetteLink J κ i j)ᴴ) ↔ κ = 0 := by
  constructor
  · intro h
    apply (directionalHopping_reverseAdjoint_iff J κ).mp
    have hentry := congrArg (fun M => M 0 0) (h 0 1)
    simpa [rabiHatanoNelsonPlaquetteLink] using hentry
  · rintro rfl
    intro i j
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [rabiHatanoNelsonPlaquetteLink]

theorem rabiHatanoNelson_directionalWilsonTrace (J κ : ℝ) :
    directionalWilsonPlaquetteTrace (rabiHatanoNelsonPlaquetteLink J κ) 0 1 2 3 =
      (((J + κ : ℝ) : ℂ) ^ 4) := by
  simp [directionalWilsonPlaquetteTrace, rabiHatanoNelsonPlaquetteLink,
    Matrix.trace]
  ring

theorem rabiHatanoNelson_reverseWilsonTrace (J κ : ℝ) :
    reverseDirectionalWilsonPlaquetteTrace (rabiHatanoNelsonPlaquetteLink J κ) 0 1 2 3 =
      (((J - κ : ℝ) : ℂ) ^ 4) := by
  simp [reverseDirectionalWilsonPlaquetteTrace, rabiHatanoNelsonPlaquetteLink,
    Matrix.trace]
  ring

/-- Exact clockwise/counterclockwise Wilson contrast of the paper hopping. -/
theorem rabiHatanoNelson_Wilson_orientation_contrast (J κ : ℝ) :
    reverseDirectionalWilsonPlaquetteTrace (rabiHatanoNelsonPlaquetteLink J κ) 0 1 2 3 -
        directionalWilsonPlaquetteTrace (rabiHatanoNelsonPlaquetteLink J κ) 0 1 2 3 =
      -8 * (J : ℂ) * κ * (J ^ 2 + κ ^ 2) := by
  rw [rabiHatanoNelson_reverseWilsonTrace, rabiHatanoNelson_directionalWilsonTrace]
  push_cast
  ring

end


namespace FDNLS

noncomputable section

/-! ## Slow-spin feedback and FDNLS polarisation -/

/-- The paper's spin-length rate written with the FDNLS Hermitian real pairing. -/
def spinFeedbackLengthRate (u d : ℂ) (z : ℝ) : ℝ :=
  2 * z * rePair u d + 2 * z * (-rePair u d)

theorem spinFeedbackLengthRate_eq_rabiHatanoNelson (u d : ℂ) (z : ℝ) :
    spinFeedbackLengthRate u d z = RabiHatanoNelson.spinLengthRate u d z := by
  rw [spinFeedbackLengthRate, RabiHatanoNelson.spinLengthRate, rePair_eq]
  simp [Complex.mul_re]
  ring

/-- The slow feedback preserves spin length in the FDNLS pairing language. -/
theorem spinFeedbackLengthRate_eq_zero (u d : ℂ) (z : ℝ) :
    spinFeedbackLengthRate u d z = 0 := by
  rw [spinFeedbackLengthRate_eq_rabiHatanoNelson,
    RabiHatanoNelson.spinLengthRate_eq_zero]

/-- One Hermitian pairing simultaneously supplies the paper's tangent spin feedback and the FDNLS
Bogoliubov polarisation identity. -/
theorem spinFeedback_tangent_and_bdg_polarization (u d : ℂ) (z : ℝ) :
    spinFeedbackLengthRate u d z = 0 ∧
      ((2 * rePair u d : ℝ) : ℂ) * u =
        ((‖u‖ ^ 2 : ℝ) : ℂ) * d + u ^ 2 * (starRingEnd ℂ) d :=
  ⟨spinFeedbackLengthRate_eq_zero u d z, two_rePair_mul u d⟩

end

end FDNLS

end GaloisForLFunctions.HTGeometry
