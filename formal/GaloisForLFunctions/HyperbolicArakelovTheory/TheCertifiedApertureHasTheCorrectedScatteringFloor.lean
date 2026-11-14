import GaloisForLFunctions.HyperbolicArakelovTheory.TheJumpTailFloorNeedsTheFullArithmeticNormalization
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize

/-!
# The certified aperture in scattering normalization

At every finite scattering height, apertures at most `1881/5000` retain
the Weil floor `1/50000`. The jump tail, Robin mass drift and omitted
prime contacts appear with their exact signs.
-/

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower

open _root_.RHTower

/-- The full form domain inherits the certified positive floor. -/
theorem sourceQuadratic_floor_firstOverlap {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ 1881 / 5000) (u : CCMArchimedeanFormDomain a) :
    (1 / 50000 : ℝ) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u :=
  (mul_le_mul_of_nonneg_right
    (WindowTowerOfSpecZ.one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000 ha)
    (sq_nonneg _)).trans (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u)

/-- Corrected finite scattering energy has the positive floor minus its exact jump tail. -/
theorem correctedScatteringEnergy_floor_firstOverlap {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ 1881 / 5000) (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    (1 / 50000 : ℝ) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 - scatteringJumpTail a u N ≤
      correctedScatteringEnergy a u N := by
  have h := sourceQuadratic_floor_firstOverlap ha u
  rw [← correctedScatteringEnergy_add_jumpTail a u N] at h
  linarith only [h]

/-- The same floor in raw normalization, retaining all three completion corrections. -/
theorem scatteringWeilEnergy_full_floor_firstOverlap {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ 1881 / 5000) (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    (1 / 50000 : ℝ) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      scatteringWeilEnergy a (N + 1) (ccmArchimedeanFormToAperture a u) +
        ((scatteringSecondHeightEnergy N (ccmArchimedeanFormToAperture a u).1).toReal /
            ((N : ℝ) + 1) ^ 2 +
          (2 * gammaHardyPhaseRate 0 - scatteringMassCoefficient (N + 1)) *
            ‖ccmArchimedeanFormToAperture a u‖ ^ 2 -
          primeSecondHeightTail a (ccmArchimedeanFormToAperture a u) N /
            ((N : ℝ) + 1) ^ 2) := by
  have h := sourceQuadratic_floor_firstOverlap ha u
  rw [← scatteringWeilEnergy_add_rawDefect a u N] at h
  exact h

#print axioms sourceQuadratic_floor_firstOverlap
#print axioms correctedScatteringEnergy_floor_firstOverlap
#print axioms scatteringWeilEnergy_full_floor_firstOverlap

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
