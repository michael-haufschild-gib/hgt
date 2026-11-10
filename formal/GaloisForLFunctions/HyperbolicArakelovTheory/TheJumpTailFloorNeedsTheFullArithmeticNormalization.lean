import GaloisForLFunctions.HyperbolicArakelovTheory.TheSecondHeightJetOfScatteringIsDirichletEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion

/-!
# The exact floor of a finite scattering height

The positive jump tail is the full defect only after restoring the
Robin mass and omitted prime contacts. The corrected finite energy
plus this tail equals the literal closed Weil form. Consequently RH
is equivalent to its jump-tail floor at every fixed positive height.
-/

open Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower

/-- The positive jump-tail defect at scattering height `N+1`. -/
def scatteringJumpTail (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) : ℝ :=
  (scatteringSecondHeightEnergy N (ccmArchimedeanFormToAperture a u).1).toReal /
    ((N : ℝ) + 1) ^ 2

/-- Restore the exact mass and prime contacts, retaining the finite jump kernel. -/
def correctedScatteringEnergy (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) : ℝ :=
  scatteringWeilEnergy a (N + 1) (ccmArchimedeanFormToAperture a u) +
    (2 * gammaHardyPhaseRate 0 - scatteringMassCoefficient (N + 1)) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 -
    primeSecondHeightTail a (ccmArchimedeanFormToAperture a u) N / ((N : ℝ) + 1) ^ 2

theorem scatteringJumpTail_nonneg (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) : 0 ≤ scatteringJumpTail a u N :=
  div_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- The corrected finite energy and the positive tail sum to the actual Weil form. -/
theorem correctedScatteringEnergy_add_jumpTail (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    correctedScatteringEnergy a u N + scatteringJumpTail a u N =
      ccmRestrictedWeilSourceQuadratic a u := by
  have hid := scatteringSecondHeightDefect_eq a u N
  rw [scatteringSecondHeightDefect, ccmRestrictedWeilForm_self_re_eq_source] at hid
  have hN : ((N : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold correctedScatteringEnergy scatteringJumpTail
  field_simp [hN]
  linear_combination -hid

/-- At each height, the jump-tail floor is exactly Weil positivity for the same state. -/
theorem correctedScatteringEnergy_floor_iff (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    -scatteringJumpTail a u N ≤ correctedScatteringEnergy a u N ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  have he := correctedScatteringEnergy_add_jumpTail a u N
  constructor <;> intro h <;> linarith only [he, h]

/-- The exact signed defect of the raw energy retains the mass drift and the prime tail. -/
def scatteringRawDefect (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) : ℝ :=
  scatteringJumpTail a u N +
    (2 * gammaHardyPhaseRate 0 - scatteringMassCoefficient (N + 1)) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 -
    primeSecondHeightTail a (ccmArchimedeanFormToAperture a u) N / ((N : ℝ) + 1) ^ 2

theorem scatteringWeilEnergy_add_rawDefect (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    scatteringWeilEnergy a (N + 1) (ccmArchimedeanFormToAperture a u) +
      scatteringRawDefect a u N = ccmRestrictedWeilSourceQuadratic a u := by
  have he := correctedScatteringEnergy_add_jumpTail a u N
  unfold scatteringRawDefect correctedScatteringEnergy at *
  linarith only [he]

/-- RH is the corrected jump-tail floor at any fixed positive scattering height. -/
theorem riemannHypothesis_iff_correctedScatteringEnergy_floor (N : ℕ) :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      -scatteringJumpTail a u N ≤ correctedScatteringEnergy a u N := by
  constructor
  · intro hRH a u
    exact (correctedScatteringEnergy_floor_iff a u N).mpr
      (ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a u)
  · intro h
    by_contra hnot
    obtain ⟨a, r, _, hneg⟩ := not_riemannHypothesis_implies_exists_negative_parityPole hnot
    exact (not_le.mpr hneg) ((correctedScatteringEnergy_floor_iff a _ N).mp (h a _))

/-- In the raw normalization, the same criterion uses its full signed arithmetic defect. -/
theorem riemannHypothesis_iff_scatteringWeilEnergy_full_floor (N : ℕ) :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      -scatteringRawDefect a u N ≤
        scatteringWeilEnergy a (N + 1) (ccmArchimedeanFormToAperture a u) := by
  rw [riemannHypothesis_iff_correctedScatteringEnergy_floor N]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro u
  unfold scatteringRawDefect correctedScatteringEnergy
  constructor <;> intro h <;> linarith only [h]

#print axioms correctedScatteringEnergy_add_jumpTail
#print axioms riemannHypothesis_iff_correctedScatteringEnergy_floor
#print axioms riemannHypothesis_iff_scatteringWeilEnergy_full_floor

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
