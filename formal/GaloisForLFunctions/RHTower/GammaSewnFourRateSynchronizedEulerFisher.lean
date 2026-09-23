import GaloisForLFunctions.RHTower.GammaSewnSynchronizedEulerFisherBarycenter
import GaloisForLFunctions.RHTower.GammaSewnFourRateSchurFisherCurvature

/-!
# Four-rate synchronized Euler--Fisher Jordan control
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complementary-pair finite part of the regularized infinite Euler depth variance. -/
def gammaSewnFourRateComplementaryEulerHeightFinitePart
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateComplementarySum
    (fun i => (-1 / 3 : ℝ) * Real.log ((cell i).1 : ℝ) ^ (2 : ℕ)) s

/-- Complementary-pair boundary Fisher mass supplied by the two-state sewing channel. -/
def gammaSewnFourRateComplementarySewingBoundaryFisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateComplementarySum
    (fun i => Real.log ((cell i).1 : ℝ) ^ (2 : ℕ)) s

theorem gammaSewnFourRateComplementaryEulerHeightFinitePart_eq_neg_half_fisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    gammaSewnFourRateComplementaryEulerHeightFinitePart cell s =
      -(1 / 2 : ℝ) * gammaSewnFourRateComplementaryFisher cell s := by
  have hi := gammaSewnSynchronizedEulerBoundary_height_sewing_three_to_one
    (cell (fourRatePairComplementLeft s)).1
  have hj := gammaSewnSynchronizedEulerBoundary_height_sewing_three_to_one
    (cell (fourRatePairComplementRight s)).1
  unfold gammaSewnFourRateComplementaryEulerHeightFinitePart
    gammaSewnFourRateComplementaryFisher fourRateComplementarySum
  change (-1 / 3 : ℝ) *
          Real.log ((cell (fourRatePairComplementLeft s)).1 : ℝ) ^ (2 : ℕ) +
        (-1 / 3 : ℝ) *
          Real.log ((cell (fourRatePairComplementRight s)).1 : ℝ) ^ (2 : ℕ) =
      -(1 / 2 : ℝ) *
        (gammaSewnMobiusApertureBoundaryFisherClock
            (cell (fourRatePairComplementLeft s)).1 +
          gammaSewnMobiusApertureBoundaryFisherClock
            (cell (fourRatePairComplementRight s)).1)
  rw [hi.1, hj.1]
  ring

theorem gammaSewnFourRateComplementarySewingBoundaryFisher_eq_three_halves_fisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    gammaSewnFourRateComplementarySewingBoundaryFisher cell s =
      (3 / 2 : ℝ) * gammaSewnFourRateComplementaryFisher cell s := by
  have hi := gammaSewnSynchronizedEulerBoundary_height_sewing_three_to_one
    (cell (fourRatePairComplementLeft s)).1
  have hj := gammaSewnSynchronizedEulerBoundary_height_sewing_three_to_one
    (cell (fourRatePairComplementRight s)).1
  unfold gammaSewnFourRateComplementarySewingBoundaryFisher
    gammaSewnFourRateComplementaryFisher fourRateComplementarySum
  change Real.log ((cell (fourRatePairComplementLeft s)).1 : ℝ) ^ (2 : ℕ) +
        Real.log ((cell (fourRatePairComplementRight s)).1 : ℝ) ^ (2 : ℕ) =
      (3 / 2 : ℝ) *
        (gammaSewnMobiusApertureBoundaryFisherClock
            (cell (fourRatePairComplementLeft s)).1 +
          gammaSewnMobiusApertureBoundaryFisherClock
            (cell (fourRatePairComplementRight s)).1)
  rw [hi.2, hj.2]
  ring

/-- Expected negative finite-depth channel over the six source-selected boundary minors. -/
def gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  complementaryFisherMean
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    (gammaSewnFourRateComplementaryEulerHeightFinitePart cell)

/-- Expected positive sewing channel over the same six boundary minors. -/
def gammaSewnFourRateBoundaryComplementarySewingMass
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  complementaryFisherMean
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    (gammaSewnFourRateComplementarySewingBoundaryFisher cell)

theorem gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass_eq_neg_half_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell =
      -(1 / 2 : ℝ) * complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  unfold gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass
    complementaryFisherMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [gammaSewnFourRateComplementaryEulerHeightFinitePart_eq_neg_half_fisher]
  ring

theorem gammaSewnFourRateBoundaryComplementarySewingMass_eq_three_halves_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementarySewingMass a rate cell =
      (3 / 2 : ℝ) * complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  unfold gammaSewnFourRateBoundaryComplementarySewingMass complementaryFisherMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [gammaSewnFourRateComplementarySewingBoundaryFisher_eq_three_halves_fisher]
  ring

/-- The corrected complementary Fisher channel is the exact signed join of the regularized
infinite-depth height mass and the sewing mass. -/
theorem gammaSewnFourRateBoundaryComplementary_heightFinite_add_sewing_eq_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell +
        gammaSewnFourRateBoundaryComplementarySewingMass a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  rw [gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass_eq_neg_half_fisher,
    gammaSewnFourRateBoundaryComplementarySewingMass_eq_three_halves_fisher]
  ring

/-- Exact Jordan ratio: the magnitude of the negative depth finite part is one third of the
positive sewing mass, for every four-rate packet even before nondegeneracy is imposed. -/
theorem gammaSewnFourRateBoundaryComplementary_neg_heightFinite_eq_one_third_sewing
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    -gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell =
      (1 / 3 : ℝ) *
        gammaSewnFourRateBoundaryComplementarySewingMass a rate cell := by
  rw [gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass_eq_neg_half_fisher,
    gammaSewnFourRateBoundaryComplementarySewingMass_eq_three_halves_fisher]
  ring

theorem gammaSewnFourRateBoundaryComplementarySewingMass_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 < gammaSewnFourRateBoundaryComplementarySewingMass a rate cell := by
  unfold gammaSewnFourRateBoundaryComplementarySewingMass complementaryFisherMean
  apply Finset.sum_pos
  · intro s _hs
    apply mul_pos
    · exact gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s
    · unfold gammaSewnFourRateComplementarySewingBoundaryFisher
        fourRateComplementarySum
      apply add_pos
      · exact sq_pos_of_pos (Real.log_pos (by
          exact_mod_cast (cell (fourRatePairComplementLeft s)).1.2.one_lt))
      · exact sq_pos_of_pos (Real.log_pos (by
          exact_mod_cast (cell (fourRatePairComplementRight s)).1.2.one_lt))
  · exact Finset.univ_nonempty

/-- **Source Jordan control.**  On every nondegenerate four-rate boundary packet the sewing mass
is positive, the regularized infinite-depth height mass is negative, its magnitude is exactly one
third of the sewing mass, and their residual is the positive complementary Fisher channel. -/
theorem gammaSewnFourRateBoundaryComplementary_sourceJordanControl
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 < gammaSewnFourRateBoundaryComplementarySewingMass a rate cell ∧
      gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell < 0 ∧
      -gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell =
        (1 / 3 : ℝ) * gammaSewnFourRateBoundaryComplementarySewingMass a rate cell ∧
      gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell +
          gammaSewnFourRateBoundaryComplementarySewingMass a rate cell =
        complementaryFisherMean
          (gammaSewnFourRateBoundaryPairProbability a rate cell)
          (gammaSewnFourRateComplementaryFisher cell) := by
  have hsew := gammaSewnFourRateBoundaryComplementarySewingMass_pos
    (cell := cell) ha hrate hboundary
  have hratio :=
    gammaSewnFourRateBoundaryComplementary_neg_heightFinite_eq_one_third_sewing
      a rate cell
  exact ⟨hsew, by nlinarith, hratio,
    gammaSewnFourRateBoundaryComplementary_heightFinite_add_sewing_eq_fisher a rate cell⟩

/-- The cumulant-corrected four-rate Schur channel inherits the exact signed Jordan join. -/
theorem gammaSewnFourRateSchurCorrectedFisher_eq_heightFinite_add_sewing
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell +
        gammaSewnFourRateBoundaryComplementarySewingMass a rate cell := by
  rw [gammaSewnFourRateSchurCorrectedFisher_eq hpartition,
    gammaSewnFourRateBoundaryComplementary_heightFinite_add_sewing_eq_fisher]

/-- Three-channel refinement of the four-rate Schur curvature: positive selected-height
dispersion, negative regularized complementary-depth mass, and positive sewing mass remain
separate until their exact signed join. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_heightFinite_sewing_dispersion
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -2 * gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell -
      2 * gammaSewnFourRateBoundaryComplementarySewingMass a rate cell -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  rw [gammaSewnFourRateSchurBoundaryLogCurvature_eq hpartition,
    ← gammaSewnFourRateBoundaryComplementary_heightFinite_add_sewing_eq_fisher]
  ring

end

end RHTower
