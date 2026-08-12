import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalPluckerComplementDepletion

/-!
# Physical Pluecker chirality clears the hostile critical four-cell

P-G79 closes the source-faithfulness defect isolated by P-G76 on the literal hostile cell
`(2,0),(2,1),(3,0),(3,1)`.  No complement averaging is applied.  The physical Gamma-sewn
Cauchy--Binet packet has a strictly positive complement-odd Fisher moment because

* its same-prime consecutive-depth minor at prime `2` is strictly heavier than the corresponding
  minor at prime `3`; and
* the prime-`3` Fisher clock is strictly larger than the prime-`2` clock.

Consequently the physical complement-Fisher Schur fraction is strictly greater than `1/2`, and
the resulting physical residual hostile mass lies below the completed-seam ceiling `29/625`.
This is an unconditional local source theorem.  It does not identify the scalar Schur fraction
with a global Feshbach elimination; that producer theorem remains separate.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- Closed arithmetic form of the first Gamma-sewn Rees boundary amplitude. -/
theorem gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq (p : Nat.Primes) :
    RHTower.gammaSewnMobiusApertureBoundaryAmplitude p =
      Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  rw [RHTower.gammaSewnMobiusApertureBoundaryAmplitude,
    RHTower.gammaSewnMobiusReesPrincipalSymbol,
    RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  field_simp [hp0.ne']
  ring

/-- Exact normalized form of the prime-`2` consecutive-depth physical minor. -/
theorem gammaSewnCriticalPhysicalPlucker_p2ConsecutiveRawWeight_eq :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight
        gammaSewnCriticalPlucker_hostileHarmonicAperture
        gammaSewnCriticalPlucker_hostileRate
        gammaSewnCriticalPlucker_hostileCell 0 =
      4 * gammaSewnCriticalPlucker_hostileHarmonicAperture ^ 2 /
        (81 * Real.log 2 ^ 2 *
          ((1 / 4 : ℝ) -
              (gammaSewnCriticalPlucker_hostileHarmonicAperture / Real.log 2) ^ 2) ^ 2 *
          ((9 / 4 : ℝ) -
              (gammaSewnCriticalPlucker_hostileHarmonicAperture / Real.log 2) ^ 2) ^ 2) := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have ha0 := gammaSewnCriticalPlucker_hostileHarmonicAperture_boundary_ne (0 : Fin 4)
  have ha1 := gammaSewnCriticalPlucker_hostileHarmonicAperture_boundary_ne (1 : Fin 4)
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.twoBoundaryCauchyPairPluckerSq,
    RHTower.twoBoundaryCauchyPairPlucker,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnCriticalPlucker_hostileRate,
    gammaSewnCriticalPlucker_hostileCell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
  field_simp
  ring

/-- Exact normalized form of the prime-`3` consecutive-depth physical minor. -/
theorem gammaSewnCriticalPhysicalPlucker_p3ConsecutiveRawWeight_eq :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight
        gammaSewnCriticalPlucker_hostileHarmonicAperture
        gammaSewnCriticalPlucker_hostileRate
        gammaSewnCriticalPlucker_hostileCell 5 =
      4 * gammaSewnCriticalPlucker_hostileHarmonicAperture ^ 2 /
        (256 * Real.log 3 ^ 2 *
          ((1 / 4 : ℝ) -
              (gammaSewnCriticalPlucker_hostileHarmonicAperture / Real.log 3) ^ 2) ^ 2 *
          ((9 / 4 : ℝ) -
              (gammaSewnCriticalPlucker_hostileHarmonicAperture / Real.log 3) ^ 2) ^ 2) := by
  have hL : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.twoBoundaryCauchyPairPluckerSq,
    RHTower.twoBoundaryCauchyPairPlucker,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnCriticalPlucker_hostileRate,
    gammaSewnCriticalPlucker_hostileCell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
  field_simp
  ring

/-- Prime damping and normalized aperture monotonicity make the physical prime-`2` minor strictly
heavier than its complementary prime-`3` minor. -/
theorem gammaSewnCriticalPhysicalPlucker_p3ConsecutiveRawWeight_lt_p2 :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight
        gammaSewnCriticalPlucker_hostileHarmonicAperture
        gammaSewnCriticalPlucker_hostileRate
        gammaSewnCriticalPlucker_hostileCell 5 <
      RHTower.gammaSewnFourRateBoundaryPairRawWeight
        gammaSewnCriticalPlucker_hostileHarmonicAperture
        gammaSewnCriticalPlucker_hostileRate
        gammaSewnCriticalPlucker_hostileCell 0 := by
  let a := gammaSewnCriticalPlucker_hostileHarmonicAperture
  let L2 := Real.log 2
  let L3 := Real.log 3
  let u2 := a / L2
  let u3 := a / L3
  let A2 := (1 / 4 : ℝ) - u2 ^ 2
  let A3 := (1 / 4 : ℝ) - u3 ^ 2
  let B2 := (9 / 4 : ℝ) - u2 ^ 2
  let B3 := (9 / 4 : ℝ) - u3 ^ 2
  have ha : 0 < a := gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
  have hL2 : 0 < L2 := Real.log_pos (by norm_num)
  have hL3 : 0 < L3 := Real.log_pos (by norm_num)
  have hL23 : L2 < L3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have haL2 : a < L2 / 2 := by
    simpa [a, L2, div_eq_mul_inv, mul_comm, gammaSewnCriticalPlucker_hostileRate,
      gammaSewnCriticalPlucker_hostileCell,
      RHTower.gammaSewnMobiusApertureCellMidHeight] using
        gammaSewnCriticalPlucker_hostileHarmonicAperture_lt_rate (0 : Fin 4)
  have hu2 : 0 < u2 := div_pos ha hL2
  have hu3 : 0 < u3 := div_pos ha hL3
  have hu3u2 : u3 < u2 := by
    apply (div_lt_div_iff₀ hL3 hL2).2
    exact mul_lt_mul_of_pos_left hL23 ha
  have hu2half : u2 < 1 / 2 := by
    apply (div_lt_iff₀ hL2).2
    nlinarith
  have hu3sq_u2sq : u3 ^ 2 < u2 ^ 2 :=
    (sq_lt_sq₀ hu3.le hu2.le).2 hu3u2
  have hA2 : 0 < A2 := by
    dsimp [A2]
    nlinarith [sq_nonneg (u2 - 1 / 2)]
  have hA3 : 0 < A3 := by
    dsimp [A3]
    nlinarith
  have hA23 : A2 < A3 := by
    dsimp [A2, A3]
    linarith
  have hB2 : 0 < B2 := by
    dsimp [B2]
    nlinarith [sq_nonneg u2]
  have hB3 : 0 < B3 := by
    dsimp [B3]
    nlinarith [sq_nonneg u3]
  have hB23 : B2 < B3 := by
    dsimp [B2, B3]
    linarith
  have hA23sq : A2 ^ 2 < A3 ^ 2 :=
    (sq_lt_sq₀ hA2.le hA3.le).2 hA23
  have hB23sq : B2 ^ 2 < B3 ^ 2 :=
    (sq_lt_sq₀ hB2.le hB3.le).2 hB23
  have hL23sq : L2 ^ 2 < L3 ^ 2 :=
    (sq_lt_sq₀ hL2.le hL3.le).2 hL23
  have hbase : 81 * L2 ^ 2 < 256 * L3 ^ 2 := by
    have hfirst : 81 * L2 ^ 2 < 81 * L3 ^ 2 :=
      mul_lt_mul_of_pos_left hL23sq (by norm_num)
    have hsecond : 81 * L3 ^ 2 < 256 * L3 ^ 2 := by
      nlinarith [sq_pos_of_pos hL3]
    exact hfirst.trans hsecond
  have hbase_pos : 0 < 81 * L2 ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hL2)
  have hbase3_pos : 0 < 256 * L3 ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hL3)
  have hbaseA : (81 * L2 ^ 2) * A2 ^ 2 < (256 * L3 ^ 2) * A3 ^ 2 :=
    mul_lt_mul hbase hA23sq.le (sq_pos_of_pos hA2) hbase3_pos.le
  have hden :
      (81 * L2 ^ 2 * A2 ^ 2) * B2 ^ 2 <
        (256 * L3 ^ 2 * A3 ^ 2) * B3 ^ 2 :=
    mul_lt_mul hbaseA hB23sq.le (sq_pos_of_pos hB2)
      (mul_nonneg hbase3_pos.le (sq_nonneg A3))
  have hden2 : 0 < (81 * L2 ^ 2 * A2 ^ 2) * B2 ^ 2 := by positivity
  have hden3 : 0 < (256 * L3 ^ 2 * A3 ^ 2) * B3 ^ 2 := by positivity
  rw [gammaSewnCriticalPhysicalPlucker_p2ConsecutiveRawWeight_eq,
    gammaSewnCriticalPhysicalPlucker_p3ConsecutiveRawWeight_eq]
  change 4 * a ^ 2 / ((256 * L3 ^ 2 * A3 ^ 2) * B3 ^ 2) <
    4 * a ^ 2 / ((81 * L2 ^ 2 * A2 ^ 2) * B2 ^ 2)
  apply (div_lt_div_iff₀ hden3 hden2).2
  exact mul_lt_mul_of_pos_left hden (mul_pos (by norm_num) (sq_pos_of_pos ha))

/-- Literal, unsymmetrized Gamma-sewn boundary-minor probability on the hostile cell. -/
def gammaSewnCriticalPhysicalPlucker_probability : Fin 6 → ℝ :=
  RHTower.gammaSewnFourRateBoundaryPairProbability
    gammaSewnCriticalPlucker_hostileHarmonicAperture
    gammaSewnCriticalPlucker_hostileRate
    gammaSewnCriticalPlucker_hostileCell

theorem gammaSewnCriticalPhysicalPlucker_probability_five_lt_zero :
    gammaSewnCriticalPhysicalPlucker_probability 5 <
      gammaSewnCriticalPhysicalPlucker_probability 0 := by
  unfold gammaSewnCriticalPhysicalPlucker_probability
    RHTower.gammaSewnFourRateBoundaryPairProbability
  apply (div_lt_div_iff₀ gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos
    gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos).2
  exact mul_lt_mul_of_pos_right
    gammaSewnCriticalPhysicalPlucker_p3ConsecutiveRawWeight_lt_p2
    gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos

theorem gammaSewnCriticalPhysicalPlucker_p2Fisher_lt_p3 :
    RHTower.gammaSewnMobiusApertureBoundaryFisherClock gammaSewnCriticalPlucker_p2 <
      RHTower.gammaSewnMobiusApertureBoundaryFisherClock gammaSewnCriticalPlucker_p3 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  unfold RHTower.gammaSewnMobiusApertureBoundaryFisherClock
  norm_num [gammaSewnCriticalPlucker_p2, gammaSewnCriticalPlucker_p3,
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo,
    RHTower.gammaSewnMobiusApertureStokesPrimeThree]
  nlinarith

/-- On this cross-prime cell all mixed complementary pairs cancel.  The entire complement-odd
Fisher moment is the product of one physical minor imbalance and one prime-clock imbalance. -/
theorem gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_eq :
    (∑ s, gammaSewnCriticalPlucker_complementChirality
          gammaSewnCriticalPhysicalPlucker_probability s *
        RHTower.gammaSewnFourRateComplementaryFisher
          gammaSewnCriticalPlucker_hostileCell s) =
      2 * (gammaSewnCriticalPhysicalPlucker_probability 0 -
          gammaSewnCriticalPhysicalPlucker_probability 5) *
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock gammaSewnCriticalPlucker_p3 -
          RHTower.gammaSewnMobiusApertureBoundaryFisherClock gammaSewnCriticalPlucker_p2) := by
  simp [Fin.sum_univ_succ, gammaSewnCriticalPlucker_complementChirality,
    gammaSewnCriticalPlucker_complementIndex,
    RHTower.gammaSewnFourRateComplementaryFisher,
    RHTower.fourRateComplementarySum,
    RHTower.fourRatePairComplementLeft,
    RHTower.fourRatePairComplementRight,
    gammaSewnCriticalPlucker_hostileCell]
  ring

theorem gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_pos :
    0 < ∑ s, gammaSewnCriticalPlucker_complementChirality
          gammaSewnCriticalPhysicalPlucker_probability s *
        RHTower.gammaSewnFourRateComplementaryFisher
          gammaSewnCriticalPlucker_hostileCell s := by
  rw [gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_eq]
  exact mul_pos
    (mul_pos (by norm_num)
      (sub_pos.mpr gammaSewnCriticalPhysicalPlucker_probability_five_lt_zero))
    (sub_pos.mpr gammaSewnCriticalPhysicalPlucker_p2Fisher_lt_p3)

/-- **Physical half-threshold gain.**  The literal source packet, without complement averaging,
extracts strictly more than half of the hostile cell's total Fisher clock. -/
theorem gammaSewnCriticalPhysicalPlucker_schurFraction_gt_half :
    (1 / 2 : ℝ) < gammaSewnCriticalPlucker_schurFraction
      gammaSewnCriticalPhysicalPlucker_probability gammaSewnCriticalPlucker_hostileCell := by
  have hsum : ∑ s, gammaSewnCriticalPhysicalPlucker_probability s = 1 :=
    RHTower.sum_gammaSewnFourRateBoundaryPairProbability
      gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos.ne'
  have hdecomp := gammaSewnCriticalPlucker_complementaryFisherMean_eq_half_add_chirality
    gammaSewnCriticalPhysicalPlucker_probability gammaSewnCriticalPlucker_hostileCell hsum
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher
      gammaSewnCriticalPlucker_hostileCell := by
    unfold RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
    exact add_pos
      (add_pos
        (add_pos
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  unfold gammaSewnCriticalPlucker_schurFraction
  apply (lt_div_iff₀ htotal).2
  nlinarith [gammaSewnCriticalPhysicalPlucker_chiralityFisherMoment_pos]

/-- **Unconditional physical local adequacy.**  The literal Gamma-sewn Cauchy--Binet packet clears
the critical four-cell mass ceiling which defeated raw and first-information carriers. -/
theorem gammaSewnCriticalPhysicalPlucker_reducedHostileMass_lt_ceiling :
    ∑ i : Fin 4,
        gammaSewnCriticalPlucker_reducedWeight
          gammaSewnCriticalPhysicalPlucker_probability
          gammaSewnCriticalPlucker_hostileCell
          (gammaSewnCriticalPlucker_hostileCell i) <
      29 / 625 := by
  apply lt_of_lt_of_le _
    gammaSewnCriticalPlucker_orientationSymmetrizedHostileMass_lt_ceiling.le
  have hterm (i : Fin 4) :
      gammaSewnCriticalPlucker_reducedWeight
          gammaSewnCriticalPhysicalPlucker_probability
          gammaSewnCriticalPlucker_hostileCell
          (gammaSewnCriticalPlucker_hostileCell i) <
        (1 / 2 : ℝ) *
          gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
            (gammaSewnCriticalPlucker_hostileCell i) := by
    unfold gammaSewnCriticalPlucker_reducedWeight
    have hweight := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos
      (gammaSewnCriticalPlucker_hostileCell i)
    nlinarith [gammaSewnCriticalPhysicalPlucker_schurFraction_gt_half]
  simp [Fin.sum_univ_succ]
  nlinarith [hterm 0, hterm 1, hterm 2, hterm 3]

end RHTower.HedenmalmThetaSource
