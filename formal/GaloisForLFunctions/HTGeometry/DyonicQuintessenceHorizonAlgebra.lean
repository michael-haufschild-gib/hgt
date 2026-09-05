import GaloisForLFunctions.HTGeometry.KerrNewmanHorizonAlgebra
import GaloisForLFunctions.HTGeometry.KerrNewmanEinsteinMaxwellAlgebra

/-!
# Dyonic cosmological black-hole algebra with quintessence

Exact horizon, stationary-limit, and electromagnetic-duality identities from arXiv:2609.04111.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def dyonicChargeSq (electric magnetic : ℝ) : ℝ :=
  electric ^ 2 + magnetic ^ 2

def quintessenceRadialPower (omega radius : ℝ) : ℝ :=
  Real.rpow radius (1 - 3 * omega)

theorem quintessenceRadialPower_oneThird (radius : ℝ) :
    quintessenceRadialPower (1 / 3) radius = 1 := by
  unfold quintessenceRadialPower
  convert Real.rpow_zero radius using 1
  all_goals norm_num

theorem quintessenceRadialPower_zero (radius : ℝ) :
    quintessenceRadialPower 0 radius = radius := by
  unfold quintessenceRadialPower
  convert Real.rpow_one radius using 1
  all_goals norm_num

theorem quintessenceRadialPower_negOne (radius : ℝ) :
    quintessenceRadialPower (-1) radius = radius ^ 4 := by
  unfold quintessenceRadialPower
  convert Real.rpow_natCast radius 4 using 1
  all_goals norm_num

def dyonicKerrNewmanDelta
    (mass spin electric magnetic radius : ℝ) : ℝ :=
  radius ^ 2 - 2 * mass * radius + spin ^ 2 + dyonicChargeSq electric magnetic

def dyonicCosmologicalQuintessenceDelta
    (mass spin electric magnetic cosmological quintessence omega radius : ℝ) : ℝ :=
  dyonicKerrNewmanDelta mass spin electric magnetic radius -
    cosmological * radius ^ 4 / 3 -
    quintessence * quintessenceRadialPower omega radius

def dyonicCosmologicalQuintessenceStationaryLimit
    (mass spin electric magnetic cosmological quintessence omega radius polar : ℝ) : ℝ :=
  dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
      quintessence omega radius - spin ^ 2 * Real.sin polar ^ 2

/-- Quartic carrier for all equation-of-state values whose radial source reduces to degree `≤ 1`. -/
def dyonicCosmologicalHorizonQuartic
    (mass spin electric magnetic cosmological linearSource constantSource : ℝ) :
    Polynomial ℝ :=
  Polynomial.C (-cosmological / 3) * Polynomial.X ^ 4 +
    Polynomial.X ^ 2 +
    Polynomial.C (-2 * mass - linearSource) * Polynomial.X +
    Polynomial.C (spin ^ 2 + dyonicChargeSq electric magnetic - constantSource)

theorem dyonicCosmologicalHorizonQuartic_eval
    (mass spin electric magnetic cosmological linearSource constantSource radius : ℝ) :
    Polynomial.eval radius
        (dyonicCosmologicalHorizonQuartic mass spin electric magnetic cosmological
          linearSource constantSource) =
      radius ^ 2 - 2 * mass * radius + spin ^ 2 +
        dyonicChargeSq electric magnetic - cosmological * radius ^ 4 / 3 -
        linearSource * radius - constantSource := by
  simp [dyonicCosmologicalHorizonQuartic]
  ring

theorem dyonicCosmologicalHorizonQuartic_natDegree_le_four
    (mass spin electric magnetic cosmological linearSource constantSource : ℝ) :
    (dyonicCosmologicalHorizonQuartic mass spin electric magnetic cosmological
      linearSource constantSource).natDegree ≤ 4 := by
  unfold dyonicCosmologicalHorizonQuartic
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  simp only [max_le_iff]
  constructor
  · refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp only [max_le_iff]
    constructor
    · refine (Polynomial.natDegree_add_le _ _).trans ?_
      simp only [max_le_iff]
      constructor
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
      · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · simp

theorem dyonicChargeSq_swap (electric magnetic : ℝ) :
    dyonicChargeSq electric magnetic = dyonicChargeSq magnetic electric := by
  simp [dyonicChargeSq, add_comm]

theorem dyonicChargeSq_neg_electric (electric magnetic : ℝ) :
    dyonicChargeSq (-electric) magnetic = dyonicChargeSq electric magnetic := by
  simp [dyonicChargeSq]

theorem dyonicChargeSq_neg_magnetic (electric magnetic : ℝ) :
    dyonicChargeSq electric (-magnetic) = dyonicChargeSq electric magnetic := by
  simp [dyonicChargeSq]

theorem dyonicChargeSq_dualityRotate (angle electric magnetic : ℝ) :
    dyonicChargeSq
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).1
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).2 =
      dyonicChargeSq electric magnetic := by
  have h := kerrNewmanCanonicalMaxwellStressMagnitude_dualityRotate
    angle electric magnetic
  unfold kerrNewmanCanonicalMaxwellStressMagnitude at h
  unfold dyonicChargeSq
  nlinarith

theorem dyonicKerrNewmanDelta_eq_kerrNewmanDelta_combined
    (mass spin electric magnetic radius : ℝ) :
    dyonicKerrNewmanDelta mass spin electric magnetic radius =
      kerrNewmanDelta mass spin (Real.sqrt (dyonicChargeSq electric magnetic)) radius := by
  rw [kerrNewmanDelta]
  rw [Real.sq_sqrt]
  · simp [dyonicKerrNewmanDelta, dyonicChargeSq]
  · simp [dyonicChargeSq]
    positivity

theorem dyonicKerrNewmanDelta_completeSquare
    (mass spin electric magnetic radius : ℝ) :
    dyonicKerrNewmanDelta mass spin electric magnetic radius =
      (radius - mass) ^ 2 -
        (mass ^ 2 - spin ^ 2 - dyonicChargeSq electric magnetic) := by
  simp [dyonicKerrNewmanDelta, dyonicChargeSq]
  ring

theorem dyonicKerrNewmanDelta_zero_iff
    (mass spin electric magnetic radius : ℝ) :
    dyonicKerrNewmanDelta mass spin electric magnetic radius = 0 ↔
      (radius - mass) ^ 2 =
        mass ^ 2 - spin ^ 2 - dyonicChargeSq electric magnetic := by
  rw [dyonicKerrNewmanDelta_completeSquare]
  exact sub_eq_zero

theorem dyonicKerrNewmanDelta_at_mass_zero_iff_extremal
    (mass spin electric magnetic : ℝ) :
    dyonicKerrNewmanDelta mass spin electric magnetic mass = 0 ↔
      mass ^ 2 = spin ^ 2 + electric ^ 2 + magnetic ^ 2 := by
  rw [dyonicKerrNewmanDelta_completeSquare]
  simp [dyonicChargeSq]
  constructor <;> intro h <;> nlinarith

theorem dyonicKerrNewmanDelta_extremal_iff_perfectSquare
    (mass spin electric magnetic : ℝ) :
    (∀ radius, dyonicKerrNewmanDelta mass spin electric magnetic radius =
        (radius - mass) ^ 2) ↔
      mass ^ 2 = spin ^ 2 + electric ^ 2 + magnetic ^ 2 := by
  constructor
  · intro h
    have hm := h mass
    simp [dyonicKerrNewmanDelta, dyonicChargeSq] at hm
    nlinarith
  · intro h radius
    rw [dyonicKerrNewmanDelta_completeSquare]
    simp [dyonicChargeSq]
    nlinarith

theorem dyonicKerrNewmanDelta_dualityRotate
    (angle mass spin electric magnetic radius : ℝ) :
    dyonicKerrNewmanDelta mass spin
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).1
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).2 radius =
      dyonicKerrNewmanDelta mass spin electric magnetic radius := by
  simp [dyonicKerrNewmanDelta, dyonicChargeSq_dualityRotate]

theorem dyonicCosmologicalQuintessenceDelta_zero_sources
    (mass spin electric magnetic omega radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic 0 0 omega radius =
      dyonicKerrNewmanDelta mass spin electric magnetic radius := by
  simp [dyonicCosmologicalQuintessenceDelta]

/-- At `ω = 1/3`, quintessence is a constant shift of the horizon function. -/
theorem dyonicCosmologicalQuintessenceDelta_oneThird
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence (1 / 3) radius =
      dyonicKerrNewmanDelta mass spin electric magnetic radius -
        cosmological * radius ^ 4 / 3 - quintessence := by
  rw [dyonicCosmologicalQuintessenceDelta, quintessenceRadialPower_oneThird]
  ring

/-- At `ω = 0`, quintessence is exactly a mass-parameter translation. -/
theorem dyonicCosmologicalQuintessenceDelta_zeroOmega
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence 0 radius =
      dyonicKerrNewmanDelta (mass + quintessence / 2) spin electric magnetic radius -
        cosmological * radius ^ 4 / 3 := by
  rw [dyonicCosmologicalQuintessenceDelta, quintessenceRadialPower_zero]
  simp only [dyonicKerrNewmanDelta]
  ring

theorem dyonicCosmologicalQuintessenceDelta_zeroOmega_at_shiftedMass_zero_iff_extremal
    (mass spin electric magnetic quintessence : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic 0 quintessence 0
        (mass + quintessence / 2) = 0 ↔
      (mass + quintessence / 2) ^ 2 =
        spin ^ 2 + electric ^ 2 + magnetic ^ 2 := by
  rw [dyonicCosmologicalQuintessenceDelta_zeroOmega]
  simpa using dyonicKerrNewmanDelta_at_mass_zero_iff_extremal
    (mass + quintessence / 2) spin electric magnetic

/-- At `ω = -1`, quintessence is exactly a cosmological-parameter translation. -/
theorem dyonicCosmologicalQuintessenceDelta_negOneOmega
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence (-1) radius =
      dyonicKerrNewmanDelta mass spin electric magnetic radius -
        (cosmological + 3 * quintessence) * radius ^ 4 / 3 := by
  rw [dyonicCosmologicalQuintessenceDelta, quintessenceRadialPower_negOne]
  ring

theorem dyonicCosmologicalQuintessenceDelta_negOneOmega_cancelled
    (mass spin electric magnetic quintessence radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic
        (-3 * quintessence) quintessence (-1) radius =
      dyonicKerrNewmanDelta mass spin electric magnetic radius := by
  rw [dyonicCosmologicalQuintessenceDelta_negOneOmega]
  ring

theorem dyonicCosmologicalHorizonQuartic_oneThird_eq_delta
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    Polynomial.eval radius
        (dyonicCosmologicalHorizonQuartic mass spin electric magnetic cosmological
          0 quintessence) =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence (1 / 3) radius := by
  rw [dyonicCosmologicalHorizonQuartic_eval,
    dyonicCosmologicalQuintessenceDelta_oneThird]
  simp [dyonicKerrNewmanDelta]

theorem dyonicCosmologicalHorizonQuartic_zeroOmega_eq_delta
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    Polynomial.eval radius
        (dyonicCosmologicalHorizonQuartic mass spin electric magnetic cosmological
          quintessence 0) =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence 0 radius := by
  rw [dyonicCosmologicalHorizonQuartic_eval,
    dyonicCosmologicalQuintessenceDelta_zeroOmega]
  simp [dyonicKerrNewmanDelta]
  ring

theorem dyonicCosmologicalHorizonQuartic_negOneOmega_eq_delta
    (mass spin electric magnetic cosmological quintessence radius : ℝ) :
    Polynomial.eval radius
        (dyonicCosmologicalHorizonQuartic mass spin electric magnetic
          (cosmological + 3 * quintessence) 0 0) =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence (-1) radius := by
  rw [dyonicCosmologicalHorizonQuartic_eval,
    dyonicCosmologicalQuintessenceDelta_negOneOmega]
  simp [dyonicKerrNewmanDelta]

theorem dyonicCosmologicalQuintessenceDelta_neg_spin
    (mass spin electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass (-spin) electric magnetic cosmological
        quintessence omega radius =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence omega radius := by
  simp [dyonicCosmologicalQuintessenceDelta, dyonicKerrNewmanDelta]

theorem dyonicCosmologicalQuintessenceDelta_dualityRotate
    (angle mass spin electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).1
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).2
        cosmological quintessence omega radius =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence omega radius := by
  simp [dyonicCosmologicalQuintessenceDelta, dyonicKerrNewmanDelta_dualityRotate]

theorem dyonicCosmologicalQuintessenceDelta_parameterDifference
    (mass spin electric magnetic cosmological₁ cosmological₂
      quintessence₁ quintessence₂ omega radius : ℝ) :
    dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological₂
        quintessence₂ omega radius -
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological₁
        quintessence₁ omega radius =
      -(cosmological₂ - cosmological₁) * radius ^ 4 / 3 -
        (quintessence₂ - quintessence₁) * quintessenceRadialPower omega radius := by
  simp [dyonicCosmologicalQuintessenceDelta]
  ring

theorem dyonicCosmologicalQuintessenceStationaryLimit_eq
    (mass spin electric magnetic cosmological quintessence omega radius polar : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius polar =
      radius ^ 2 - 2 * mass * radius + dyonicChargeSq electric magnetic -
        cosmological * radius ^ 4 / 3 -
        quintessence * quintessenceRadialPower omega radius +
        spin ^ 2 * Real.cos polar ^ 2 := by
  unfold dyonicCosmologicalQuintessenceStationaryLimit
    dyonicCosmologicalQuintessenceDelta dyonicKerrNewmanDelta
  have htrig := Real.sin_sq_add_cos_sq polar
  nlinarith

theorem dyonicCosmologicalQuintessenceStationaryLimit_le_delta
    (mass spin electric magnetic cosmological quintessence omega radius polar : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius polar ≤
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence omega radius := by
  unfold dyonicCosmologicalQuintessenceStationaryLimit
  exact sub_le_self _ (mul_nonneg (sq_nonneg spin) (sq_nonneg (Real.sin polar)))

theorem dyonicCosmologicalQuintessenceStationaryLimit_axis
    (mass spin electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius 0 =
      dyonicCosmologicalQuintessenceDelta mass spin electric magnetic cosmological
        quintessence omega radius := by
  simp [dyonicCosmologicalQuintessenceStationaryLimit]

theorem dyonicCosmologicalQuintessenceStationaryLimit_equator
    (mass spin electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius (Real.pi / 2) =
      radius ^ 2 - 2 * mass * radius + dyonicChargeSq electric magnetic -
        cosmological * radius ^ 4 / 3 -
        quintessence * quintessenceRadialPower omega radius := by
  rw [dyonicCosmologicalQuintessenceStationaryLimit_eq]
  simp

theorem dyonicCosmologicalQuintessenceStationaryLimit_equator_spinIndependent
    (mass spin₁ spin₂ electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin₁ electric magnetic
        cosmological quintessence omega radius (Real.pi / 2) =
      dyonicCosmologicalQuintessenceStationaryLimit mass spin₂ electric magnetic
        cosmological quintessence omega radius (Real.pi / 2) := by
  rw [dyonicCosmologicalQuintessenceStationaryLimit_equator,
    dyonicCosmologicalQuintessenceStationaryLimit_equator]

theorem dyonicCosmologicalQuintessenceStationaryLimit_dualityRotate
    (angle mass spin electric magnetic cosmological quintessence omega radius polar : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).1
        (kerrNewmanMaxwellDualityRotate angle electric magnetic).2
        cosmological quintessence omega radius polar =
      dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius polar := by
  simp [dyonicCosmologicalQuintessenceStationaryLimit,
    dyonicCosmologicalQuintessenceDelta_dualityRotate]

theorem dyonicCosmologicalQuintessenceStationaryLimit_zero_iff
    (mass spin electric magnetic cosmological quintessence omega radius polar : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius polar = 0 ↔
      cosmological * radius ^ 4 / 3 - radius ^ 2 + 2 * mass * radius +
          quintessence * quintessenceRadialPower omega radius -
          dyonicChargeSq electric magnetic - spin ^ 2 * Real.cos polar ^ 2 = 0 := by
  rw [dyonicCosmologicalQuintessenceStationaryLimit_eq]
  constructor <;> intro h <;> linarith

theorem dyonicCosmologicalQuintessenceStationaryLimit_equator_zero_iff
    (mass spin electric magnetic cosmological quintessence omega radius : ℝ) :
    dyonicCosmologicalQuintessenceStationaryLimit mass spin electric magnetic
        cosmological quintessence omega radius (Real.pi / 2) = 0 ↔
      cosmological * radius ^ 4 / 3 - radius ^ 2 + 2 * mass * radius +
          quintessence * quintessenceRadialPower omega radius -
          dyonicChargeSq electric magnetic = 0 := by
  rw [dyonicCosmologicalQuintessenceStationaryLimit_equator]
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions.HTGeometry
