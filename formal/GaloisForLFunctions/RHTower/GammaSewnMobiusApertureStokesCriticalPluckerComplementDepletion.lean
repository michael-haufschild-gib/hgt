import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalInformationCarrierNoGo
import GaloisForLFunctions.RHTower.GammaSewnFourRatePluckerConnector
import GaloisForLFunctions.RHTower.EulerFisherLowTemperature

/-!
# Critical Pluecker complement depletion

The first-information channel is too weak because it acts diagonally after source-label
compression. The existing four-rate Gamma Pluecker carrier provides a coherent pre-compression
alternative. Its six boundary minors have a canonical complement involution, pairing each selected
two-cell orientation with the retained complementary orientation.

Averaging every boundary probability with its complement forces the complementary Fisher fraction
to exactly one half of total Fisher mass for every nondegenerate source cell. No scalar is fitted.
For the hostile critical cell (2,0), (2,1), (3,0), (3,1), rational source bounds prove that applying
this exact half-factor to the information-depleted masses puts their total below 29/625. Thus the
coherent complement channel clears the four-atom mass obstruction that survives every diagonal
first-information subtraction.

This is an unconditional local adequacy theorem, not a global completed-seam identification.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalPlucker_complementIndex : Fin 6 → Fin 6 := ![5, 4, 3, 2, 1, 0]

theorem gammaSewnCriticalPlucker_complementIndex_involutive : Function.Involutive gammaSewnCriticalPlucker_complementIndex := by
  intro s
  fin_cases s <;> rfl

theorem gammaSewnCriticalPlucker_complementIndex_bijective : Function.Bijective gammaSewnCriticalPlucker_complementIndex :=
  gammaSewnCriticalPlucker_complementIndex_involutive.bijective

theorem gammaSewnCriticalPlucker_complementaryFisher_complementIndex
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    RHTower.gammaSewnFourRateComplementaryFisher cell (gammaSewnCriticalPlucker_complementIndex s) =
      RHTower.gammaSewnFourRateSelectedFisher cell s := by
  fin_cases s <;>
    simp [gammaSewnCriticalPlucker_complementIndex, RHTower.gammaSewnFourRateComplementaryFisher,
      RHTower.gammaSewnFourRateSelectedFisher, RHTower.fourRateComplementarySum,
      RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
      RHTower.fourRatePairRight, RHTower.fourRatePairComplementLeft,
      RHTower.fourRatePairComplementRight]

def gammaSewnCriticalPlucker_symmetrize (weight : Fin 6 → ℝ) (s : Fin 6) : ℝ :=
  (weight s + weight (gammaSewnCriticalPlucker_complementIndex s)) / 2

theorem gammaSewnCriticalPlucker_sum_symmetrize (weight : Fin 6 → ℝ) :
    ∑ s, gammaSewnCriticalPlucker_symmetrize weight s = ∑ s, weight s := by
  simp [gammaSewnCriticalPlucker_symmetrize, gammaSewnCriticalPlucker_complementIndex, Fin.sum_univ_succ]
  ring

theorem gammaSewnCriticalPlucker_symmetrized_complementaryFisherMean_eq_half_total
    (weight : Fin 6 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ)
    (hweight : ∑ s, weight s = 1) :
    RHTower.complementaryFisherMean (gammaSewnCriticalPlucker_symmetrize weight)
        (RHTower.gammaSewnFourRateComplementaryFisher cell) =
      (1 / 2 : ℝ) * RHTower.gammaSewnFourRateTotalFisher cell := by
  have hselcomp := RHTower.gammaSewnFourRateSelectedFisher_add_complementaryFisher cell
  simp only [RHTower.complementaryFisherMean, gammaSewnCriticalPlucker_symmetrize]
  have hexpand :
      (∑ s, (weight s + weight (gammaSewnCriticalPlucker_complementIndex s)) / 2 *
        RHTower.gammaSewnFourRateComplementaryFisher cell s) =
      (1 / 2 : ℝ) *
        ((∑ s, weight s * RHTower.gammaSewnFourRateComplementaryFisher cell s) +
          ∑ s, weight (gammaSewnCriticalPlucker_complementIndex s) *
            RHTower.gammaSewnFourRateComplementaryFisher cell s) := by
    simp only [Fin.sum_univ_succ]
    ring
  rw [hexpand]
  have hcomp :
      (∑ s, weight (gammaSewnCriticalPlucker_complementIndex s) *
        RHTower.gammaSewnFourRateComplementaryFisher cell s) =
      ∑ s, weight s * RHTower.gammaSewnFourRateSelectedFisher cell s := by
    rw [← gammaSewnCriticalPlucker_complementIndex_bijective.sum_comp]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [gammaSewnCriticalPlucker_complementIndex_involutive s,
      gammaSewnCriticalPlucker_complementaryFisher_complementIndex]
  rw [hcomp]
  have htotal :
      (∑ s, weight s * RHTower.gammaSewnFourRateSelectedFisher cell s) +
          ∑ s, weight s * RHTower.gammaSewnFourRateComplementaryFisher cell s =
        RHTower.gammaSewnFourRateTotalFisher cell := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ s, (weight s * RHTower.gammaSewnFourRateSelectedFisher cell s +
        weight s * RHTower.gammaSewnFourRateComplementaryFisher cell s)) =
          ∑ s, weight s * RHTower.gammaSewnFourRateTotalFisher cell := by
            apply Finset.sum_congr rfl
            intro s _hs
            rw [← mul_add, hselcomp]
      _ = RHTower.gammaSewnFourRateTotalFisher cell := by
        rw [← Finset.sum_mul, hweight, one_mul]
  rw [add_comm
    (∑ s, weight s * RHTower.gammaSewnFourRateComplementaryFisher cell s)
    (∑ s, weight s * RHTower.gammaSewnFourRateSelectedFisher cell s), htotal]

def gammaSewnCriticalPlucker_symProbability
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : Fin 6 → ℝ :=
  gammaSewnCriticalPlucker_symmetrize (RHTower.gammaSewnFourRateBoundaryPairProbability a rate cell)

theorem gammaSewnCriticalPlucker_sum_symProbability
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    ∑ s, gammaSewnCriticalPlucker_symProbability a rate cell s = 1 := by
  rw [gammaSewnCriticalPlucker_symProbability, gammaSewnCriticalPlucker_sum_symmetrize]
  exact RHTower.sum_gammaSewnFourRateBoundaryPairProbability hpartition

theorem gammaSewnCriticalPlucker_symSchurFactor_eq_half
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    RHTower.complementaryFisherMean (gammaSewnCriticalPlucker_symProbability a rate cell)
        (RHTower.gammaSewnFourRateComplementaryFisher cell) /
        RHTower.gammaSewnFourRateTotalFisher cell = 1 / 2 := by
  rw [gammaSewnCriticalPlucker_symProbability,
    gammaSewnCriticalPlucker_symmetrized_complementaryFisherMean_eq_half_total _ _
      (RHTower.sum_gammaSewnFourRateBoundaryPairProbability hpartition)]
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher cell := by
    unfold RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
    exact add_pos
      (add_pos
        (add_pos
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  field_simp [htotal.ne']

/-- Dimensionless coherent Schur fraction before scalar compression. -/
def gammaSewnCriticalPlucker_schurFraction
    (weight : Fin 6 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  RHTower.complementaryFisherMean weight
      (RHTower.gammaSewnFourRateComplementaryFisher cell) /
    RHTower.gammaSewnFourRateTotalFisher cell

/-- Residual critical Stokes weight after the complement-Fisher Schur fraction is removed.  The
prime-power label remains unchanged; the non-diagonal information is carried by `weight` and
`cell` before this scalar output is formed. -/
def gammaSewnCriticalPlucker_reducedWeight
    (weight : Fin 6 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ)
    (pk : Nat.Primes × ℕ) : ℝ :=
  (1 - gammaSewnCriticalPlucker_schurFraction weight cell) *
    gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk

/-- Complement symmetrization forces every reduced prime-power weight to exactly one half of the
first-information residual. -/
theorem gammaSewnCriticalPlucker_reducedWeight_eq_half
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition :
      ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0)
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalPlucker_reducedWeight
        (gammaSewnCriticalPlucker_symProbability a rate cell) cell pk =
      (1 / 2 : ℝ) *
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
  rw [gammaSewnCriticalPlucker_reducedWeight,
    gammaSewnCriticalPlucker_schurFraction,
    gammaSewnCriticalPlucker_symSchurFactor_eq_half hpartition]
  ring

abbrev gammaSewnCriticalPlucker_p2 : Nat.Primes := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
abbrev gammaSewnCriticalPlucker_p3 : Nat.Primes := RHTower.gammaSewnMobiusApertureStokesPrimeThree

def gammaSewnCriticalPlucker_hostileCell : Fin 4 → Nat.Primes × ℕ :=
  ![(gammaSewnCriticalPlucker_p2, 0), (gammaSewnCriticalPlucker_p2, 1), (gammaSewnCriticalPlucker_p3, 0), (gammaSewnCriticalPlucker_p3, 1)]

def gammaSewnCriticalPlucker_hostileRate (i : Fin 4) : ℝ :=
  RHTower.gammaSewnMobiusApertureCellMidHeight
    (gammaSewnCriticalPlucker_hostileCell i).1 (gammaSewnCriticalPlucker_hostileCell i).2

theorem gammaSewnCriticalPlucker_hostileRate_pos (i : Fin 4) : 0 < gammaSewnCriticalPlucker_hostileRate i := by
  unfold gammaSewnCriticalPlucker_hostileRate RHTower.gammaSewnMobiusApertureCellMidHeight
  exact mul_pos (by positivity)
    (Real.log_pos (by exact_mod_cast (gammaSewnCriticalPlucker_hostileCell i).1.2.one_lt))

theorem gammaSewnCriticalPlucker_hostileRate_injective : Function.Injective gammaSewnCriticalPlucker_hostileRate := by
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have h32 : Real.log 3 < 2 * Real.log 2 :=
    RHTower.log_three_lt_two_mul_log_two
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [gammaSewnCriticalPlucker_hostileRate, gammaSewnCriticalPlucker_hostileCell,
      RHTower.gammaSewnMobiusApertureCellMidHeight] at hij ⊢ <;>
    try norm_num at hij <;>
    nlinarith

def gammaSewnCriticalPlucker_hostileHarmonicAperture : ℝ :=
  (1 + ∑ i : Fin 4, (gammaSewnCriticalPlucker_hostileRate i)⁻¹)⁻¹

theorem gammaSewnCriticalPlucker_hostileHarmonicAperture_pos :
    0 < gammaSewnCriticalPlucker_hostileHarmonicAperture := by
  unfold gammaSewnCriticalPlucker_hostileHarmonicAperture
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => (inv_pos.mpr (gammaSewnCriticalPlucker_hostileRate_pos i)).le)

theorem gammaSewnCriticalPlucker_hostileHarmonicAperture_lt_rate (i : Fin 4) :
    gammaSewnCriticalPlucker_hostileHarmonicAperture < gammaSewnCriticalPlucker_hostileRate i := by
  have hrate := gammaSewnCriticalPlucker_hostileRate_pos i
  have hle : (gammaSewnCriticalPlucker_hostileRate i)⁻¹ ≤
      ∑ j : Fin 4, (gammaSewnCriticalPlucker_hostileRate j)⁻¹ := by
    exact Finset.single_le_sum
      (fun j _ => (inv_pos.mpr (gammaSewnCriticalPlucker_hostileRate_pos j)).le)
      (Finset.mem_univ i)
  have hden : 0 < 1 + ∑ j : Fin 4, (gammaSewnCriticalPlucker_hostileRate j)⁻¹ := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ => (inv_pos.mpr (gammaSewnCriticalPlucker_hostileRate_pos j)).le)
  have hlt : (gammaSewnCriticalPlucker_hostileRate i)⁻¹ <
      1 + ∑ j : Fin 4, (gammaSewnCriticalPlucker_hostileRate j)⁻¹ := by linarith
  unfold gammaSewnCriticalPlucker_hostileHarmonicAperture
  rw [← inv_inv (gammaSewnCriticalPlucker_hostileRate i)]
  exact (inv_lt_inv₀ hden (inv_pos.mpr hrate)).2 hlt

theorem gammaSewnCriticalPlucker_hostileHarmonicAperture_boundary_ne (i : Fin 4) :
    gammaSewnCriticalPlucker_hostileRate i ^ 2 - gammaSewnCriticalPlucker_hostileHarmonicAperture ^ 2 ≠ 0 := by
  apply sub_ne_zero.mpr
  exact ne_of_gt ((sq_lt_sq₀ gammaSewnCriticalPlucker_hostileHarmonicAperture_pos.le
    (gammaSewnCriticalPlucker_hostileRate_pos i).le).2 (gammaSewnCriticalPlucker_hostileHarmonicAperture_lt_rate i))

theorem gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos :
    0 < ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight
      gammaSewnCriticalPlucker_hostileHarmonicAperture gammaSewnCriticalPlucker_hostileRate gammaSewnCriticalPlucker_hostileCell s := by
  exact RHTower.gammaSewnFourRateBoundaryPairPartition_pos
    gammaSewnCriticalPlucker_hostileHarmonicAperture_pos.ne' gammaSewnCriticalPlucker_hostileRate_injective
    gammaSewnCriticalPlucker_hostileHarmonicAperture_boundary_ne

theorem gammaSewnCriticalPlucker_hostileSymSchurFactor_eq_half :
    RHTower.complementaryFisherMean
          (gammaSewnCriticalPlucker_symProbability gammaSewnCriticalPlucker_hostileHarmonicAperture
            gammaSewnCriticalPlucker_hostileRate gammaSewnCriticalPlucker_hostileCell)
          (RHTower.gammaSewnFourRateComplementaryFisher gammaSewnCriticalPlucker_hostileCell) /
        RHTower.gammaSewnFourRateTotalFisher gammaSewnCriticalPlucker_hostileCell =
      1 / 2 := by
  exact gammaSewnCriticalPlucker_symSchurFactor_eq_half gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos.ne'

theorem gammaSewnCriticalPlucker_p2_node_bounds :
    (7 / 10 : ℝ) < RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p2 ∧
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p2 < 71 / 100 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p2
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ 2 = 1 / 2 := by
    simpa [r, gammaSewnCriticalPlucker_p2, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv] using
      RHTower.xiMobiusContinuousApertureDiskNode_half_sq gammaSewnCriticalPlucker_p2
  constructor
  · by_contra h
    have hr : r ≤ 7 / 10 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 7 / 10))]
  · by_contra h
    have hr : 71 / 100 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 71 / 100))]

theorem gammaSewnCriticalPlucker_p3_node_bounds :
    (57 / 100 : ℝ) < RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p3 ∧
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p3 < 58 / 100 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p3
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ 2 = 1 / 3 := by
    simpa [r, gammaSewnCriticalPlucker_p3, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv] using
      RHTower.xiMobiusContinuousApertureDiskNode_half_sq gammaSewnCriticalPlucker_p3
  constructor
  · by_contra h
    have hr : r ≤ 57 / 100 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 57 / 100))]
  · by_contra h
    have hr : 58 / 100 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 58 / 100))]

theorem gammaSewnCriticalPlucker_criticalSquaredWeight_eq (p : Nat.Primes) (e : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, e) =
      2 * RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p ^ 2 *
        (RHTower.xiTransversePrimeApertureDiskNode 1 p /
          (1 + RHTower.xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
        (1 - RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p) ^ 2 *
        RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p ^ e /
        (((e + 1 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ) *
          RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p) := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num)]
  ring

theorem gammaSewnCriticalPlucker_p2_weight_zero_upper :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p2, 0) <
      21 / 500 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p2
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) gammaSewnCriticalPlucker_p2
  have hr := gammaSewnCriticalPlucker_p2_node_bounds
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hc0 : 0 < c := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc : c < 1 := RHTower.gammaSewnMobiusValuationContractionMultiplier_lt_one
    (by norm_num) _
  have hc2 : c ^ 2 < 1 := by nlinarith [sq_nonneg (c - 1)]
  have hgap : (1 - r) ^ 2 < (3 / 10 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ (by linarith [hr.1]) (by linarith [hr.2]) (by norm_num)
  have hprod : c ^ 2 * (1 - r) ^ 2 < (3 / 10 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hlog : (69 / 100 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hden0 : 0 < Real.log 2 * r := by positivity
  have hden : (69 / 100 : ℝ) * (7 / 10) < Real.log 2 * r := by
    exact mul_lt_mul hlog hr.1.le (by norm_num)
      (Real.log_pos (by norm_num)).le
  rw [gammaSewnCriticalPlucker_criticalSquaredWeight_eq]
  simp only [gammaSewnCriticalPlucker_p2, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  simp only [one_mul]
  rw [div_lt_iff₀ (by simpa only [r] using hden0)]
  nlinarith

theorem gammaSewnCriticalPlucker_p3_weight_zero_upper :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p3, 0) <
      3 / 80 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) gammaSewnCriticalPlucker_p3
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) gammaSewnCriticalPlucker_p3
  have hr := gammaSewnCriticalPlucker_p3_node_bounds
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hc0 : 0 < c := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc : c < 1 := RHTower.gammaSewnMobiusValuationContractionMultiplier_lt_one
    (by norm_num) _
  have hc2 : c ^ 2 < 1 := by nlinarith [sq_nonneg (c - 1)]
  have hgap : (1 - r) ^ 2 < (43 / 100 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ (by linarith [hr.1]) (by linarith [hr.2]) (by norm_num)
  have hprod : c ^ 2 * (1 - r) ^ 2 < (43 / 100 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hlog : (109 / 100 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hden0 : 0 < Real.log 3 * r := by positivity
  have hden : (109 / 100 : ℝ) * (57 / 100) < Real.log 3 * r := by
    exact mul_lt_mul hlog hr.1.le (by norm_num)
      (Real.log_pos (by norm_num)).le
  rw [gammaSewnCriticalPlucker_criticalSquaredWeight_eq]
  simp only [gammaSewnCriticalPlucker_p3, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  simp only [one_mul]
  rw [div_lt_iff₀ (by simpa only [r] using hden0)]
  nlinarith

theorem gammaSewnCriticalPlucker_criticalSquaredWeight_depthOne_eq (p : Nat.Primes) :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 1) =
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p / 4 *
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 0) := by
  rw [gammaSewnCriticalPlucker_criticalSquaredWeight_eq, gammaSewnCriticalPlucker_criticalSquaredWeight_eq]
  have hr := (RHTower.xiMobiusContinuousApertureDiskNode_pos (1 / 2) p).ne'
  have hlog := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < (p : ℝ))).ne'
  norm_num
  field_simp [hr, hlog]

theorem gammaSewnCriticalPlucker_p2_weight_one_upper :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p2, 1) <
      3 / 400 := by
  rw [gammaSewnCriticalPlucker_criticalSquaredWeight_depthOne_eq]
  have hr := gammaSewnCriticalPlucker_p2_node_bounds.2
  have hw := gammaSewnCriticalPlucker_p2_weight_zero_upper
  have hr0 := RHTower.xiMobiusContinuousApertureDiskNode_pos (1 / 2) gammaSewnCriticalPlucker_p2
  have hw0 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) (gammaSewnCriticalPlucker_p2, 0)
  nlinarith [mul_pos (sub_pos.mpr hr) (sub_pos.mpr hw)]

theorem gammaSewnCriticalPlucker_p3_weight_one_upper :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p3, 1) <
      11 / 2000 := by
  rw [gammaSewnCriticalPlucker_criticalSquaredWeight_depthOne_eq]
  have hr := gammaSewnCriticalPlucker_p3_node_bounds.2
  have hw := gammaSewnCriticalPlucker_p3_weight_zero_upper
  have hr0 := RHTower.xiMobiusContinuousApertureDiskNode_pos (1 / 2) gammaSewnCriticalPlucker_p3
  have hw0 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) (gammaSewnCriticalPlucker_p3, 0)
  nlinarith [mul_pos (sub_pos.mpr hr) (sub_pos.mpr hw)]

theorem gammaSewnCriticalPlucker_criticalRawFourAtomMass_upper :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p2, 0) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p2, 1) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p3, 0) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (gammaSewnCriticalPlucker_p3, 1) <
      37 / 400 := by
  linarith [gammaSewnCriticalPlucker_p2_weight_zero_upper, gammaSewnCriticalPlucker_p2_weight_one_upper,
    gammaSewnCriticalPlucker_p3_weight_zero_upper, gammaSewnCriticalPlucker_p3_weight_one_upper]

theorem gammaSewnCriticalPlucker_depletedWeight_lt_squaredWeight (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk <
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk := by
  rw [gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
  have hk := gammaSewnMobiusApertureStokesCriticalInformationFactor_pos pk
  have hw := RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk
  nlinarith [mul_pos hk hw]

theorem gammaSewnCriticalPlucker_orientationSymmetrizedHostileMass_lt_ceiling :
    ∑ i : Fin 4,
        (1 / 2 : ℝ) *
          gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
            (gammaSewnCriticalPlucker_hostileCell i) <
      29 / 625 := by
  have h20 := gammaSewnCriticalPlucker_depletedWeight_lt_squaredWeight (gammaSewnCriticalPlucker_p2, 0)
  have h21 := gammaSewnCriticalPlucker_depletedWeight_lt_squaredWeight (gammaSewnCriticalPlucker_p2, 1)
  have h30 := gammaSewnCriticalPlucker_depletedWeight_lt_squaredWeight (gammaSewnCriticalPlucker_p3, 0)
  have h31 := gammaSewnCriticalPlucker_depletedWeight_lt_squaredWeight (gammaSewnCriticalPlucker_p3, 1)
  simp [Fin.sum_univ_succ, gammaSewnCriticalPlucker_hostileCell]
  nlinarith [gammaSewnCriticalPlucker_criticalRawFourAtomMass_upper]

/-- **Local adequacy.**  On the literal hostile critical four-cell, the coherent Pluecker
complement reduction leaves less mass than the completed seam ceiling which defeated both raw and
first-information carriers. -/
theorem gammaSewnCriticalPlucker_reducedHostileMass_lt_ceiling :
    ∑ i : Fin 4,
        gammaSewnCriticalPlucker_reducedWeight
          (gammaSewnCriticalPlucker_symProbability
            gammaSewnCriticalPlucker_hostileHarmonicAperture
            gammaSewnCriticalPlucker_hostileRate
            gammaSewnCriticalPlucker_hostileCell)
          gammaSewnCriticalPlucker_hostileCell
          (gammaSewnCriticalPlucker_hostileCell i) <
      29 / 625 := by
  apply lt_of_eq_of_lt _
    gammaSewnCriticalPlucker_orientationSymmetrizedHostileMass_lt_ceiling
  apply Finset.sum_congr rfl
  intro i _hi
  exact gammaSewnCriticalPlucker_reducedWeight_eq_half
    gammaSewnCriticalPlucker_hostileBoundaryPairPartition_pos.ne' _

end RHTower.HedenmalmThetaSource
