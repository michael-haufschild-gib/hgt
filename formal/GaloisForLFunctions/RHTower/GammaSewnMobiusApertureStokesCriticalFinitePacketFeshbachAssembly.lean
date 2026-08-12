import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesOrderedPrimeDepthPluckerChirality

/-!
# Finite physical ordered-prime packet Feshbach assembly

P-G82 assembles arbitrary nonempty finite families of P-G81 prime-by-depth packets at the literal
critical harmonic aperture.  Each block is weighted by its physical Cauchy--Binet partition mass;
the numerator and denominator are proved equal to the corresponding raw Fisher sums.  The global
block fraction lies strictly in (1/2,1), and every resulting information-depleted residual remains
positive and strictly below the symmetrized half residual.

This is source-exact finite block assembly, not a fitted convex combination.  Pairing-independent
cofinal completion and identification with the global Gamma/polar Feshbach operator remain open.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

abbrev gammaSewnCriticalFinitePacket_aperture : ℝ := gammaSewnCriticalPlucker_hostileHarmonicAperture

theorem gammaSewnCriticalFinitePacket_aperture_admissible (e : ℕ) (p : Nat.Primes) :
    gammaSewnCriticalFinitePacket_aperture < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ) := by
  have ha2 : gammaSewnCriticalFinitePacket_aperture < Real.log 2 / 2 := by
    simpa [gammaSewnCriticalFinitePacket_aperture, gammaSewnCriticalPlucker_hostileRate,
      gammaSewnCriticalPlucker_hostileCell,
      RHTower.gammaSewnMobiusApertureCellMidHeight, div_eq_mul_inv, mul_comm] using
        gammaSewnCriticalPlucker_hostileHarmonicAperture_lt_rate (0 : Fin 4)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlogle : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp0
      (by exact_mod_cast p.2.two_le)
  have he : (0 : ℝ) ≤ (e : ℝ) := by positivity
  have hc : (1 / 2 : ℝ) ≤ (e : ℝ) + 1 / 2 := by linarith
  have hprod : (1 / 2 : ℝ) * Real.log 2 ≤
      ((e : ℝ) + 1 / 2) * Real.log (p : ℝ) :=
    mul_le_mul hc hlogle hlog2.le (by positivity)
  nlinarith

def gammaSewnCriticalPrimeDepthPacket_Partition (e : ℕ) (p q : Nat.Primes) : ℝ :=
  ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalFinitePacket_aperture
    (gammaSewnOrderedPrimeDepthPlucker_rate e p q)
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s

def gammaSewnCriticalPrimeDepthPacket_Mean (e : ℕ) (p q : Nat.Primes) : ℝ :=
  RHTower.complementaryFisherMean
    (gammaSewnOrderedPrimeDepthPlucker_probability gammaSewnCriticalFinitePacket_aperture e p q)
    (RHTower.gammaSewnFourRateComplementaryFisher
      (gammaSewnOrderedPrimeDepthPlucker_cell e p q))

def gammaSewnCriticalPrimeDepthPacket_Total (e : ℕ) (p q : Nat.Primes) : ℝ :=
  RHTower.gammaSewnFourRateTotalFisher
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q)

theorem gammaSewnCriticalPrimeDepthPacket_Partition_pos {e : ℕ} {p q : Nat.Primes}
    (hpq : (p : ℕ) < (q : ℕ)) : 0 < gammaSewnCriticalPrimeDepthPacket_Partition e p q := by
  exact gammaSewnOrderedPrimeDepthPlucker_partition_pos
    gammaSewnCriticalPlucker_hostileHarmonicAperture_pos hpq
    (gammaSewnCriticalFinitePacket_aperture_admissible e p)

theorem gammaSewnCriticalPrimeDepthPacket_Total_pos (e : ℕ) (p q : Nat.Primes) :
    0 < gammaSewnCriticalPrimeDepthPacket_Total e p q := by
  unfold gammaSewnCriticalPrimeDepthPacket_Total RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
  exact add_pos
    (add_pos
      (add_pos
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
    (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)

theorem gammaSewnCriticalPrimeDepthPacket_Mean_gt_half_total {e : ℕ} {p q : Nat.Primes}
    (hpq : (p : ℕ) < (q : ℕ)) :
    (1 / 2 : ℝ) * gammaSewnCriticalPrimeDepthPacket_Total e p q < gammaSewnCriticalPrimeDepthPacket_Mean e p q := by
  have hfrac := gammaSewnOrderedPrimeDepthPlucker_schurFraction_gt_half
    gammaSewnCriticalPlucker_hostileHarmonicAperture_pos hpq
    (gammaSewnCriticalFinitePacket_aperture_admissible e p)
  unfold gammaSewnCriticalPlucker_schurFraction at hfrac
  exact (lt_div_iff₀ (gammaSewnCriticalPrimeDepthPacket_Total_pos e p q)).mp (by simpa [gammaSewnCriticalPrimeDepthPacket_Mean, gammaSewnCriticalPrimeDepthPacket_Total] using hfrac)

theorem gammaSewnCriticalPrimeDepthPacket_Mean_lt_total {e : ℕ} {p q : Nat.Primes}
    (hpq : (p : ℕ) < (q : ℕ)) :
    gammaSewnCriticalPrimeDepthPacket_Mean e p q < gammaSewnCriticalPrimeDepthPacket_Total e p q := by
  simpa [gammaSewnCriticalPrimeDepthPacket_Mean, gammaSewnCriticalPrimeDepthPacket_Total] using
    gammaSewnOrderedPrimeDepthPlucker_complementaryFisherMean_lt_total
      gammaSewnCriticalPlucker_hostileHarmonicAperture_pos hpq
      (gammaSewnCriticalFinitePacket_aperture_admissible e p)

theorem gammaSewnCriticalPrimeDepthPacket_Partition_mul_mean_eq_rawFisherSum
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    gammaSewnCriticalPrimeDepthPacket_Partition e p q * gammaSewnCriticalPrimeDepthPacket_Mean e p q =
      ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalFinitePacket_aperture
          (gammaSewnOrderedPrimeDepthPlucker_rate e p q)
          (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s *
        RHTower.gammaSewnFourRateComplementaryFisher
          (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
  have hP := (gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e) hpq).ne'
  unfold gammaSewnCriticalPrimeDepthPacket_Mean RHTower.complementaryFisherMean
    gammaSewnOrderedPrimeDepthPlucker_probability
    RHTower.gammaSewnFourRateBoundaryPairProbability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  change gammaSewnCriticalPrimeDepthPacket_Partition e p q *
      (RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalFinitePacket_aperture
          (gammaSewnOrderedPrimeDepthPlucker_rate e p q)
          (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s /
        gammaSewnCriticalPrimeDepthPacket_Partition e p q *
          RHTower.gammaSewnFourRateComplementaryFisher
            (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s) = _
  field_simp [hP]

theorem gammaSewnCriticalPrimeDepthPacket_Partition_mul_total_eq_rawTotalSum
    (e : ℕ) (p q : Nat.Primes) :
    gammaSewnCriticalPrimeDepthPacket_Partition e p q * gammaSewnCriticalPrimeDepthPacket_Total e p q =
      ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalFinitePacket_aperture
          (gammaSewnOrderedPrimeDepthPlucker_rate e p q)
          (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s *
        gammaSewnCriticalPrimeDepthPacket_Total e p q := by
  rw [← Finset.sum_mul]
  rfl

def gammaSewnCriticalFinitePacket_Numerator {I : Type*} [Fintype I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes) : ℝ :=
  ∑ i, gammaSewnCriticalPrimeDepthPacket_Partition (depth i) (lower i) (upper i) *
    gammaSewnCriticalPrimeDepthPacket_Mean (depth i) (lower i) (upper i)

def gammaSewnCriticalFinitePacket_Denominator {I : Type*} [Fintype I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes) : ℝ :=
  ∑ i, gammaSewnCriticalPrimeDepthPacket_Partition (depth i) (lower i) (upper i) *
    gammaSewnCriticalPrimeDepthPacket_Total (depth i) (lower i) (upper i)

def gammaSewnCriticalFinitePacket_Fraction {I : Type*} [Fintype I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes) : ℝ :=
  gammaSewnCriticalFinitePacket_Numerator depth lower upper / gammaSewnCriticalFinitePacket_Denominator depth lower upper

theorem gammaSewnCriticalFinitePacket_Denominator_pos {I : Type*} [Fintype I] [Nonempty I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (horder : ∀ i, ((lower i : Nat.Primes) : ℕ) < (upper i : ℕ)) :
    0 < gammaSewnCriticalFinitePacket_Denominator depth lower upper := by
  unfold gammaSewnCriticalFinitePacket_Denominator
  exact Finset.sum_pos (fun i _ => mul_pos (gammaSewnCriticalPrimeDepthPacket_Partition_pos (horder i))
    (gammaSewnCriticalPrimeDepthPacket_Total_pos _ _ _)) Finset.univ_nonempty

theorem gammaSewnCriticalFinitePacket_Numerator_gt_half_denominator
    {I : Type*} [Fintype I] [Nonempty I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (horder : ∀ i, ((lower i : Nat.Primes) : ℕ) < (upper i : ℕ)) :
    (1 / 2 : ℝ) * gammaSewnCriticalFinitePacket_Denominator depth lower upper <
      gammaSewnCriticalFinitePacket_Numerator depth lower upper := by
  unfold gammaSewnCriticalFinitePacket_Denominator gammaSewnCriticalFinitePacket_Numerator
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _hi
  have hP := gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := depth i) (horder i)
  have hM := gammaSewnCriticalPrimeDepthPacket_Mean_gt_half_total (e := depth i) (horder i)
  calc
    (1 / 2 : ℝ) *
        (gammaSewnCriticalPrimeDepthPacket_Partition (depth i) (lower i) (upper i) *
          gammaSewnCriticalPrimeDepthPacket_Total (depth i) (lower i) (upper i)) =
      gammaSewnCriticalPrimeDepthPacket_Partition (depth i) (lower i) (upper i) *
        ((1 / 2 : ℝ) * gammaSewnCriticalPrimeDepthPacket_Total (depth i) (lower i) (upper i)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hM hP

theorem gammaSewnCriticalFinitePacket_Numerator_lt_denominator
    {I : Type*} [Fintype I] [Nonempty I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (horder : ∀ i, ((lower i : Nat.Primes) : ℕ) < (upper i : ℕ)) :
    gammaSewnCriticalFinitePacket_Numerator depth lower upper <
      gammaSewnCriticalFinitePacket_Denominator depth lower upper := by
  unfold gammaSewnCriticalFinitePacket_Denominator gammaSewnCriticalFinitePacket_Numerator
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _hi
  exact mul_lt_mul_of_pos_left (gammaSewnCriticalPrimeDepthPacket_Mean_lt_total (horder i))
    (gammaSewnCriticalPrimeDepthPacket_Partition_pos (horder i))

theorem gammaSewnCriticalFinitePacket_Fraction_mem
    {I : Type*} [Fintype I] [Nonempty I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (horder : ∀ i, ((lower i : Nat.Primes) : ℕ) < (upper i : ℕ)) :
    gammaSewnCriticalFinitePacket_Fraction depth lower upper ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hden := gammaSewnCriticalFinitePacket_Denominator_pos depth lower upper horder
  constructor
  · unfold gammaSewnCriticalFinitePacket_Fraction
    exact (lt_div_iff₀ hden).2
      (gammaSewnCriticalFinitePacket_Numerator_gt_half_denominator depth lower upper horder)
  · unfold gammaSewnCriticalFinitePacket_Fraction
    rw [div_lt_iff₀ hden]
    simpa using gammaSewnCriticalFinitePacket_Numerator_lt_denominator depth lower upper horder

def gammaSewnCriticalFinitePacket_ReducedWeight {I : Type*} [Fintype I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (pk : Nat.Primes × ℕ) : ℝ :=
  (1 - gammaSewnCriticalFinitePacket_Fraction depth lower upper) *
    gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk

theorem gammaSewnCriticalFinitePacket_ReducedWeight_mem
    {I : Type*} [Fintype I] [Nonempty I]
    (depth : I → ℕ) (lower upper : I → Nat.Primes)
    (horder : ∀ i, ((lower i : Nat.Primes) : ℕ) < (upper i : ℕ))
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalFinitePacket_ReducedWeight depth lower upper pk ∈
      Set.Ioo 0 ((1 / 2 : ℝ) *
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) := by
  have hf := gammaSewnCriticalFinitePacket_Fraction_mem depth lower upper horder
  have hw := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk
  constructor
  · unfold gammaSewnCriticalFinitePacket_ReducedWeight
    exact mul_pos (sub_pos.mpr hf.2) hw
  · unfold gammaSewnCriticalFinitePacket_ReducedWeight
    nlinarith [mul_pos (sub_pos.mpr hf.1) hw]

end RHTower.HedenmalmThetaSource
