import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCofinalReducedMomentNoGo

/-!
# Physical diagonal Schur-transfer no-go

P-G89 rejects one uniform cofinal scalar.  The obstruction is stronger.  Every adjacent-prime
physical packet has complementary-Fisher fraction at most `4/5`, hence residual at least `1/5`.
Any nonnegative diagonal transfer that retains this physical residual floor on the leading
prime-two atom already exceeds the completed first moment, even if every other multiplier is an
arbitrary node-dependent function.

Thus no coefficientwise averaging of local physical Schur residuals can solve the compact moment
problem.  A viable Feshbach transfer must be genuinely non-diagonal and move spectral nodes, not
only rescale residues at the bare reciprocal-gap nodes.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalAdjacentPrime_LocalResidual (e n : ℕ) : ℝ :=
  1 - gammaSewnCriticalAdjacentPrime_Mean e n /
    gammaSewnCriticalAdjacentPrime_Total e n

theorem gammaSewnCriticalAdjacentPrime_LocalResidual_mem (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_LocalResidual e n ∈ Set.Ico (1 / 5 : ℝ) (1 / 2) := by
  have htotal := gammaSewnCriticalAdjacentPrime_Total_pos e n
  have hupper := gammaSewnCriticalAdjacentPrime_Mean_le_four_fifths_total e n
  have hlower := gammaSewnCriticalAdjacentPrime_Mean_gt_half_total e n
  have hfracUpper : gammaSewnCriticalAdjacentPrime_Mean e n /
      gammaSewnCriticalAdjacentPrime_Total e n ≤ (4 / 5 : ℝ) := by
    rw [div_le_iff₀ htotal]
    simpa [mul_comm] using hupper
  have hfracLower : (1 / 2 : ℝ) <
      gammaSewnCriticalAdjacentPrime_Mean e n /
        gammaSewnCriticalAdjacentPrime_Total e n := by
    rw [lt_div_iff₀ htotal]
    exact hlower
  unfold gammaSewnCriticalAdjacentPrime_LocalResidual
  constructor <;> linarith

theorem one_fifth_le_finiteAverage_gammaSewnCriticalAdjacentPrime_LocalResidual
    {ι : Type*} [Fintype ι]
    (probability : ι → ℝ) (e n : ι → ℕ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hsum : ∑ i, probability i = 1) :
    (1 / 5 : ℝ) ≤
      ∑ i, probability i * gammaSewnCriticalAdjacentPrime_LocalResidual (e i) (n i) := by
  calc
    (1 / 5 : ℝ) = ∑ i, probability i * (1 / 5 : ℝ) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, probability i *
        gammaSewnCriticalAdjacentPrime_LocalResidual (e i) (n i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (gammaSewnCriticalAdjacentPrime_LocalResidual_mem (e i) (n i)).1
        (hprobability i)

def gammaSewnCriticalPhysicalDiagonalTransferredWeight
    (transfer : Nat.Primes × ℕ → ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  transfer pk * gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk

def GammaSewnCriticalPhysicalDiagonalMomentIdentification
    (transfer : Nat.Primes × ℕ → ℝ) : Prop :=
  ∀ k : ℕ, RHTower.normalizedPrimeArchMoment k =
    ∑' pk : Nat.Primes × ℕ,
      gammaSewnCriticalPhysicalDiagonalTransferredWeight transfer pk *
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
          (1 / 2) pk ^ k

private theorem physicalDiagonalCriticalInformationFactor_two_zero_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo 0
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hu0 : 0 ≤ Real.log 2 / 2 := by positivity
  have hu : Real.log 2 / 2 < 7 / 20 := by linarith
  have hexp : Real.exp (-(Real.log 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul, mul_one] at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤
      4 / 3 * ((Real.log 2 / 2) ^ 3 * Real.exp (-(Real.log 2 / 2))) := h
    _ < 4 / 3 * ((7 / 20 : ℝ) ^ 3 * Real.exp (-(Real.log 2 / 2))) := by gcongr
    _ ≤ 4 / 3 * ((7 / 20 : ℝ) ^ 3 * 1) := by gcongr
    _ < 3 / 10 := by norm_num

theorem gammaSewnCriticalInformationDepletedPrimeTwoDepthZero_firstMoment_lower :
    (51 / 55000 : ℝ) <
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) *
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let pk : Nat.Primes × ℕ :=
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
  let raw := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk
  let depleted := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk
  let node := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hraw : (33 / 1000 : ℝ) < raw := by
    simpa only [raw, pk] using
      gammaSewnCriticalPrimeTwoDepthZero_weight_gt_thirtyThree_thousandths
  have hk := physicalDiagonalCriticalInformationFactor_two_zero_lt
  have href : 0 < RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk :=
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos (by norm_num) pk
  have hdepRaw : (17 / 20 : ℝ) * raw < depleted := by
    dsimp only [depleted, raw]
    rw [gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
    simpa only [pk] using
      (show (17 / 20 : ℝ) *
          (2 * RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk) <
        (2 - gammaSewnMobiusApertureStokesCriticalInformationFactor pk) *
          RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk by
        nlinarith [mul_pos (sub_pos.mpr hk) href])
  have hdep : (561 / 20000 : ℝ) < depleted := by nlinarith
  have hnode : (4 / 121 : ℝ) < node := by
    simpa only [node, pk] using
      gammaSewnCriticalPrimeTwoDepthZero_node_gt_four_over_oneTwentyOne
  have hprod : (561 / 20000 : ℝ) * (4 / 121 : ℝ) < depleted * node :=
    (mul_lt_mul_of_pos_right hdep (by norm_num)).trans
      (mul_lt_mul_of_pos_left hnode (lt_trans (by norm_num) hdep))
  have hprod' : (51 / 55000 : ℝ) < depleted * node := by
    norm_num at hprod ⊢
    exact hprod
  simpa only [depleted, node, pk] using hprod'

theorem gammaSewnCriticalPhysicalDiagonalPrimeTwoDepthZero_firstMoment_lower
    {transfer : Nat.Primes × ℕ → ℝ}
    (hfloor : (1 / 5 : ℝ) ≤
      transfer (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)) :
    (9 / 50000 : ℝ) <
      gammaSewnCriticalPhysicalDiagonalTransferredWeight transfer
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) *
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let pk : Nat.Primes × ℕ :=
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
  let base := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk *
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hbase : (51 / 55000 : ℝ) < base := by
    simpa only [base, pk] using
      gammaSewnCriticalInformationDepletedPrimeTwoDepthZero_firstMoment_lower
  have hpositive : 0 < base := (by norm_num : (0 : ℝ) < 51 / 55000).trans hbase
  have hscaled : (51 / 275000 : ℝ) < transfer pk * base := by
    calc
      (51 / 275000 : ℝ) = (1 / 5 : ℝ) * (51 / 55000 : ℝ) := by norm_num
      _ < (1 / 5 : ℝ) * base := mul_lt_mul_of_pos_left hbase (by norm_num)
      _ ≤ transfer pk * base := mul_le_mul_of_nonneg_right (by simpa only [pk] using hfloor)
        hpositive.le
  have hnumeric : (9 / 50000 : ℝ) < 51 / 275000 := by norm_num
  unfold gammaSewnCriticalPhysicalDiagonalTransferredWeight
  rw [show transfer pk *
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk *
        RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk =
      transfer pk * base by ring]
  simpa only [pk] using hnumeric.trans hscaled

/-- **P-G90 diagonal no-go.** Arbitrary node dependence does not help if physical packet
residuals are transferred coefficientwise: their forced `1/5` floor on the leading atom already
violates completed first moment. -/
theorem not_gammaSewnCriticalPhysicalDiagonalMomentIdentification
    {transfer : Nat.Primes × ℕ → ℝ}
    (htransfer : ∀ pk, 0 ≤ transfer pk)
    (hsummable : Summable
      (gammaSewnCriticalPhysicalDiagonalTransferredWeight transfer))
    (hfloor : (1 / 5 : ℝ) ≤
      transfer (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)) :
    ¬ GammaSewnCriticalPhysicalDiagonalMomentIdentification transfer := by
  intro hidentification
  let f := fun pk : Nat.Primes × ℕ =>
    gammaSewnCriticalPhysicalDiagonalTransferredWeight transfer pk *
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk
  have hfnonneg : ∀ pk, 0 ≤ f pk := fun pk => mul_nonneg
    (mul_nonneg (htransfer pk)
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le)
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) pk).le
  have hfsum : Summable f := by
    refine Summable.of_nonneg_of_le hfnonneg (fun pk => ?_)
      (hsummable.mul_left (((Real.log 2)⁻¹) ^ 2))
    have hw : 0 ≤ gammaSewnCriticalPhysicalDiagonalTransferredWeight transfer pk :=
      mul_nonneg (htransfer pk)
        (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le
    have hn := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) pk
    dsimp only [f]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hn hw
  have hselected :
      f (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤ ∑' pk, f pk := by
    have hle := hfsum.sum_le_tsum
      ({(RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)} :
        Finset (Nat.Primes × ℕ))
      (fun pk _ => hfnonneg pk)
    simpa only [Finset.sum_singleton] using hle
  have hsource := hidentification 1
  simp only [pow_one] at hsource
  have hexcess :=
    gammaSewnCriticalPhysicalDiagonalPrimeTwoDepthZero_firstMoment_lower hfloor
  have hcompleted := RHTower.normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  rw [hsource] at hcompleted
  have htooLarge : (9 / 50000 : ℝ) < ∑' pk, f pk :=
    hexcess.trans_le hselected
  exact (not_lt_of_ge (le_of_lt htooLarge)) hcompleted

end RHTower.HedenmalmThetaSource
