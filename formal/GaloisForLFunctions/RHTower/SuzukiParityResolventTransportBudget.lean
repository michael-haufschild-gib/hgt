import GaloisForLFunctions.RHTower.SuzukiInteriorExcursionShiftSelection
import GaloisForLFunctions.RHTower.SuzukiShiftSpectralMonotoneRatio
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Suzuki parity-resolvent transport budget

The surviving interior-excursion selector needs the even/odd resolvent ratio to grow from its
free value to the Xi threshold.  This module identifies the exact accumulated quantity that must
pay for that growth.

For positive parity energies `E,O`, define log odds `log(E/O)`.  Its shift derivative is the
hazard gap

`E'/E - O'/O`.

For actual spectral resolvent energies, `E'` and `O'` are squared-resolvent matrix elements, so
the hazard gap is the difference of the two resolvent-tilted inverse-gap means.  The fundamental
theorem of calculus makes its interval integral exactly the log-odds gain.

An interior value above the unconditional Xi first defect forces `E > (81/4) O`.  Consequently
every such excursion must spend a strict integrated hazard budget

`∫ (E'/E-O'/O) > log(81/4) - log(E₁/O₁)`.

No monotone-likelihood assumption, Riemann-hypothesis assumption, or numerical computation occurs.
-/

open Set

namespace RHTower

noncomputable section

/-- Logarithmic even/odd odds of a positive Suzuki parity-resolvent path. -/
def suzukiParityResolventLogOdds
    (evenEnergy oddEnergy : ℝ → ℝ) (lambda : ℝ) : ℝ :=
  Real.log (evenEnergy lambda / oddEnergy lambda)

/-- Difference of the normalized even and odd squared-resolvent responses. -/
def suzukiParityResolventHazardGap
    (evenEnergy oddEnergy evenVelocity oddVelocity : ℝ → ℝ)
    (lambda : ℝ) : ℝ :=
  evenVelocity lambda / evenEnergy lambda -
    oddVelocity lambda / oddEnergy lambda

/-! ## Differential and integrated transport identities -/

/-- The parity-resolvent hazard gap is exactly the derivative of log odds. -/
theorem hasDerivAt_suzukiParityResolventLogOdds
    {evenEnergy oddEnergy : ℝ → ℝ}
    {evenVelocity oddVelocity lambda : ℝ}
    (hevenDeriv : HasDerivAt evenEnergy evenVelocity lambda)
    (hoddDeriv : HasDerivAt oddEnergy oddVelocity lambda)
    (heven : 0 < evenEnergy lambda)
    (hodd : 0 < oddEnergy lambda) :
    HasDerivAt
      (suzukiParityResolventLogOdds evenEnergy oddEnergy)
      (evenVelocity / evenEnergy lambda - oddVelocity / oddEnergy lambda)
      lambda := by
  have hratio :=
    (hevenDeriv.div hoddDeriv hodd.ne').log
      (div_ne_zero heven.ne' hodd.ne')
  simp only [Pi.div_apply] at hratio
  convert hratio using 1 <;> try rfl
  field_simp [heven.ne', hodd.ne']

/-- Exact finite-shift transport: integrated parity hazard equals the log-odds gain. -/
theorem intervalIntegral_suzukiParityResolventHazardGap
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ → ℝ}
    {lambda₁ lambda₂ : ℝ}
    (hevenDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt evenEnergy (evenVelocity lambda) lambda)
    (hoddDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt oddEnergy (oddVelocity lambda) lambda)
    (heven : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < evenEnergy lambda)
    (hodd : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < oddEnergy lambda)
    (hint : IntervalIntegrable
      (suzukiParityResolventHazardGap
        evenEnergy oddEnergy evenVelocity oddVelocity)
      MeasureTheory.volume lambda₁ lambda₂) :
    (∫ lambda in lambda₁..lambda₂,
        suzukiParityResolventHazardGap
          evenEnergy oddEnergy evenVelocity oddVelocity lambda) =
      suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₂ -
        suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₁ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro lambda hlambda
    exact hasDerivAt_suzukiParityResolventLogOdds
      (hevenDeriv lambda hlambda) (hoddDeriv lambda hlambda)
      (heven lambda hlambda) (hodd lambda hlambda)
  · exact hint

/-! ## Unconditional Xi transport cost -/

/-- Exact even/odd energy ratio required to exceed Xi's first defect. -/
def primeArchSuzukiParityEvenOddThreshold : ℝ :=
  (1 + primeArchSuzukiFirstDefectCalibration) /
    (1 - primeArchSuzukiFirstDefectCalibration)

/-- The exact Xi even/odd threshold is strictly larger than `81/4`. -/
theorem primeArchSuzukiParityEvenOddThreshold_gt_eightyOne_div_four :
    (81 : ℝ) / 4 < primeArchSuzukiParityEvenOddThreshold := by
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo
  have hden : 0 < 1 - primeArchSuzukiFirstDefectCalibration :=
    sub_pos.mpr hk.2
  rw [primeArchSuzukiParityEvenOddThreshold, lt_div_iff₀ hden]
  nlinarith [hk.1]

/-- Exact ratio form of a strict finite-shift Xi excursion. -/
theorem primeArchSuzukiParityEnergy_angle_gt_iff_evenOddRatio
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    primeArchSuzukiFirstDefectCalibration <
          GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy ↔
      primeArchSuzukiParityEvenOddThreshold < evenEnergy / oddEnergy := by
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hden : 0 < 1 - primeArchSuzukiFirstDefectCalibration :=
    sub_pos.mpr primeArchSuzukiFirstDefectCalibration_mem_Ioo.2
  rw [GaloisForLFunctions.RHTower.suzukiDefectAngle, lt_div_iff₀ hsum]
  rw [primeArchSuzukiParityEvenOddThreshold, div_lt_div_iff₀ hden hodd]
  constructor <;> intro h <;> nlinarith

/-- Exact logarithmic form of a strict finite-shift Xi excursion. -/
theorem primeArchSuzukiParityEnergy_angle_gt_iff_logOdds
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    primeArchSuzukiFirstDefectCalibration <
          GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy ↔
      Real.log primeArchSuzukiParityEvenOddThreshold <
        Real.log (evenEnergy / oddEnergy) := by
  rw [primeArchSuzukiParityEnergy_angle_gt_iff_evenOddRatio heven hodd]
  have hthreshold : 0 < primeArchSuzukiParityEvenOddThreshold := by
    have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo
    exact div_pos (by linarith [hk.1]) (by linarith [hk.2])
  exact (Real.log_lt_log_iff hthreshold (div_pos heven hodd)).symm

/-- Any finite parity-energy point above Xi's first defect has even/odd ratio greater than
`81/4`. -/
theorem primeArchSuzukiParityEnergy_even_gt_eightyOne_div_four_mul_odd
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 ≤ evenEnergy) (hodd : 0 ≤ oddEnergy)
    (hover :
      primeArchSuzukiFirstDefectCalibration <
        GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy) :
    ((81 : ℝ) / 4) * oddEnergy < evenEnergy := by
  have hsum : 0 < evenEnergy + oddEnergy := by
    by_contra h
    have hz : evenEnergy = 0 ∧ oddEnergy = 0 := by
      constructor <;> nlinarith
    simp [hz.1, hz.2, GaloisForLFunctions.RHTower.suzukiDefectAngle] at hover
    have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
    nlinarith
  have hadmitted :=
    (target_lt_suzukiGroundResidueAngle_iff
      (target := primeArchSuzukiFirstDefectCalibration) hsum).mp
      (by simpa [suzukiGroundResidueAngle] using hover)
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
  nlinarith

/-- Logarithmic form of the unconditional `81/4` parity amplification. -/
theorem primeArchSuzukiParityEnergy_logOdds_gt_log_eightyOne_div_four
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 ≤ evenEnergy) (hodd : 0 < oddEnergy)
    (hover :
      primeArchSuzukiFirstDefectCalibration <
        GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy) :
    Real.log ((81 : ℝ) / 4) <
      Real.log (evenEnergy / oddEnergy) := by
  have hmass :=
    primeArchSuzukiParityEnergy_even_gt_eightyOne_div_four_mul_odd
      heven hodd.le hover
  have hc : (0 : ℝ) < 81 / 4 := by norm_num
  have hevenPos : 0 < evenEnergy := lt_of_lt_of_le (mul_pos hc hodd) hmass.le
  have hlog :
      Real.log (((81 : ℝ) / 4) * oddEnergy) < Real.log evenEnergy :=
    (Real.log_lt_log_iff (mul_pos hc hodd) hevenPos).mpr hmass
  rw [Real.log_mul (by norm_num) hodd.ne'] at hlog
  rw [Real.log_div hevenPos.ne' hodd.ne']
  linarith

/-- **Exact interior-excursion transport budget.**  An endpoint lies above Xi's first defect
exactly when accumulated parity hazard exceeds the exact Xi log-odds cost. -/
theorem primeArchSuzukiInteriorExcursion_iff_hazardBudget
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ → ℝ}
    {lambda₁ lambda₂ : ℝ}
    (hevenDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt evenEnergy (evenVelocity lambda) lambda)
    (hoddDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt oddEnergy (oddVelocity lambda) lambda)
    (heven : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < evenEnergy lambda)
    (hodd : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < oddEnergy lambda)
    (hint : IntervalIntegrable
      (suzukiParityResolventHazardGap
        evenEnergy oddEnergy evenVelocity oddVelocity)
      MeasureTheory.volume lambda₁ lambda₂) :
    primeArchSuzukiFirstDefectCalibration <
          GaloisForLFunctions.RHTower.suzukiDefectAngle
            (evenEnergy lambda₂) (oddEnergy lambda₂) ↔
      Real.log primeArchSuzukiParityEvenOddThreshold -
            suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₁ <
        ∫ lambda in lambda₁..lambda₂,
          suzukiParityResolventHazardGap
            evenEnergy oddEnergy evenVelocity oddVelocity lambda := by
  have hlambda₂ : lambda₂ ∈ uIcc lambda₁ lambda₂ := right_mem_uIcc
  rw [primeArchSuzukiParityEnergy_angle_gt_iff_logOdds
    (heven lambda₂ hlambda₂) (hodd lambda₂ hlambda₂)]
  rw [intervalIntegral_suzukiParityResolventHazardGap
    hevenDeriv hoddDeriv heven hodd hint]
  change
    Real.log primeArchSuzukiParityEvenOddThreshold <
          suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₂ ↔
      Real.log primeArchSuzukiParityEvenOddThreshold -
            suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₁ <
        suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₂ -
          suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₁
  constructor <;> intro h <;> linarith

/-- **Interior-excursion transport budget.**  Any endpoint above Xi's first defect forces the
integrated even-over-odd resolvent hazard to exceed the displayed sharp log-odds cost. -/
theorem primeArchSuzukiInteriorExcursion_hazardBudget
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ → ℝ}
    {lambda₁ lambda₂ : ℝ}
    (hevenDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt evenEnergy (evenVelocity lambda) lambda)
    (hoddDeriv : ∀ lambda ∈ uIcc lambda₁ lambda₂,
      HasDerivAt oddEnergy (oddVelocity lambda) lambda)
    (heven : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < evenEnergy lambda)
    (hodd : ∀ lambda ∈ uIcc lambda₁ lambda₂, 0 < oddEnergy lambda)
    (hint : IntervalIntegrable
      (suzukiParityResolventHazardGap
        evenEnergy oddEnergy evenVelocity oddVelocity)
      MeasureTheory.volume lambda₁ lambda₂)
    (hover :
      primeArchSuzukiFirstDefectCalibration <
        GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy lambda₂) (oddEnergy lambda₂)) :
    Real.log ((81 : ℝ) / 4) -
          suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₁ <
      ∫ lambda in lambda₁..lambda₂,
        suzukiParityResolventHazardGap
          evenEnergy oddEnergy evenVelocity oddVelocity lambda := by
  have hlambda₂ : lambda₂ ∈ uIcc lambda₁ lambda₂ := right_mem_uIcc
  have hlog :=
    primeArchSuzukiParityEnergy_logOdds_gt_log_eightyOne_div_four
      (heven lambda₂ hlambda₂).le (hodd lambda₂ hlambda₂) hover
  change Real.log ((81 : ℝ) / 4) <
    suzukiParityResolventLogOdds evenEnergy oddEnergy lambda₂ at hlog
  rw [intervalIntegral_suzukiParityResolventHazardGap
    hevenDeriv hoddDeriv heven hodd hint]
  linarith

/-! ## Exact finite cross-parity spectral carrier -/

variable {ι κ : Type*}

/-- Finite source spectral energy at shift `lambda`. -/
def suzukiFiniteParityResolventEnergy
    (indices : Finset ι) (node weight : ι → ℝ) (lambda : ℝ) : ℝ :=
  ∑ i ∈ indices, weight i * suzukiShiftResolventKernel node lambda i

/-- Squared-resolvent velocity of a finite source spectral energy. -/
def suzukiFiniteParitySquaredResolventEnergy
    (indices : Finset ι) (node weight : ι → ℝ) (lambda : ℝ) : ℝ :=
  ∑ i ∈ indices, weight i * suzukiShiftResolventKernel node lambda i ^ 2

/-- Signed cross-parity spectral-gap mass. Every even--odd pair is weighted by its source masses
and the squared resolvent denominator; its sign is the sign of `oddNode j - evenNode i`. -/
def suzukiFiniteParityCrossGapMass
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) : ℝ :=
  ∑ i ∈ evenIndices, ∑ j ∈ oddIndices,
    evenWeight i * oddWeight j * (oddNode j - evenNode i) /
      ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2)

/-- Signed cross-parity gap mass normalized by the two parity resolvent energies. -/
def suzukiFiniteParityNormalizedCrossGapMass
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) : ℝ :=
  suzukiFiniteParityCrossGapMass
      evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda /
    (suzukiFiniteParityResolventEnergy
        evenIndices evenNode evenWeight lambda *
      suzukiFiniteParityResolventEnergy
        oddIndices oddNode oddWeight lambda)

/-- A finite source spectral energy differentiates to its squared-resolvent energy. -/
theorem hasDerivAt_suzukiFiniteParityResolventEnergy
    (indices : Finset ι) (node weight : ι → ℝ) (lambda : ℝ)
    (hnode : ∀ i ∈ indices, node i - lambda ≠ 0) :
    HasDerivAt
      (fun l => suzukiFiniteParityResolventEnergy indices node weight l)
      (suzukiFiniteParitySquaredResolventEnergy indices node weight lambda)
      lambda := by
  simp only [suzukiFiniteParityResolventEnergy,
    suzukiFiniteParitySquaredResolventEnergy]
  let F : ℝ → ℝ :=
    ∑ i ∈ indices, fun l =>
      weight i * suzukiShiftResolventKernel node l i
  have hF :
      F = fun l =>
        ∑ i ∈ indices, weight i * suzukiShiftResolventKernel node l i := by
    funext l
    simp [F]
  rw [← hF]
  exact HasDerivAt.sum fun i hi =>
    (hasDerivAt_suzukiShiftResolventKernel (hnode i hi)).const_mul (weight i)

/-- **Finite cross-parity Wronskian law.** The numerator of the parity hazard is exactly the
weighted signed sum of every odd--even spectral gap. -/
theorem suzukiFiniteParityResolvent_crossWronskian_eq_pairSum
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) :
    suzukiFiniteParitySquaredResolventEnergy
          evenIndices evenNode evenWeight lambda *
        suzukiFiniteParityResolventEnergy
          oddIndices oddNode oddWeight lambda -
      suzukiFiniteParityResolventEnergy
          evenIndices evenNode evenWeight lambda *
        suzukiFiniteParitySquaredResolventEnergy
          oddIndices oddNode oddWeight lambda =
      suzukiFiniteParityCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  simp only [suzukiFiniteParityResolventEnergy,
    suzukiFiniteParitySquaredResolventEnergy,
    suzukiFiniteParityCrossGapMass]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [suzukiShiftResolventKernel]
  field_simp
  ring

/-- The finite parity hazard is the cross-gap sum divided by the product of parity energies. -/
theorem suzukiFiniteParityResolvent_hazardGap_eq_pairSum_div
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ)
    (heven : suzukiFiniteParityResolventEnergy
      evenIndices evenNode evenWeight lambda ≠ 0)
    (hodd : suzukiFiniteParityResolventEnergy
      oddIndices oddNode oddWeight lambda ≠ 0) :
    suzukiParityResolventHazardGap
        (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
        (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
        (suzukiFiniteParitySquaredResolventEnergy evenIndices evenNode evenWeight)
        (suzukiFiniteParitySquaredResolventEnergy oddIndices oddNode oddWeight)
        lambda =
      suzukiFiniteParityCrossGapMass
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda /
        (suzukiFiniteParityResolventEnergy
            evenIndices evenNode evenWeight lambda *
          suzukiFiniteParityResolventEnergy
            oddIndices oddNode oddWeight lambda) := by
  rw [suzukiParityResolventHazardGap]
  have hcross :=
    suzukiFiniteParityResolvent_crossWronskian_eq_pairSum
      evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda
  field_simp [heven, hodd]
  linear_combination hcross

/-- Definition-packaged form of the exact normalized cross-gap identity. -/
theorem suzukiFiniteParityResolvent_hazardGap_eq_normalizedCrossGapMass
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ)
    (heven : suzukiFiniteParityResolventEnergy
      evenIndices evenNode evenWeight lambda ≠ 0)
    (hodd : suzukiFiniteParityResolventEnergy
      oddIndices oddNode oddWeight lambda ≠ 0) :
    suzukiParityResolventHazardGap
        (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
        (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
        (suzukiFiniteParitySquaredResolventEnergy evenIndices evenNode evenWeight)
        (suzukiFiniteParitySquaredResolventEnergy oddIndices oddNode oddWeight)
        lambda =
      suzukiFiniteParityNormalizedCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  exact suzukiFiniteParityResolvent_hazardGap_eq_pairSum_div
    evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda heven hodd

/-- For positive parity energies, positive hazard is equivalent—not merely implied by—positive
signed cross-parity gap mass. -/
theorem suzukiFiniteParityResolvent_hazardGap_pos_iff_pairSum_pos
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ)
    (heven : 0 < suzukiFiniteParityResolventEnergy
      evenIndices evenNode evenWeight lambda)
    (hodd : 0 < suzukiFiniteParityResolventEnergy
      oddIndices oddNode oddWeight lambda) :
    0 <
        suzukiParityResolventHazardGap
          (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
          (suzukiFiniteParitySquaredResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParitySquaredResolventEnergy oddIndices oddNode oddWeight)
          lambda ↔
      0 < suzukiFiniteParityCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  rw [suzukiFiniteParityResolvent_hazardGap_eq_pairSum_div
    evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda
    heven.ne' hodd.ne']
  constructor
  · intro h
    rcases (div_pos_iff.mp h) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (mul_pos heven hodd).le) hneg.2)
  · intro h
    exact div_pos h (mul_pos heven hodd)

/-- The integrated normalized signed cross-gap mass is exactly the finite spectral log-odds gain. -/
theorem intervalIntegral_suzukiFiniteParityNormalizedCrossGapMass
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda₁ lambda₂ : ℝ)
    (hevenNode : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      ∀ i ∈ evenIndices, evenNode i - lambda ≠ 0)
    (hoddNode : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      ∀ j ∈ oddIndices, oddNode j - lambda ≠ 0)
    (heven : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      0 < suzukiFiniteParityResolventEnergy
        evenIndices evenNode evenWeight lambda)
    (hodd : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      0 < suzukiFiniteParityResolventEnergy
        oddIndices oddNode oddWeight lambda)
    (hint : IntervalIntegrable
      (suzukiFiniteParityNormalizedCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight)
      MeasureTheory.volume lambda₁ lambda₂) :
    (∫ lambda in lambda₁..lambda₂,
        suzukiFiniteParityNormalizedCrossGapMass
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda) =
      suzukiParityResolventLogOdds
          (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
          lambda₂ -
        suzukiParityResolventLogOdds
          (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
          lambda₁ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro lambda hlambda
    have hderiv :=
      hasDerivAt_suzukiParityResolventLogOdds
        (hasDerivAt_suzukiFiniteParityResolventEnergy
          evenIndices evenNode evenWeight lambda (hevenNode lambda hlambda))
        (hasDerivAt_suzukiFiniteParityResolventEnergy
          oddIndices oddNode oddWeight lambda (hoddNode lambda hlambda))
        (heven lambda hlambda) (hodd lambda hlambda)
    have hgap :=
      suzukiFiniteParityResolvent_hazardGap_eq_normalizedCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda
        (heven lambda hlambda).ne' (hodd lambda hlambda).ne'
    change
      suzukiFiniteParitySquaredResolventEnergy
            evenIndices evenNode evenWeight lambda /
          suzukiFiniteParityResolventEnergy
            evenIndices evenNode evenWeight lambda -
        suzukiFiniteParitySquaredResolventEnergy
            oddIndices oddNode oddWeight lambda /
          suzukiFiniteParityResolventEnergy
            oddIndices oddNode oddWeight lambda =
        suzukiFiniteParityNormalizedCrossGapMass
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda at hgap
    rw [hgap] at hderiv
    exact hderiv
  · exact hint

/-- **Exact finite Suzuki spectral carrier.** A finite parity-resolvent endpoint crosses the Xi
first-defect threshold exactly when the integrated normalized signed cross-parity gap mass pays
the calibrated Xi log-odds cost. -/
theorem primeArchSuzukiFiniteParityInteriorExcursion_iff_crossGapBudget
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda₁ lambda₂ : ℝ)
    (hevenNode : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      ∀ i ∈ evenIndices, evenNode i - lambda ≠ 0)
    (hoddNode : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      ∀ j ∈ oddIndices, oddNode j - lambda ≠ 0)
    (heven : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      0 < suzukiFiniteParityResolventEnergy
        evenIndices evenNode evenWeight lambda)
    (hodd : ∀ lambda ∈ Set.uIcc lambda₁ lambda₂,
      0 < suzukiFiniteParityResolventEnergy
        oddIndices oddNode oddWeight lambda)
    (hint : IntervalIntegrable
      (suzukiFiniteParityNormalizedCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight)
      MeasureTheory.volume lambda₁ lambda₂) :
    primeArchSuzukiFirstDefectCalibration <
          GaloisForLFunctions.RHTower.suzukiDefectAngle
            (suzukiFiniteParityResolventEnergy
              evenIndices evenNode evenWeight lambda₂)
            (suzukiFiniteParityResolventEnergy
              oddIndices oddNode oddWeight lambda₂) ↔
      Real.log primeArchSuzukiParityEvenOddThreshold -
            suzukiParityResolventLogOdds
              (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
              (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
              lambda₁ <
        ∫ lambda in lambda₁..lambda₂,
          suzukiFiniteParityNormalizedCrossGapMass
            evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  have hlambda₂ : lambda₂ ∈ Set.uIcc lambda₁ lambda₂ := Set.right_mem_uIcc
  rw [primeArchSuzukiParityEnergy_angle_gt_iff_logOdds
    (heven lambda₂ hlambda₂) (hodd lambda₂ hlambda₂)]
  rw [intervalIntegral_suzukiFiniteParityNormalizedCrossGapMass
    evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda₁ lambda₂
    hevenNode hoddNode heven hodd hint]
  change
    Real.log primeArchSuzukiParityEvenOddThreshold <
          suzukiParityResolventLogOdds
            (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
            (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
            lambda₂ ↔
      Real.log primeArchSuzukiParityEvenOddThreshold -
            suzukiParityResolventLogOdds
              (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
              (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
              lambda₁ <
        suzukiParityResolventLogOdds
              (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
              (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
              lambda₂ -
          suzukiParityResolventLogOdds
              (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
              (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
              lambda₁
  constructor <;> intro h <;> linarith

/-! ## Lower-pair credit versus spectral-inversion debt -/

/-- Positive contribution from pairs in which the even node lies below the odd node. -/
def suzukiFiniteParityLowerPairCredit
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) : ℝ :=
  ∑ i ∈ evenIndices, ∑ j ∈ oddIndices,
    evenWeight i * oddWeight j * (oddNode j - evenNode i)⁺ /
      ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2)

/-- Negative contribution from spectral inversions in which an odd node lies below an even node. -/
def suzukiFiniteParitySpectralInversionDebt
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) : ℝ :=
  ∑ i ∈ evenIndices, ∑ j ∈ oddIndices,
    evenWeight i * oddWeight j * (oddNode j - evenNode i)⁻ /
      ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2)

/-- The signed cross-parity mass is exactly lower-pair credit minus spectral-inversion debt. -/
theorem suzukiFiniteParityCrossGapMass_eq_credit_sub_inversionDebt
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ) :
    suzukiFiniteParityCrossGapMass
        evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda =
      suzukiFiniteParityLowerPairCredit
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda -
        suzukiFiniteParitySpectralInversionDebt
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  simp only [suzukiFiniteParityCrossGapMass,
    suzukiFiniteParityLowerPairCredit,
    suzukiFiniteParitySpectralInversionDebt, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    evenWeight i * oddWeight j * (oddNode j - evenNode i) /
          ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2) =
        evenWeight i * oddWeight j *
            ((oddNode j - evenNode i)⁺ - (oddNode j - evenNode i)⁻) /
          ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2) := by
            rw [posPart_sub_negPart]
    _ = evenWeight i * oddWeight j * (oddNode j - evenNode i)⁺ /
          ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2) -
        evenWeight i * oddWeight j * (oddNode j - evenNode i)⁻ /
          ((evenNode i - lambda) ^ 2 * (oddNode j - lambda) ^ 2) := by ring

/-- With positive parity energies, positive transport occurs exactly when lower-pair credit beats
the complete weighted debt from locally reversed odd/even spectral pairs. -/
theorem suzukiFiniteParityResolvent_hazardGap_pos_iff_inversionDebt_lt_credit
    (evenIndices : Finset ι) (oddIndices : Finset κ)
    (evenNode evenWeight : ι → ℝ) (oddNode oddWeight : κ → ℝ)
    (lambda : ℝ)
    (heven : 0 < suzukiFiniteParityResolventEnergy
      evenIndices evenNode evenWeight lambda)
    (hodd : 0 < suzukiFiniteParityResolventEnergy
      oddIndices oddNode oddWeight lambda) :
    0 <
        suzukiParityResolventHazardGap
          (suzukiFiniteParityResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParityResolventEnergy oddIndices oddNode oddWeight)
          (suzukiFiniteParitySquaredResolventEnergy evenIndices evenNode evenWeight)
          (suzukiFiniteParitySquaredResolventEnergy oddIndices oddNode oddWeight)
          lambda ↔
      suzukiFiniteParitySpectralInversionDebt
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda <
        suzukiFiniteParityLowerPairCredit
          evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda := by
  rw [suzukiFiniteParityResolvent_hazardGap_pos_iff_pairSum_pos
    evenIndices oddIndices evenNode evenWeight oddNode oddWeight lambda heven hodd]
  rw [suzukiFiniteParityCrossGapMass_eq_credit_sub_inversionDebt]
  exact sub_pos

/-! ## Global parity monotone-likelihood no-go -/

/-- Global comonotone-likelihood order for the two-valued parity response: every visible odd node
must lie below every visible even node. -/
def SuzukiParitySpectraComonotone
    {ι κ : Type*} (evenNode : ι → ℝ) (oddNode : κ → ℝ) : Prop :=
  ∀ i j, oddNode j ≤ evenNode i

/-- The opposite global likelihood orientation: every visible even node must lie below every
visible odd node. -/
def SuzukiParitySpectraAntimonotone
    {ι κ : Type*} (evenNode : ι → ℝ) (oddNode : κ → ℝ) : Prop :=
  ∀ i j, evenNode i ≤ oddNode j

/-- An unbounded-above visible odd spectrum rules out global comonotone parity likelihood as soon
as one visible even node exists. -/
theorem not_suzukiParitySpectraComonotone_of_odd_unbounded
    {ι κ : Type*} [Nonempty ι]
    {evenNode : ι → ℝ} {oddNode : κ → ℝ}
    (hodd : ∀ bound : ℝ, ∃ j, bound < oddNode j) :
    ¬ SuzukiParitySpectraComonotone evenNode oddNode := by
  intro hmono
  let i : ι := Classical.choice inferInstance
  obtain ⟨j, hj⟩ := hodd (evenNode i)
  exact (not_lt_of_ge (hmono i j)) hj

/-- An unbounded-above visible even spectrum rules out the opposite global likelihood orientation
as soon as one visible odd node exists. -/
theorem not_suzukiParitySpectraAntimonotone_of_even_unbounded
    {ι κ : Type*} [Nonempty κ]
    {evenNode : ι → ℝ} {oddNode : κ → ℝ}
    (heven : ∀ bound : ℝ, ∃ i, bound < evenNode i) :
    ¬ SuzukiParitySpectraAntimonotone evenNode oddNode := by
  intro hmono
  let j : κ := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := heven (oddNode j)
  exact (not_lt_of_ge (hmono i j)) hi

/-- **Bi-unbounded parity-likelihood no-go.**  When both source-visible parity spectra are
unbounded above, neither global two-valued monotone-likelihood orientation is possible. -/
theorem no_global_suzukiParitySpectralMonotoneLikelihood_of_biunbounded
    {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    {evenNode : ι → ℝ} {oddNode : κ → ℝ}
    (heven : ∀ bound : ℝ, ∃ i, bound < evenNode i)
    (hodd : ∀ bound : ℝ, ∃ j, bound < oddNode j) :
    ¬ SuzukiParitySpectraComonotone evenNode oddNode ∧
      ¬ SuzukiParitySpectraAntimonotone evenNode oddNode :=
  ⟨not_suzukiParitySpectraComonotone_of_odd_unbounded hodd,
    not_suzukiParitySpectraAntimonotone_of_even_unbounded heven⟩

end

end RHTower
