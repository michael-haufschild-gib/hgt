import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsShallowCharge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsDeepBand
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount

/-!
# Canonical seven-tenths HCF divisor packets

This module welds Route T's analytic-multiplicity zero density to the actual multiplicity-copy Xi
carrier consumed by HCF.  Positive-ordinate supports are split into strict-right shallow and deep
packets.  The deep packet cardinality is bounded by the literal Littlewood zero count and is
therefore `o(N)`.  Every shallow copy has centered transverse displacement at most `1/5` and so is
admissible for the improved `23/25` HCF sector theorem.

The construction is divisor-side bookkeeping only.  It does not provide the remaining source-only
upper bound for the corrected HCF lattice budget.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Positive-height Xi supports strictly right of the critical line but below `Re rho = 7/10`. -/
def criticalFeatureCanonicalShallowRightSupportPacket (n : ℕ) :
    Finset XiDivisorSupport :=
  (xiSupportsPos (n : ℝ)).filter fun rho =>
    1 / 2 < (rho : ℂ).re ∧ (rho : ℂ).re < 7 / 10

/-- Positive-height Xi supports in the Route-T deep band `Re rho ≥ 7/10`. -/
def criticalFeatureCanonicalDeepRightSupportPacket (n : ℕ) :
    Finset XiDivisorSupport :=
  (xiSupportsPos (n : ℝ)).filter fun rho => 7 / 10 ≤ (rho : ℂ).re

/-- Multiplicity copies of the canonical strict-right shallow support packet. -/
def criticalFeatureCanonicalShallowRightCopyPacket (n : ℕ) : Finset XiZeroCopy :=
  (criticalFeatureCanonicalShallowRightSupportPacket n).biUnion xiZeroCopyFiber

/-- Multiplicity copies of the canonical strict-right deep support packet. -/
def criticalFeatureCanonicalDeepRightCopyPacket (n : ℕ) : Finset XiZeroCopy :=
  (criticalFeatureCanonicalDeepRightSupportPacket n).biUnion xiZeroCopyFiber

/-- Generic cardinality regrouping for a finite Xi support packet and all its multiplicity copies. -/
theorem card_biUnion_xiZeroCopyFiber (S : Finset XiDivisorSupport) :
    (S.biUnion xiZeroCopyFiber).card = ∑ rho ∈ S, xiSupportMultiplicity rho := by
  classical
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro rho hrho
    exact card_xiZeroCopyFiber rho
  · intro rho hrho tau htau hne
    exact Finset.disjoint_left.mpr fun q hqrho hqtau =>
      hne ((mem_xiZeroCopyFiber.mp hqrho).symm.trans
        (mem_xiZeroCopyFiber.mp hqtau))

theorem mem_criticalFeatureCanonicalShallowRightCopyPacket
    {n : ℕ} {q : XiZeroCopy} :
    q ∈ criticalFeatureCanonicalShallowRightCopyPacket n ↔
      |(q.1 : ℂ).im| ≤ n ∧ 0 < (q.1 : ℂ).im ∧
        1 / 2 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 7 / 10 := by
  classical
  rw [criticalFeatureCanonicalShallowRightCopyPacket, Finset.mem_biUnion]
  constructor
  · rintro ⟨rho, hrho, hq⟩
    have hqrho := mem_xiZeroCopyFiber.mp hq
    rw [criticalFeatureCanonicalShallowRightSupportPacket,
      Finset.mem_filter, mem_xiSupportsPos] at hrho
    subst rho
    exact ⟨hrho.1.1, hrho.1.2, hrho.2.1, hrho.2.2⟩
  · rintro ⟨hheight, hpos, hright, hdeep⟩
    refine ⟨q.1, ?_, mem_xiZeroCopyFiber.mpr rfl⟩
    rw [criticalFeatureCanonicalShallowRightSupportPacket,
      Finset.mem_filter, mem_xiSupportsPos]
    exact ⟨⟨hheight, hpos⟩, hright, hdeep⟩

theorem mem_criticalFeatureCanonicalDeepRightCopyPacket
    {n : ℕ} {q : XiZeroCopy} :
    q ∈ criticalFeatureCanonicalDeepRightCopyPacket n ↔
      |(q.1 : ℂ).im| ≤ n ∧ 0 < (q.1 : ℂ).im ∧
        7 / 10 ≤ (q.1 : ℂ).re := by
  classical
  rw [criticalFeatureCanonicalDeepRightCopyPacket, Finset.mem_biUnion]
  constructor
  · rintro ⟨rho, hrho, hq⟩
    have hqrho := mem_xiZeroCopyFiber.mp hq
    rw [criticalFeatureCanonicalDeepRightSupportPacket,
      Finset.mem_filter, mem_xiSupportsPos] at hrho
    subst rho
    exact ⟨hrho.1.1, hrho.1.2, hrho.2⟩
  · rintro ⟨hheight, hpos, hdeep⟩
    refine ⟨q.1, ?_, mem_xiZeroCopyFiber.mpr rfl⟩
    rw [criticalFeatureCanonicalDeepRightSupportPacket,
      Finset.mem_filter, mem_xiSupportsPos]
    exact ⟨⟨hheight, hpos⟩, hdeep⟩

/-- Every canonical shallow copy lies on the strict-right side in centered transverse
coordinates. -/
theorem criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalShallowRightCopyPacket n) :
    0 < (I * xiSpectralPoint q).re := by
  have hdata := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re]
  norm_num
  linarith [hdata.2.2.1]

/-- `Re rho < 7/10` is exactly the centered HCF transverse strip `|Im z| < 1/5` on the
strict-right side. -/
theorem criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalShallowRightCopyPacket n) :
    |(xiSpectralPoint q).im| ≤ 1 / 5 := by
  have hdata := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hq
  rw [xiSpectralPoint_im_eq, abs_of_nonpos (by linarith [hdata.2.2.1])]
  linarith [hdata.2.2.2]

private def criticalFeatureXiSupportEmbedding : XiDivisorSupport ↪ ℂ where
  toFun rho := (rho : ℂ)
  inj' := Subtype.coe_injective

/-- The literal canonical deep Xi-copy count is bounded by Route T's multiplicity-exact
Littlewood count in the same height window. -/
theorem card_criticalFeatureCanonicalDeepRightCopyPacket_le_zetaLittlewoodZeroCountAbove
    (n : ℕ) :
    ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) ≤
      Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
        (n : ℝ) (7 / 10) := by
  classical
  let D : Finset XiDivisorSupport :=
    criticalFeatureCanonicalDeepRightSupportPacket n
  let Z : Finset ℂ :=
    (Sieve.zetaResidueUnitClosedRectangleZeros
      ((Sieve.inghamFixedGabrielSigma : ℂ) + (-(n : ℝ) : ℝ) * I)
      ((4 : ℂ) + (n : ℝ) * I)).filter fun w => 7 / 10 ≤ w.re
  have hsub : D.map criticalFeatureXiSupportEmbedding ⊆ Z := by
    intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨rho, hrhoD, rfl⟩ := hw
    have hrho : rho ∈ criticalFeatureCanonicalDeepRightSupportPacket n := hrhoD
    rw [criticalFeatureCanonicalDeepRightSupportPacket,
      Finset.mem_filter, mem_xiSupportsPos] at hrho
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    have hxi := xi_eq_zero_of_mem_divisor_support rho
    have hzeta := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
    have hunit : zetaResidueUnit (rho : ℂ) = 0 :=
      zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hzeta
    simp only [Z, Finset.mem_filter]
    refine ⟨Sieve.mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, hunit⟩, hrho.2⟩
    rw [Complex.mem_reProdIm]
    rw [show criticalFeatureXiSupportEmbedding rho = (rho : ℂ) from rfl]
    constructor
    · have hre : (rho : ℂ).re ∈ Set.Icc Sieve.inghamFixedGabrielSigma 4 := by
        constructor
        · norm_num [Sieve.inghamFixedGabrielSigma]
          linarith [hrho.2]
        · linarith [hstrip.2]
      have hlre :
          ((Sieve.inghamFixedGabrielSigma : ℂ) + (-(n : ℝ) : ℝ) * I).re =
            Sieve.inghamFixedGabrielSigma := by norm_num
      have hure : ((4 : ℂ) + (n : ℝ) * I).re = 4 := by norm_num
      rw [hlre, hure, uIcc_of_le (by norm_num [Sieve.inghamFixedGabrielSigma])]
      exact hre
    · have him : (rho : ℂ).im ∈ Set.Icc (-(n : ℝ)) (n : ℝ) :=
        abs_le.mp hrho.1.1
      have hlim :
          ((Sieve.inghamFixedGabrielSigma : ℂ) + (-(n : ℝ) : ℝ) * I).im =
            -(n : ℝ) := by simp
      have huim : ((4 : ℂ) + (n : ℝ) * I).im = n := by simp
      have hn : (-(n : ℝ)) ≤ n := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [hlim, huim, uIcc_of_le hn]
      exact him
  have hregroup :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) =
        ∑ rho ∈ D, (xiSupportMultiplicity rho : ℝ) := by
    rw [criticalFeatureCanonicalDeepRightCopyPacket,
      card_biUnion_xiZeroCopyFiber]
    norm_cast
  calc
    ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) =
        ∑ rho ∈ D, (xiSupportMultiplicity rho : ℝ) := hregroup
    _ = ∑ w ∈ D.map criticalFeatureXiSupportEmbedding,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro rho hrho
      have hstrip := xi_divisor_support_re_mem_open_unit rho
      change (xiSupportMultiplicity rho : ℝ) =
        ((analyticOrderAt zetaResidueUnit (rho : ℂ)).toNat : ℝ)
      norm_cast
      rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat,
        Sieve.analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip hstrip]
    _ ≤ ∑ w ∈ Z,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro w hwZ hwD
      positivity
    _ = Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
        (n : ℝ) (7 / 10) := by
      rfl

/-- The actual multiplicity-copy deep packet has density zero relative to the canonical Riemann
zero count. -/
theorem tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    tendsto_zetaLittlewoodZeroCountAbove_sevenTenths_div_canonicalZeroCount
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    exact div_nonneg (Nat.cast_nonneg _) hN.le
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    exact div_le_div_of_nonneg_right
      (card_criticalFeatureCanonicalDeepRightCopyPacket_le_zetaLittlewoodZeroCountAbove n)
      hN.le

end


end RHTower
