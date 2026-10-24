import GaloisForLFunctions.«arithmetic-positivity-theory».ExplicitCollarThresholdsAndKernelShape
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyRecordsAreVisibleAtAnExplicitLag
import GaloisForLFunctions.ArithmeticCompensationTheory.TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange

/-!
# Certified scales for the critical family and centered prime rows

The critical and collared thresholds admit closed upper bounds using the
proved channel and slope constants. The polynomial window has a fixed
positive exponent. A radius-one-quarter probe has an exact visibility lag,
and the centered-prime theorem gives explicit rational endpoint exponents.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section

/-- A closed upper bound for the complete critical block threshold. -/
theorem criticalBlockThreshold_le_explicit :
    criticalBlockThreshold ≤
      max 2 (⌊Real.exp (criticalArchLogOffset + 125000 * (10 : ℝ)^15)⌋₊ + 1) := by
  have hratio : criticalCompleteChannelConstant / criticalArchLogSlope ≤
      125000 * (10 : ℝ)^15 := by
    rw [div_le_iff₀ criticalArchLogSlope_pos]
    nlinarith only [criticalCompleteChannelConstant_le, criticalArchLogSlope_ge]
  exact max_le_max le_rfl (Nat.add_le_add_right
    (Nat.floor_mono (Real.exp_le_exp.mpr
      (add_le_add (le_refl criticalArchLogOffset) hratio))) 1)

/-- The collar gives the explicit channel-to-slope allowance `66000·10⁸`. -/
theorem criticalCollaredBlockThreshold_le_explicit :
    criticalCollaredBlockThreshold ≤
      max 2 (⌊Real.exp (criticalCollarArchLogOffset + 66000 * (10 : ℝ)^8)⌋₊ + 1) := by
  have hratio : criticalCollaredChannelConstant / criticalCollarArchLogSlope ≤
      66000 * (10 : ℝ)^8 := by
    rw [div_le_iff₀ criticalCollarArchLogSlope_pos]
    nlinarith only [criticalCollaredChannelConstant_le, criticalCollarArchLogSlope_ge]
  exact max_le_max le_rfl (Nat.add_le_add_right
    (Nat.floor_mono (Real.exp_le_exp.mpr
      (add_le_add (le_refl criticalCollarArchLogOffset) hratio))) 1)

/-- The polynomial window threshold has no unnamed channel constants. -/
theorem criticalWindowThreshold_le_explicit :
    criticalWindowThreshold ≤
      max 2 (⌊Real.exp (2*criticalArchLogOffset + 363000*(10 : ℝ)^15)⌋₊+1) := by
  have hbound :
      2*(criticalWindowBaseConstant+6*criticalWindowPrimeSlope)/criticalArchLogSlope ≤
        363000*(10 : ℝ)^15 := by
    rw [div_le_iff₀ criticalArchLogSlope_pos]
    nlinarith only [criticalWindowBaseConstant_le, criticalWindowPrimeSlope_le,
      criticalArchLogSlope_ge]
  have heq :
      2*(criticalArchLogSlope*criticalArchLogOffset+criticalWindowBaseConstant+
        6*criticalWindowPrimeSlope)/criticalArchLogSlope =
      2*criticalArchLogOffset+
        2*(criticalWindowBaseConstant+6*criticalWindowPrimeSlope)/criticalArchLogSlope := by
    field_simp [ne_of_gt criticalArchLogSlope_pos]
    ring
  unfold criticalWindowThreshold
  rw [heq]
  exact max_le_max le_rfl (Nat.add_le_add_right
    (Nat.floor_mono (Real.exp_le_exp.mpr
      (add_le_add (le_refl (2*criticalArchLogOffset)) hbound))) 1)

/-- A single explicit positive exponent works for the complete critical polynomial windows. -/
theorem criticalCompleteEnergy_pos_of_explicit_window {M L : ℕ}
    (hM : max 2 (⌊Real.exp
      (2*criticalArchLogOffset + 363000*(10 : ℝ)^15)⌋₊+1) ≤ M)
    (hL : 1 ≤ L) (hLM : (L : ℝ) ≤ (M : ℝ)^((1 : ℝ)/10^21))
    (S : Finset ℕ) (hS : ScaleWindow S M L) (b : ℕ → ℝ)
    (hb : ∃ n ∈ S, b n ≠ 0) : 0 < criticalCompleteEnergy S b := by
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  apply criticalCompleteEnergy_pos_of_window_threshold_le
    (criticalWindowThreshold_le_explicit.trans hM) hL _ S hS b hb
  exact hLM.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ M by omega)) criticalWindowExponent_bounds.1)

end
end GaloisForLFunctions.ArithmeticPositivityTheory

namespace GaloisForLFunctions.SquareRootThreshold
noncomputable section

/-- Exact visibility scale for radius 1/4, specified loudness, and depth 1/4. -/
theorem quarterProbe_recordLag (a : ℝ) :
    recordLag (1/4) a (1/4) =
      16*(13*Real.pi*recordOrder (1/4) a+4)+1/4+
        2*Real.exp (1/8)*bumpMass (1/4)/recordScale (1/4) a := by
  unfold recordLag
  norm_num <;> ring

/-- The same probe's certified height cutoff. -/
theorem quarterProbe_recordHeight (a : ℝ) :
    recordHeightOf (1/4) a =
      (230400*(Real.exp (1/8)*scaledBumpDecay (1/4))^2/a)^((1 : ℝ)/3) := by
  unfold recordHeightOf
  congr 1
  norm_num <;> ring

end
end GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticCompensationTheory
noncomputable section
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty

/-- With δ=1/10 and ε=1/2, the centered row range is [P^(11/10), P^(283/170)]
and the block exponent is 71/120. -/
theorem exists_centeredPrimeRow_explicit_range :
    ∃ P₀ : ℕ, ∀ {N A H K P Q : ℕ} {c : ℕ → ℝ}, P₀ ≤ P →
      (P : ℝ)^(11/10 : ℝ) ≤ Q → (Q : ℝ) ≤ (P : ℝ)^(283/170 : ℝ) →
      Q ≤ A → A+K*H ≤ 2*Q → 2*Q ≤ N → (N : ℝ) ≤ (Q : ℝ)^(2 : ℝ) →
      (2*(Q : ℝ))^(71/120 : ℝ) ≤ H → (H : ℝ) ≤ 4*(Q : ℝ)^(71/120 : ℝ) →
      (∀ d, c d ≠ 0 → P < d ∧ d ≤ 2*P) →
      |rowBilinear N c (centredPrimeRow A H K)+
        rowMean N c*vonMangoldtReadout N (centredPrimeRow A H K)+
        rowBeta N c*finiteHarmonicSum N (centredPrimeRow A H K)| ≤
        8*rowInverseSquareMass N (centredPrimeRow A H K)*rowLinearWeight N c := by
  have h := exists_abs_rowBilinear_centredPrimeRow_le_of_range
    (δ := 1/10) (ε := 1/2) (C := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (1 : ℝ)+1/10 = 11/10 by norm_num,
    show (30 : ℝ)/17-1/10 = 283/170 by norm_num,
    show (17 : ℝ)/30+(1/10)/4 = 71/120 by norm_num,
    show (16 : ℝ)*(1/2) = 8 by norm_num] at h
  exact h

end
end GaloisForLFunctions.ArithmeticCompensationTheory
