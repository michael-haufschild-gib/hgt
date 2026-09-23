import GaloisForLFunctions.HTGeometry.FirstAtomOddScaleSevenBounds

/-! # Lower profile bounds and absolute leading-minor control on scale seven -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000

/-- Positive polynomial reserve for the lower order-1 entry bound. -/
theorem firstAtomOddScaleSeven_profile1_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    8 ≤ firstAtomOddTailProfile1 u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator1 u-8*firstAtomOddTailDenominator u =
      (192/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator1 firstAtomOddTailDenominator
        ring
  have h : 0 ≤ firstAtomOddTailNumerator1 u-8*firstAtomOddTailDenominator u := by
    rw [heq]
    positivity
  unfold firstAtomOddTailProfile1
  apply (le_div_iff₀ hD).mpr
  linarith only [h]

/-- Positive polynomial reserve for the lower order-2 entry bound. -/
theorem firstAtomOddScaleSeven_profile2_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    180 ≤ firstAtomOddTailProfile2 u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator2 u-180*firstAtomOddTailDenominator u =
      (192 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(3 : ℕ) +
      (2944/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(2 : ℕ) +
      (24176/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(1 : ℕ) +
      (88912/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator2 firstAtomOddTailDenominator
        ring
  have h : 0 ≤ firstAtomOddTailNumerator2 u-180*firstAtomOddTailDenominator u := by
    rw [heq]
    positivity
  unfold firstAtomOddTailProfile2
  apply (le_div_iff₀ hD).mpr
  linarith only [h]

/-- Positive polynomial reserve for the lower order-3 entry bound. -/
theorem firstAtomOddScaleSeven_profile3_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    7000 ≤ firstAtomOddTailProfile3 u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator3 u-7000*firstAtomOddTailDenominator u =
      (10880 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(4 : ℕ) +
      (30080 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(3 : ℕ) +
      (1986848/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(2 : ℕ) +
      (11462208/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(1 : ℕ) +
      (28986784/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator3 firstAtomOddTailDenominator
        ring
  have h : 0 ≤ firstAtomOddTailNumerator3 u-7000*firstAtomOddTailDenominator u := by
    rw [heq]
    positivity
  unfold firstAtomOddTailProfile3
  apply (le_div_iff₀ hD).mpr
  linarith only [h]

/-- Positive polynomial reserve for the lower order-4 entry bound. -/
theorem firstAtomOddScaleSeven_profile4_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    300000 ≤ firstAtomOddTailProfile4 u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator4 u-300000*firstAtomOddTailDenominator u =
      (2081280 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(5 : ℕ) +
      (59719680/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(4 : ℕ) +
      (719970432/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(3 : ℕ) +
      (4651030144/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(2 : ℕ) +
      (16233846656/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(1 : ℕ) +
      (24279398272/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator4 firstAtomOddTailDenominator
        ring
  have h : 0 ≤ firstAtomOddTailNumerator4 u-300000*firstAtomOddTailDenominator u := by
    rw [heq]
    positivity
  unfold firstAtomOddTailProfile4
  apply (le_div_iff₀ hD).mpr
  linarith only [h]

/-- Positive polynomial reserve for the lower order-5 entry bound. -/
theorem firstAtomOddScaleSeven_profile5_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    20000000 ≤ firstAtomOddTailProfile5 u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator5 u-20000000*firstAtomOddTailDenominator u =
      (175452160 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(6 : ℕ) +
      (6016880640/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(5 : ℕ) +
      (88510417920/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(4 : ℕ) +
      (725925785600/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(3 : ℕ) +
      (3543370692608/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(2 : ℕ) +
      (9792599400448/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(1 : ℕ) +
      (11886004767744/117649 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator5 firstAtomOddTailDenominator
        ring
  have h : 0 ≤ firstAtomOddTailNumerator5 u-20000000*firstAtomOddTailDenominator u := by
    rw [heq]
    positivity
  unfold firstAtomOddTailProfile5
  apply (le_div_iff₀ hD).mpr
  linarith only [h]

/-- The leading first-atom minor is nonnegative throughout the enlarged interval. -/
theorem firstAtomOddScaleSeven_head_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile1 u*firstAtomOddTailProfile3 u-firstAtomOddTailProfile2 u^(2 : ℕ) := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ) =
      (6291456 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(6 : ℕ) +
      (221773824/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(5 : ℕ) +
      (3288858624/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(4 : ℕ) +
      (26295140352/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(3 : ℕ) +
      (119636361216/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(2 : ℕ) +
      (41970401280/2401 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(1 : ℕ) +
      (6208585728/2401 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailNumerator1 firstAtomOddTailNumerator2 firstAtomOddTailNumerator3
        ring
  have h : 0 ≤ firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ) := by
    rw [heq]
    positivity
  have he : firstAtomOddTailProfile1 u*firstAtomOddTailProfile3 u-firstAtomOddTailProfile2 u^(2 : ℕ) =
      (firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ))/
        firstAtomOddTailDenominator u^(2 : ℕ) := by
    unfold firstAtomOddTailProfile1 firstAtomOddTailProfile2 firstAtomOddTailProfile3
    field_simp
  rw [he]
  exact div_nonneg h (sq_nonneg _)

/-- The absolute leading cofactor stays at most twenty-seven thousand. -/
theorem firstAtomOddScaleSeven_head_abs_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    |firstAtomOddTailProfile1 u*firstAtomOddTailProfile3 u-firstAtomOddTailProfile2 u^(2 : ℕ)| ≤ 27000 := by
  rw [abs_of_nonneg (firstAtomOddScaleSeven_head_nonneg hu0 hu1)]
  exact firstAtomOddScaleSeven_head_upper hu0 hu1

end
end HTGeometry
