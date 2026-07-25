/-
# Bourgain's Section 3 spacing exponent arithmetic

This file isolates the exact power comparison in the last paragraph of
Section 3 of Bourgain's proof.

After the first- and second-spacing estimates have been combined, equation
(3.18) gives two relevant bounds below `M = T^(3/7)`:

* `A ≤ M^4 T^(1/2)` when `M ≥ T^(5/12)`;
* `A ≤ M^2 T^(4/3)` when `M < T^(5/12)`.

Together with the lower endpoint `M ≥ T^(17/42)`, both imply
`A ≤ M^3 T^(13/14)`.  Taking a sixth root then gives
`|S| ≤ M^(1/2) T^(13/84)`.

The analytic spacing estimates themselves are not asserted here.  The
theorems below prove only their exact algebraic consequence, so later files
must supply every analytic premise.
-/
import GaloisForLFunctions.RHTower.BourgainExponentEndgame

namespace RHTower

/-- In the middle range, `M^4 T^(1/2)` is at most Bourgain's target sixth
power because `M ≤ T^(3/7)`. -/
theorem bourgain_mid_spacing_power_le
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hMT : M ≤ T ^ (3 / 7 : ℝ)) :
    M ^ (4 : ℕ) * T ^ (1 / 2 : ℝ) ≤
      M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by
  have hTpow : 0 ≤ T ^ (1 / 2 : ℝ) := Real.rpow_nonneg hT.le _
  have hMpow : 0 ≤ M ^ (3 : ℕ) := pow_nonneg hM _
  calc
    M ^ (4 : ℕ) * T ^ (1 / 2 : ℝ) =
        M ^ (3 : ℕ) * (M * T ^ (1 / 2 : ℝ)) := by ring
    _ ≤ M ^ (3 : ℕ) *
        (T ^ (3 / 7 : ℝ) * T ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hMT hTpow) hMpow
    _ = M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by
      rw [← Real.rpow_add hT]
      congr 2
      norm_num

/-- In the lower range, the endpoint `T^(17/42) ≤ M` absorbs the extra
power in `M^2 T^(4/3)`. -/
theorem bourgain_low_spacing_power_le
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hTM : T ^ (17 / 42 : ℝ) ≤ M) :
    M ^ (2 : ℕ) * T ^ (4 / 3 : ℝ) ≤
      M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by
  have hTpow : 0 ≤ T ^ (13 / 14 : ℝ) := Real.rpow_nonneg hT.le _
  have hMpow : 0 ≤ M ^ (2 : ℕ) := pow_nonneg hM _
  calc
    M ^ (2 : ℕ) * T ^ (4 / 3 : ℝ) =
        M ^ (2 : ℕ) *
          (T ^ (17 / 42 : ℝ) * T ^ (13 / 14 : ℝ)) := by
      rw [← Real.rpow_add hT]
      congr 2
      norm_num
    _ ≤ M ^ (2 : ℕ) * (M * T ^ (13 / 14 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hTM hTpow) hMpow
    _ = M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by ring

/-- Exact Section 3 range split.  It combines the direct `M ≥ T^(3/7)`
estimate with the two relevant cases of Bourgain's equation (3.18). -/
theorem bourgain_spacing_sixth_power_endgame
    {T M A : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hLower : T ^ (17 / 42 : ℝ) ≤ M)
    (hDirect :
      T ^ (3 / 7 : ℝ) ≤ M →
        A ≤ M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ))
    (hMiddle :
      T ^ (5 / 12 : ℝ) ≤ M →
        A ≤ M ^ (4 : ℕ) * T ^ (1 / 2 : ℝ))
    (hLow :
      M < T ^ (5 / 12 : ℝ) →
        A ≤ M ^ (2 : ℕ) * T ^ (4 / 3 : ℝ)) :
    A ≤ M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by
  by_cases hDirectRange : T ^ (3 / 7 : ℝ) ≤ M
  · exact hDirect hDirectRange
  have hUpper : M ≤ T ^ (3 / 7 : ℝ) :=
    le_of_not_ge hDirectRange
  by_cases hMiddleRange : T ^ (5 / 12 : ℝ) ≤ M
  · exact (hMiddle hMiddleRange).trans
      (bourgain_mid_spacing_power_le hT hM hUpper)
  · exact (hLow (lt_of_not_ge hMiddleRange)).trans
      (bourgain_low_spacing_power_le hT hM hLower)

/-- Sixth power of Bourgain's target is exactly the moment target occurring
in Section 3. -/
theorem bourgain_target_pow_six
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) :
    (M ^ (1 / 2 : ℝ) * T ^ bourgainZetaExponent) ^ (6 : ℕ) =
      M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ) := by
  rw [mul_pow]
  have hMhalf :
      (M ^ (1 / 2 : ℝ)) ^ (6 : ℕ) = M ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    norm_num
  have hTexp :
      (T ^ bourgainZetaExponent) ^ (6 : ℕ) =
        T ^ (13 / 14 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    congr 1
    simp only [bourgainZetaExponent]
    norm_num
  rw [hMhalf, hTexp]

/-- Taking the nonnegative sixth root of the Section 3 moment estimate gives
the published `M^(1/2) T^(13/84)` bound. -/
theorem bourgain_bound_of_sixth_power
    {T M S : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hSixth :
      S ^ (6 : ℕ) ≤ M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ)) :
    S ≤ M ^ (1 / 2 : ℝ) * T ^ bourgainZetaExponent := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0)
    (mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hT.le _))
  rw [bourgain_target_pow_six hT hM]
  exact hSixth

/-- Complete algebraic consequence of the three Section 3 spacing regimes. -/
theorem bourgain_spacing_endgame
    {T M S : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hLower : T ^ (17 / 42 : ℝ) ≤ M)
    (hDirect :
      T ^ (3 / 7 : ℝ) ≤ M →
        S ^ (6 : ℕ) ≤ M ^ (3 : ℕ) * T ^ (13 / 14 : ℝ))
    (hMiddle :
      T ^ (5 / 12 : ℝ) ≤ M →
        S ^ (6 : ℕ) ≤ M ^ (4 : ℕ) * T ^ (1 / 2 : ℝ))
    (hLow :
      M < T ^ (5 / 12 : ℝ) →
        S ^ (6 : ℕ) ≤ M ^ (2 : ℕ) * T ^ (4 / 3 : ℝ)) :
    S ≤ M ^ (1 / 2 : ℝ) * T ^ bourgainZetaExponent := by
  apply bourgain_bound_of_sixth_power hT hM
  exact bourgain_spacing_sixth_power_endgame hT hM hLower
    hDirect hMiddle hLow

end RHTower
