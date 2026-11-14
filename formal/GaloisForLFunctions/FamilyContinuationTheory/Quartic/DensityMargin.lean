import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The quartic zero-density exponent margin

The piecewise density exponent, combined with the local correction cost, stays
below `599/600` on the entire contour-shift interval. This is a real-variable
inequality; it does not assume or assert a zero-density theorem for L-functions.
The middle interval is controlled by an explicit positive cubic certificate.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic

/-- Quartic family norm exponent, expressed in the abscissa variable. -/
noncomputable def densityExponent (σ : ℝ) : ℝ :=
  if σ ≤ 3 / 4 then 1 - (2 * σ - 1) / (8 * (1 - σ))
  else if σ ≤ 7 / 8 then
    1 - (2 * σ - 1) * (4 * (2 * σ - 1) - 1) /
      (24 * (2 * σ - 1) - 16 * (2 * σ - 1) ^ 2 - 6)
  else 6 * (1 - σ) / (1 + 4 * (1 - σ))

/-- Combined abscissa after fourth-power decomposition and the local Euler loss. -/
noncomputable def densityTransfer (σ : ℝ) : ℝ :=
  σ + (65 / 144) * (max (densityExponent σ - 1 / 4) 0 + max 0 (1 - 3 * σ / 2))

private theorem middle_certificate (x : ℝ) (hx : -(4 / 25) ≤ x) :
    0 < 8 * x ^ 3 + (139 / 45) * x ^ 2 + (589 / 90000) * x + 13 / 750000 := by
  have hc := mul_nonneg (show 0 ≤ 8 * x + 32 / 25 by linarith only [hx]) (sq_nonneg x)
  have hq : 0 < (9 / 5) * x ^ 2 - |x| / 150 + 1 / 60000 := by
    have hs := sq_nonneg (|x| - 1 / 540)
    nlinarith only [hs, sq_abs x]
  have hxabs := neg_abs_le x
  have ha := abs_nonneg x
  have hsq := sq_nonneg x
  nlinarith only [hc, hq, hxabs, ha, hsq]

private theorem low_density_bound (σ : ℝ) (hσ : 5 / 8 ≤ σ) (hσ' : σ ≤ 2 / 3) :
    densityExponent σ ≤ 11 / 12 := by
  rw [densityExponent, if_pos (by linarith only [hσ'])]
  have hd : 0 < 8 * (1 - σ) := by linarith only [hσ']
  have hratio : (1 / 12 : ℝ) ≤ (2 * σ - 1) / (8 * (1 - σ)) := by
    apply (le_div_iff₀ hd).mpr
    linarith only [hσ]
  linarith only [hratio]

private theorem lower_middle_bound (σ : ℝ) (hσ : 2 / 3 ≤ σ) (hσ' : σ ≤ 3 / 4) :
    σ + (65 / 144) * (densityExponent σ - 1 / 4) ≤ 281 / 288 := by
  rw [densityExponent, if_pos hσ']
  have hd : 0 < 8 * (1 - σ) := by linarith only [hσ']
  have hr := (div_mul_cancel₀ (2 * σ - 1) (ne_of_gt hd))
  have hp := mul_nonneg (show 0 ≤ 3 / 4 - σ by linarith only [hσ'])
    (show 0 ≤ 1 - σ - 65 / 288 by linarith only [hσ'])
  apply (mul_le_mul_iff_left₀ hd).mp
  nlinarith only [hr, hp]

private theorem middle_bound (σ : ℝ) (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (hbranch : ¬σ ≤ 3 / 4) :
    σ + (65 / 144) * (densityExponent σ - 1 / 4) < 599 / 600 := by
  rw [densityExponent, if_neg hbranch, if_pos hσ']
  let q := 2 * σ - 1
  let d := 24 * q - 16 * q ^ 2 - 6
  have hq : (1 / 2 : ℝ) ≤ q := by dsimp [q]; linarith only [hσ]
  have hq' : q ≤ (3 / 4 : ℝ) := by dsimp [q]; linarith only [hσ']
  have hd : 0 < d := by
    have hp := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hq')
    dsimp [d]
    nlinarith only [hp, hq]
  have hc := middle_certificate (q - 33 / 50) (by linarith only [hq])
  have hr := div_mul_cancel₀ (q * (4 * q - 1)) (ne_of_gt hd)
  change σ + 65 / 144 * (1 - q * (4 * q - 1) / d - 1 / 4) < 599 / 600
  apply (mul_lt_mul_iff_right₀ hd).mp
  have hid : d * (599 / 600 - (σ + 65 / 144 * (1 - q * (4 * q - 1) / d - 1 / 4))) =
      8 * (q - 33 / 50) ^ 3 + 139 / 45 * (q - 33 / 50) ^ 2 +
        589 / 90000 * (q - 33 / 50) + 13 / 750000 := by
    dsimp [d, q] at *
    nlinarith only [hr]
  nlinarith only [hid, hc]

private theorem high_bound (σ : ℝ) (hσ : 7 / 8 ≤ σ) (hσ' : σ ≤ 1)
    (hbranch : ¬σ ≤ 7 / 8) :
    σ + (65 / 144) * (densityExponent σ - 1 / 4) ≤ 569 / 576 := by
  rw [densityExponent, if_neg (by linarith only [hσ]), if_neg hbranch]
  have hd : 0 < 1 + 4 * (1 - σ) := by linarith only [hσ']
  have hr := div_mul_cancel₀ (6 * (1 - σ)) (ne_of_gt hd)
  have hp := mul_nonneg (show 0 ≤ σ - 7 / 8 by linarith only [hσ])
    (show 0 ≤ 4 * σ - 115 / 36 by linarith only [hσ])
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [hr, hp]

/-- Uniform transfer margin on its full closed interval of abscissae. -/
theorem densityTransfer_bound (σ : Set.Icc (5 / 8 : ℝ) (599 / 600)) :
    densityTransfer σ ≤ 599 / 600 := by
  obtain ⟨hlo, hhi⟩ := σ.property
  unfold densityTransfer
  by_cases hlow : (σ : ℝ) ≤ 2 / 3
  · have hE := low_density_bound σ hlo hlow
    have hmax : max (densityExponent σ - 1 / 4) 0 ≤ 2 / 3 := by
      apply max_le <;> linarith only [hE]
    rw [max_eq_right (by linarith only [hlow])]
    nlinarith only [hmax, hlow]
  · rw [max_eq_left (by linarith only [hlow])]
    by_cases hE : densityExponent σ - 1 / 4 ≤ 0
    · rw [max_eq_right hE, add_zero, mul_zero, add_zero]
      exact hhi
    · rw [max_eq_left (le_of_not_ge hE), add_zero]
      by_cases hm : (σ : ℝ) ≤ 3 / 4
      · have hb := lower_middle_bound σ (le_of_not_ge hlow) hm
        linarith only [hb]
      · by_cases hh : (σ : ℝ) ≤ 7 / 8
        · exact (middle_bound σ (le_of_not_ge hm) hh hm).le
        · have hb := high_bound σ (le_of_not_ge hh) (by linarith only [hhi]) hh
          linarith only [hb]

/-- The zero-free floor bin also fits when only the trivial family count is used. -/
theorem floor_bin_bound :
    (5 / 8 : ℝ) + (65 / 144) * (max (1 - 1 / 4 : ℝ) 0 + max 0 (1 - 3 * (5 / 8) / 2)) <
      599 / 600 := by norm_num

end GaloisForLFunctions.FamilyContinuationTheory.Quartic
