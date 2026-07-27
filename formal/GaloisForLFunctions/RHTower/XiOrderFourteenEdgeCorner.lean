import GaloisForLFunctions.RHTower.XiEndpointOffLineQuartetHeightGap
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The compact edge corner for the order-fourteen squared-Xi source

For a Xi zero with centered coordinates `delta + gamma*I`, the order-fourteen radial atom is
controlled by the fifteenth reciprocal power of

`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

This module proves the exact rational reduction behind the sector argument.  At every `y > 1/4`,
failure of `100*B^2 < A^2` forces an off-critical zero into the compact corner

`1/5 < delta^2 < 1/4` and `85 < gamma^2 < 100`.

No zero computation, RH assumption, or unproved analytic input occurs here.  The complex sector
lemma below turns the rational certificate into strict positivity of the fifteenth reciprocal
power.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose transverse-to-longitudinal ratio is strictly below `1/10` has a
strictly positive fifteenth reciprocal power.  This is the exact complex-sector implication used
by the order-fourteen radial source. -/
theorem orderFifteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 100 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 15).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 1 / 10) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

/-- A nonzero centered horizontal square is exactly an off-critical real part. -/
theorem re_ne_half_of_pos_centered_sq {x : ℝ} (h : 0 < (x - 1 / 2) ^ 2) : x ≠ 1 / 2 := by
  intro hx
  rw [hx] at h
  norm_num at h

/-- **A nonpositive reciprocal power falls into the sector-failure window.**  At a Xi zero the
radial coordinate `A = im² - (re - 1/2)² + y` is positive for every `y > 1/4`, because the strip
keeps `(re - 1/2)² < 1/4`.  A positivity criterion `hcrit` then makes a nonpositive real part of
`((A - B i)⁻¹) ^ n` refute the sector ratio `N B² < A²`, and whatever conclusion `hwindow` draws
from that failure holds.  Order, sector constant and window are all parameters, so this is the
single law behind every order's reciprocal-power reduction. -/
theorem xiZeroCopy_reciprocalPower_nonpos_of_sector {n : ℕ} {N y : ℝ} {W : Prop}
    (q : XiZeroCopy) (hy : 1 / 4 < y)
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ 2 < A ^ 2 →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hwindow :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 → W)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ n).re ≤ 0) :
    W := by
  have hA : 0 < (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y := by
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    nlinarith [sq_nonneg (q.1 : ℂ).im]
  exact hwindow
    (GaloisForLFunctions.HTGeometry.sq_le_of_re_inv_sub_mul_I_pow_nonpos
      (fun h => hcrit _ _ hA h) hnonpos)

/-- **Reciprocal-power positivity from an empty window.**  On the critical line the transverse
coordinate `B` vanishes and `A = im² + y` is positive, so the sector ratio is trivial.  Off it, a
nonpositive real part would place the zero in the window `W`, and `W` is empty.  The real part is
therefore positive at every Xi zero, for whatever order and sector constant `hcrit` supplies. -/
theorem xiZeroCopy_reciprocalPower_re_pos_of_window_empty {n : ℕ} {N y : ℝ} {W : Prop}
    (q : XiZeroCopy) (hy : 1 / 4 < y)
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ 2 < A ^ 2 →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hcorner : (q.1 : ℂ).re ≠ 1 / 2 →
      (let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
       let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
       ((((A : ℂ) - B * I)⁻¹) ^ n).re ≤ 0) → W)
    (hempty : ¬ W) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re := by
  intro A B
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · have hB : B = 0 := by
      show 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im = 0
      rw [hoff]
      ring
    have hA : 0 < A := by
      show 0 < (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      rw [hoff]
      nlinarith [sq_nonneg (q.1 : ℂ).im]
    refine hcrit A B hA ?_
    rw [hB]
    simpa using pow_pos hA 2
  · by_contra hnot
    exact hempty (hcorner hoff (not_lt.mp hnot))

/-- Off the critical line, the central four-fifths of the critical strip satisfies the rational
order-fifteen sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderFifteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 5 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 100) (u₀ := 1 / 5)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Every Xi zero above squared height `100` satisfies the rational order-fifteen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderFifteenSectorRatio_of_hundred_le_im_sq
    (q : XiZeroCopy) (hhigh : 100 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 100)
    (u₀ := 1 / 4) (v₀ := 100) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

/-- **Exact compact-edge reduction.**  If an off-critical Xi zero fails the rational
order-fifteen sector certificate at `y > 1/4`, then its centered real square lies strictly between
`1/5` and `1/4`, while its ordinate square lies strictly between `85` and `100`. -/
theorem xiOrderFifteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        100 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 100 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderFifteenSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderFifteenSectorRatio_of_hundred_le_im_sq q h hy) hfail

/-- **Actual order-fifteen atom reduction.**  A nonpositive fifteenth reciprocal-power atom from
an off-critical Xi zero at `y > 1/4` must come from the exact compact edge corner. -/
theorem xiOrderFifteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 15).re ≤ 0) :
    (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 100 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderFifteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiOrderFifteenSectorFailure_mem_edgeCorner q hoff hy) hnonpos

end

end RHTower
