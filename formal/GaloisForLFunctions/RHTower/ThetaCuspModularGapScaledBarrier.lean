import GaloisForLFunctions.RHTower.ThetaCuspModularBarrierFlux

/-!
# A gap-scaled bound for the actual modular slope defect

The complete actual orbit satisfies `0 ≤ (u/3-J)/(t*(k+1/3)) < 1/12`.
The kinetic-gap bound makes the forcing of the comparison defect strictly
positive everywhere; a positive comparison defect would escape its global
upper bound on a complete ray. This controls a normalized source correction
without assuming a determinant sign or any asymptotic source estimate.
-/

open Set Filter Topology
namespace RHTower.ThetaCuspModularRatio
noncomputable section

/-- Difference from the gap-scaled slope barrier. -/
def gapScaledDefect (x : ℝ) : ℝ := barrierDefect x-t x*(k x+1/3)/12

private theorem forcingBracket_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < 8-2*(3-u x)*k x+2*u x/3-J x := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hu3 := thetaCuspModularMassDrift_lt_three hx
  have hk := k_gt hx
  have hg := kineticGap_lt hx
  have ht : (3-u x)^(2 : ℕ) ≤ t x := by
    have h := mul_nonneg hu (show 0 ≤ 3-u x by linarith only [hu3])
    dsimp [t]
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg (k x))
  have hp : 0 ≤ (3-u x)*k x := mul_nonneg (by linarith only [hu3]) (by linarith only [hk])
  have hb : (3-u x)*k x < 19/5 := by nlinarith only [hm, hg, hp]
  have hj := J_le_third_drift hx
  linarith only [hb, hu, hj]

private theorem dGapScaled {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gapScaledDefect
      (2*u x*(k x+2/3)*gapScaledDefect x+
        (t x*(k x+1/3)/6)*(8-2*(3-u x)*k x+2*u x/3-J x)) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert (((du hx).div_const 3).sub (dJ hx)).sub
    (((dt hx).mul ((dk hx).add_const (1/3 : ℝ))).div_const 12) using 1
  all_goals first | rfl |
    (dsimp [gapScaledDefect, barrierDefect, D, t]; field_simp [hk]; ring)

private theorem gapScaled_upper {x : ℝ} (hx : 0 ≤ x) : gapScaledDefect x ≤ 1 := by
  have hp : 0 ≤ t x*(k x+1/3)/12 := by
    have ht := t_pos hx
    have hk := k_gt hx
    positivity
  dsimp [gapScaledDefect, barrierDefect]
  linarith only [hp, thetaCuspModularMassDrift_lt_three hx, J_nonneg hx]

private theorem gapScaled_zero_neg : gapScaledDefect 0 < 0 := by
  have ht := t_pos (show (0 : ℝ) ≤ 0 by rfl)
  have hk := k_gt (show (0 : ℝ) ≤ 0 by rfl)
  have hz : barrierDefect 0 = 0 := by simp [barrierDefect, J_zero, u]
  dsimp [gapScaledDefect]
  rw [hz]
  have hp : 0 < t 0*(k 0+1/3)/12 := by positivity
  linarith only [hp]

private theorem gapScaled_nonpos {b : ℝ} (hb : 0 ≤ b) : gapScaledDefect b ≤ 0 := by
  by_contra hn
  have hFb : 0 < gapScaledDefect b := lt_of_not_ge hn
  have hb0 : 0 < b := by
    rcases hb.eq_or_lt with heq | hlt
    · subst b
      linarith only [hFb, gapScaled_zero_neg]
    · exact hlt
  have hub : 0 < u b := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hb0)
  have hkb := k_gt hb
  let c : ℝ := 2*u b*(k b+2/3)*gapScaledDefect b
  have hc : 0 < c := by dsimp [c]; positivity
  have hderiv {y : ℝ} (hy : b ≤ y) (hFy : gapScaledDefect b ≤ gapScaledDefect y) :
      c ≤ deriv gapScaledDefect y := by
    have hy0 := hb.trans hy
    have hky := k_mono hb hy0 hy
    have huy := u_mono hb hy0 hy
    have huy0 : 0 ≤ u y := hub.le.trans huy
    have hky0 : 0 ≤ k y+2/3 := by linarith only [hky, hkb]
    have hky1 : 0 < k y+1/3 := by linarith only [hky, hkb]
    have hf : 0 ≤ (t y*(k y+1/3)/6)*(8-2*(3-u y)*k y+2*u y/3-J y) := by
      have ht := t_pos hy0
      have hp := forcingBracket_pos hy0
      positivity
    have hm : c ≤ 2*u y*(k y+2/3)*gapScaledDefect y := by
      dsimp [c]
      gcongr
    rw [(dGapScaled hy0).deriv]
    linarith only [hm, hf]
  have hbound : ∀ x, b ≤ x → gapScaledDefect b ≤ gapScaledDefect x := by
    intro x hbx
    have h : -gapScaledDefect x ≤ -gapScaledDefect b := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun y => -gapScaledDefect y) (f' := fun y => -deriv gapScaledDefect y)
        (a := b) (b := x)
        (fun y hy => (dGapScaled (hb.trans hy.1)).neg.continuousAt.continuousWithinAt)
        (fun y hy => ((dGapScaled (hb.trans hy.1)).differentiableAt.hasDerivAt.neg).hasDerivWithinAt)
        (B := fun _ => -gapScaledDefect b) (B' := fun _ => 0)
        le_rfl (fun y => hasDerivAt_const y (-gapScaledDefect b)) ?_ ⟨hbx, le_rfl⟩
      intro y hy he
      have hFy : gapScaledDefect b ≤ gapScaledDefect y := by linarith only [he]
      have hd := hderiv hy.1 hFy
      linarith only [hd, hc]
    linarith only [h]
  have hmono : MonotoneOn (fun y => gapScaledDefect y-c*y) (Ici b) := by
    have hd (y : ℝ) (hy : b ≤ y) :
        HasDerivAt (fun z => gapScaledDefect z-c*z) (deriv gapScaledDefect y-c) y := by
      convert (dGapScaled (hb.trans hy)).differentiableAt.hasDerivAt.sub
        ((hasDerivAt_id y).const_mul c) using 1
      all_goals first | rfl | simp
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (show b ≤ y from (show b < y by simpa [interior_Ici] using hy).le)).differentiableAt.differentiableWithinAt)
    intro y hy
    have hby : b ≤ y := (show b < y by simpa [interior_Ici] using hy).le
    rw [(hd y hby).deriv]
    exact sub_nonneg.mpr (hderiv hby (hbound y hby))
  let x : ℝ := b+2/c
  have hbx : b ≤ x := by dsimp [x]; linarith [div_pos (by norm_num : (0 : ℝ)<2) hc]
  have hinc := hmono (show b ∈ Ici b by simp) hbx hbx
  have he : c*(x-b)=2 := by dsimp [x]; field_simp [hc.ne']; ring
  have hu := gapScaled_upper (hb.trans hbx)
  nlinarith only [hinc, he, hu, hFb]

/-- Strict gap-scaled upper bound on the actual full theta defect. -/
theorem barrierDefect_lt_gap {x : ℝ} (hx : 0 ≤ x) :
    barrierDefect x < t x*(k x+1/3)/12 := by
  have hle := gapScaled_nonpos hx
  have hlt : gapScaledDefect x < 0 := by
    rcases hx.eq_or_lt with heq | hx0
    · subst x
      exact gapScaled_zero_neg
    · by_contra hn
      have hz : gapScaledDefect x = 0 := le_antisymm hle (le_of_not_gt hn)
      have hmax : IsLocalMax gapScaledDefect x := by
        filter_upwards [eventually_gt_nhds hx0] with y hy
        rw [hz]
        exact gapScaled_nonpos hy.le
      have hd := hmax.hasDerivAt_eq_zero (dGapScaled hx)
      rw [hz, mul_zero, zero_add] at hd
      have hp := forcingBracket_pos hx
      have ht := t_pos hx
      have hk := k_gt hx
      have hh : 0 < (t x*(k x+1/3)/6)*(8-2*(3-u x)*k x+2*u x/3-J x) := by positivity
      linarith only [hh, hd]
  exact sub_neg.mp hlt

/-- The normalized defect stays in a fixed nonnegative interval on the complete half-orbit. -/
theorem normalized_barrierDefect_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ barrierDefect x/(t x*(k x+1/3)) ∧
      barrierDefect x/(t x*(k x+1/3)) < 1/12 := by
  have ht := t_pos hx
  have hk := k_gt hx
  have hd : 0 < t x*(k x+1/3) := by positivity
  refine ⟨div_nonneg (barrierDefect_nonneg hx) hd.le, (div_lt_iff₀ hd).mpr ?_⟩
  have h := barrierDefect_lt_gap hx
  linarith only [h]

end
end RHTower.ThetaCuspModularRatio
