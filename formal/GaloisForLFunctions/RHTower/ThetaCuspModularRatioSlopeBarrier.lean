import GaloisForLFunctions.RHTower.ThetaCuspModularRatioUpperBarrier

/-!
# A slope barrier for the full theta modular orbit

The complete-ray escape argument improves the actual defect bound to `J ≤ u / 3`.
Consequently `k² (9 - u²)` decreases and stays below `361 / 25`. These bounds
constrain the source variables of the native compensated determinant; they do
not assert a sign for that determinant.
-/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

/-- Defect from the linear barrier of slope one third. -/
def slopeDefect (x : ℝ) : ℝ := J x-u x/3

private theorem dSlope {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt slopeDefect
      (t x*(k x^2-k x-4/9)+2*u x*(k x+2/3)*slopeDefect x) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert (dJ hx).sub ((du hx).div_const 3) using 1
  all_goals first | rfl | (dsimp [slopeDefect, D, t]; field_simp [hk]; ring)

private theorem slope_zero : slopeDefect 0 = 0 := by
  simp [slopeDefect, J_zero, u]

private theorem fourThirds_le_of_slope_pos {b : ℝ} (hb : 0 < b)
    (hFb : 0 < slopeDefect b) : 4/3 ≤ k b := by
  have hc : ContinuousOn slopeDefect (Icc 0 b) :=
    fun x hx => (dSlope hx.1).continuousAt.continuousWithinAt
  let S : Set ℝ := Icc 0 b ∩ slopeDefect ⁻¹' {0}
  have hs : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hne : S.Nonempty := ⟨0, ⟨⟨le_rfl, hb.le⟩, slope_zero⟩⟩
  obtain ⟨a, ha, hmax⟩ := hs.exists_isGreatest hne
  have ha0 : 0 ≤ a := ha.1.1
  have haz : slopeDefect a = 0 := ha.2
  have hab : a < b := by
    rcases ha.1.2.eq_or_lt with heq | hlt
    · subst a
      exact False.elim ((ne_of_gt hFb) haz)
    · exact hlt
  have hpos : ∀ y ∈ Ioc a b, 0 < slopeDefect y := by
    intro y hy
    by_contra hny
    have hFy : slopeDefect y ≤ 0 := le_of_not_gt hny
    have hcy : ContinuousOn slopeDefect (Icc y b) := fun z hz =>
      (dSlope (ha0.trans (hy.1.le.trans hz.1))).continuousAt.continuousWithinAt
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hy.2 hcy ⟨hFy, hFb.le⟩
    have hzS : z ∈ S := ⟨⟨ha0.trans (hy.1.le.trans hz.1), hz.2⟩, hz0⟩
    have hza := hmax hzS
    linarith only [hz.1, hy.1, hza]
  have hdFa : 0 ≤ t a*(k a^2-k a-4/9)+2*u a*(k a+2/3)*slopeDefect a := by
    apply ge_of_tendsto ((dSlope ha0).tendsto_slope.mono_left (nhdsGT_le_nhdsNE a))
    have hlt : ∀ᶠ y in 𝓝[>] a, y < b :=
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with y hy hyb
    have hjy := hpos y ⟨hy, hyb.le⟩
    rw [slope_def_field, haz, sub_zero]
    exact div_nonneg hjy.le (sub_pos.mpr hy).le
  rw [haz, mul_zero, add_zero] at hdFa
  have hp : 0 ≤ k a^2-k a-4/9 := (mul_nonneg_iff_of_pos_left (t_pos ha0)).mp hdFa
  have hka : 4/3 ≤ k a := by
    by_contra hn
    have hneg := mul_neg_of_neg_of_pos
      (sub_neg.mpr (lt_of_not_ge hn))
      (show 0 < k a+1/3 by linarith only [k_gt ha0])
    nlinarith only [hp, hneg]
  exact hka.trans (k_mono ha0 hb.le hab.le)

/-- The actual full theta orbit remains below the one-third drift barrier. -/
theorem J_le_third_drift {b : ℝ} (hb : 0 ≤ b) : J b ≤ u b/3 := by
  by_contra hn
  have hFb : 0 < slopeDefect b := sub_pos.mpr (lt_of_not_ge hn)
  have hb0 : 0 < b := by
    rcases hb.eq_or_lt with heq | hlt
    · subst b
      rw [slope_zero] at hFb
      exact False.elim ((lt_irrefl (0 : ℝ)) hFb)
    · exact hlt
  have hkb := fourThirds_le_of_slope_pos hb0 hFb
  have hub : 0 < u b := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hb0)
  let c : ℝ := 2*u b*(k b+2/3)*slopeDefect b
  have hc : 0 < c := by dsimp [c]; positivity
  have hderiv {y : ℝ} (hy : b ≤ y) (hFy : slopeDefect b ≤ slopeDefect y) :
      c ≤ deriv slopeDefect y := by
    have hy0 := hb.trans hy
    have hky := k_mono hb hy0 hy
    have huy := u_mono hb hy0 hy
    have huy0 : 0 ≤ u y := hub.le.trans huy
    have hky0 : 0 ≤ k y+2/3 := by linarith only [hky, hkb]
    have hp : 0 ≤ k y^2-k y-4/9 := by
      have hh := mul_nonneg (show 0 ≤ k y-4/3 by linarith only [hky, hkb])
        (show 0 ≤ k y+1/3 by linarith only [hky, hkb])
      nlinarith only [hh]
    have htp := mul_nonneg (t_pos hy0).le hp
    have hmul : c ≤ 2*u y*(k y+2/3)*slopeDefect y := by
      dsimp [c]
      gcongr
    rw [(dSlope hy0).deriv]
    linarith only [hmul, htp]
  have hbound : ∀ x, b ≤ x → slopeDefect b ≤ slopeDefect x := by
    intro x hbx
    have h : -slopeDefect x ≤ -slopeDefect b := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun y => -slopeDefect y) (f' := fun y => -deriv slopeDefect y)
        (a := b) (b := x)
        (fun y hy => (dSlope (hb.trans hy.1)).neg.continuousAt.continuousWithinAt)
        (fun y hy => ((dSlope (hb.trans hy.1)).differentiableAt.hasDerivAt.neg).hasDerivWithinAt)
        (B := fun _ => -slopeDefect b) (B' := fun _ => 0)
        le_rfl (fun y => hasDerivAt_const y (-slopeDefect b)) ?_ ⟨hbx, le_rfl⟩
      intro y hy he
      have hFy : slopeDefect b ≤ slopeDefect y := by linarith only [he]
      have hd := hderiv hy.1 hFy
      linarith only [hd, hc]
    linarith only [h]
  have hmono : MonotoneOn (fun y => slopeDefect y-c*y) (Ici b) := by
    have hd (y : ℝ) (hy : b ≤ y) :
        HasDerivAt (fun z => slopeDefect z-c*z) (deriv slopeDefect y-c) y := by
      convert (dSlope (hb.trans hy)).differentiableAt.hasDerivAt.sub
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
  have hJ := J_lt_one (hb.trans hbx)
  have hu := thetaCuspModularMassDrift_nonneg (hb.trans hbx)
  dsimp [slopeDefect] at hFb hinc
  nlinarith only [hinc, he, hJ, hu, hFb]

/-- The gap factor weighted by the square of the modular ratio. -/
def kineticGap (x : ℝ) : ℝ := k x^2*t x

theorem kineticGap_deriv_nonpos {x : ℝ} (hx : 0 ≤ x) : deriv kineticGap x ≤ 0 := by
  have hd : HasDerivAt kineticGap
      (4*k x*(k x+1/3)*J x*t x-2*u x*k x^3*t x) x := by
    convert ((dk hx).pow 2).mul (dt hx) using 1
    all_goals first | rfl | (simp only [Pi.pow_apply]; ring)
  have hk := k_gt_fiveFourths hx
  have hu := thetaCuspModularMassDrift_nonneg hx
  have ht := t_pos hx
  have hj := J_le_third_drift hx
  have hm := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ 4*k x*(k x+1/3)*t x by positivity)
  have hq : 0 ≤ k x^2-2*k x/3-2/9 := by
    have hp := mul_nonneg (show 0 ≤ k x-5/4 by linarith only [hk])
      (show 0 ≤ k x+7/12 by linarith only [hk])
    nlinarith only [hp]
  have hn := mul_nonneg (show 0 ≤ 2*u x*k x*t x by positivity) hq
  rw [hd.deriv]
  nlinarith only [hm, hn]

theorem kineticGap_antitone : AntitoneOn kineticGap (Ici 0) := by
  have hd (x : ℝ) (hx : 0 ≤ x) : DifferentiableAt ℝ kineticGap x :=
    ((dk hx).differentiableAt.pow 2).mul (dt hx).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (show 0 ≤ x from (show 0 < x by simpa [interior_Ici] using hx).le)).differentiableWithinAt)
  intro x hx
  exact kineticGap_deriv_nonpos (show 0 ≤ x from (show 0 < x by simpa [interior_Ici] using hx).le)

/-- Uniform rational bound inherited from the self-dual source value. -/
theorem kineticGap_lt {x : ℝ} (hx : 0 ≤ x) : k x^2*t x < 361/25 := by
  have h0 : k 0 = thetaCuspSelfDualModularScale^2/12-1/3 := by
    simp [k, t, u, A, thetaCuspModularGapAmplitude_zero]
    ring
  have hs := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths
  have hk : k 0 < 19/15 := by rw [h0]; linarith only [hs]
  have hkp := k_gt_fiveFourths (show (0 : ℝ) ≤ 0 by rfl)
  have hsquare := mul_self_lt_mul_self (show 0 ≤ k 0 by linarith only [hkp]) hk
  have hmono := kineticGap_antitone (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  have ht0 : t 0=9 := by simp [t,u]
  dsimp [kineticGap] at hmono
  rw [ht0] at hmono
  nlinarith only [hmono, hsquare]

end
end RHTower.ThetaCuspModularRatio
