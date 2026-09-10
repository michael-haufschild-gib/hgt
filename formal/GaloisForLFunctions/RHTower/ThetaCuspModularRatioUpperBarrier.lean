import GaloisForLFunctions.RHTower.ThetaCuspModularRatioMonotonicity

/-!
# A global upper barrier for the complete theta modular ratio

The actual source satisfies `0 ≤ J < 1`, where `J = u * k - w`.
At or above one, the source ODE forces Riccati growth on a complete ray;
the already proved Riccati escape theorem excludes that alternative.
Together with ratio monotonicity this traps the native shear in an interval
of width one. Rank-seven determinant positivity remains a separate goal.
-/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

theorem k_gt_fiveFourths {x : ℝ} (hx : 0 ≤ x) : 5/4 < k x := by
  have hs := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have h0 : k 0 = thetaCuspSelfDualModularScale^2/12-1/3 := by
    simp [k, t, u, A, thetaCuspModularGapAmplitude_zero]
    ring
  have hm := k_mono (show 0 ∈ Ici (0 : ℝ) by simp) hx hx
  rw [h0] at hm
  linarith only [hs, hm]

theorem u_mono : MonotoneOn u (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (du hx).continuousAt.continuousWithinAt)
    (fun x hx => (du (show 0 ≤ x from (show 0 < x by simpa [interior_Ici] using hx).le)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx0 : 0 ≤ x := (show 0 < x by simpa [interior_Ici] using hx).le
  rw [(du hx0).deriv]
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx0)
  exact (mul_pos hk (t_pos hx0)).le

theorem J_le_three_k {x : ℝ} (hx : 0 ≤ x) : J x ≤ 3*k x := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hw := thetaCuspModularMassDrift_le_shear hx
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx)
  have hm := mul_le_mul_of_nonneg_right (thetaCuspModularMassDrift_lt_three hx).le hk.le
  dsimp [J]
  nlinarith only [hu, hw, hm]

theorem J_deriv_boundary_decomposition {x : ℝ} (hx : 0 ≤ x) :
    deriv J x = (3-u x)*((u x+3)*k x^2-2*k x-4/3) +
      2*u x*(k x+2/3)*(J x-1) := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  rw [(dJ hx).deriv]
  dsimp [D, t]
  field_simp [hk]
  ring

theorem J_deriv_boundary_reserve_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < (3-u x)*((u x+3)*k x^2-2*k x-4/3) := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have h3 := thetaCuspModularMassDrift_lt_three hx
  have hk := k_gt_fiveFourths hx
  have hp := mul_nonneg (show 0 ≤ k x-5/4 by linarith)
    (show 0 ≤ 3*k x+7/4 by linarith)
  have hq := mul_nonneg hu (sq_nonneg (k x))
  have hb : 0 < (u x+3)*k x^2-2*k x-4/3 := by nlinarith only [hp,hq]
  exact mul_pos (sub_pos.mpr h3) hb

theorem J_deriv_gt_escape {b x : ℝ} (hb : 0 < b) (hbx : b ≤ x) (hJ : 1 ≤ J x) :
    (2*u b/3)*(J x-1)^2 < deriv J x := by
  have hx : 0 ≤ x := hb.le.trans hbx
  have hub : 0 < u b := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hb)
  have hux := thetaCuspModularMassDrift_nonneg hx
  have huk := u_mono hb.le hx hbx
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx)
  have hm := mul_le_mul_of_nonneg_right huk hk.le
  have hn := mul_le_mul_of_nonneg_left (J_le_three_k hx) hub.le
  have hcoef : (2*u b/3)*(J x-1) ≤ 2*u x*(k x+2/3) := by
    nlinarith only [hm, hn, hub, hux]
  have hmul := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hJ)
  have hpos := J_deriv_boundary_reserve_pos hx
  have he := J_deriv_boundary_decomposition hx
  nlinarith only [hmul, hpos, he]

/-- The actual complete-source ratio defect stays strictly below one. -/
theorem J_lt_one {b : ℝ} (hb : 0 ≤ b) : J b < 1 := by
  by_contra hn
  have hJb : 1 ≤ J b := le_of_not_gt hn
  have hb0 : 0 < b := by
    rcases hb.eq_or_lt with he | he
    · subst b
      rw [J_zero] at hJb
      linarith only [hJb]
    · exact he
  have hbound : ∀ x, b ≤ x → 1 ≤ J x := by
    intro x hbx
    have h : -J x ≤ -1 := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun y => -J y) (f' := fun y => -deriv J y)
        (a := b) (b := x)
        (fun y hy => (dJ (hb.trans hy.1)).neg.continuousAt.continuousWithinAt)
        (fun y hy => ((dJ (hb.trans hy.1)).differentiableAt.hasDerivAt.neg).hasDerivWithinAt)
        (B := fun _ => (-1 : ℝ)) (B' := fun _ => 0)
        (by linarith only [hJb]) (fun y => hasDerivAt_const y (-1 : ℝ)) ?_ ⟨hbx, le_rfl⟩
      intro y hy he
      have hjy : J y = 1 := by linarith only [he]
      have hp := J_deriv_gt_escape (lt_of_lt_of_le hb0 hy.1) le_rfl hjy.ge
      rw [hjy] at hp
      nlinarith only [hp]
    linarith only [h]
  let c : ℝ := 2*u b/3
  have hc : 0 < c := by
    have hu : 0 < u b := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hb0)
    dsimp [c]
    positivity
  let f : ℝ → ℝ := fun s => c*(1-J (b+s))
  have hf (s : ℝ) (hs : 0 < s) : HasDerivAt f (-c*deriv J (b+s)) s := by
    have hy : 0 ≤ b+s := by linarith only [hb, hs]
    have hj := (dJ hy).differentiableAt.hasDerivAt
    have hcomp := hj.comp s ((hasDerivAt_id s).const_add b)
    convert (hcomp.const_sub 1).const_mul c using 1
    all_goals first | rfl | (simp only [mul_one]; ring)
  have hineq (s : ℝ) (hs : 0 < s) : deriv f s < -(f s)^2 := by
    rw [(hf s hs).deriv]
    have hbs : b ≤ b+s := by linarith only [hs]
    have hp := J_deriv_gt_escape hb0 hbs (hbound (b+s) hbs)
    change c*(J (b+s)-1)^2 < deriv J (b+s) at hp
    have hm := mul_lt_mul_of_pos_left hp hc
    dsimp [f]
    nlinarith only [hm]
  have hpos := pos_of_deriv_lt_neg_sq_on_Ioi (f := f)
    (A := 0) (x := 1) (by norm_num)
    (fun s hs => (hf s hs).differentiableAt) hineq
  have hj := hbound (b+1) (by linarith)
  have hf0 : f 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hj)
  exact (not_lt_of_ge hf0) hpos

/-- The full native shear lies in an interval of width one. -/
theorem shear_lower {x : ℝ} (hx : 0 ≤ x) : u x*k x-1 < w x := by
  have h := J_lt_one hx
  dsimp [J] at h
  linarith only [h]

end
end RHTower.ThetaCuspModularRatio
