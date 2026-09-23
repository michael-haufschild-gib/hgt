import GaloisForLFunctions.RHTower.ThetaCuspModularGapScaledBarrier

/-!
# An explicit cost bound for the complete modular barrier flux

The normalized slope defect satisfies `B/T ≤ u/36 ≤ x/3`. Its drift
comparison has monotone forcing, so any positive comparison defect would
violate either the initial boundary or the bounded complete orbit.

The resulting estimate controls the actual zero-integral flux correction:
its adverse part is at most `504/169` times the weighted full-source square.
This makes the inner correction cost explicit. The separate native determinant
margin and a globally compatible repair coefficient remain unproved.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.ThetaCuspModularRatio
noncomputable section

/-- The actual slope defect divided by its positive modular gap. -/
def normalizedDefect (x : ℝ) : ℝ := barrierDefect x/(t x*(k x+1/3))

private theorem dNormalized {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedDefect
      (4/3-k x+(4*u x*(k x+1/3)-2*J x)*normalizedDefect x) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  have ht := (t_pos hx).ne'
  have hk1 : k x+1/3 ≠ 0 := by have := k_gt hx; linarith
  have hk3 : 1+k x*3 ≠ 0 := by have := k_gt hx; linarith
  have hb := ((du hx).div_const 3).sub (dJ hx)
  convert hb.div ((dt hx).mul ((dk hx).add_const (1/3 : ℝ))) (mul_ne_zero ht hk1) using 1
  all_goals first | rfl | (dsimp [normalizedDefect, barrierDefect, D, t] at *; field_simp [hk, ht, hk1, hk3]; ring_nf; field_simp [hk3]; ring)

/-- Difference between the normalized defect and the drift comparison. -/
def normalizedDriftDefect (x : ℝ) : ℝ := normalizedDefect x-u x/36

/-- Forcing in the normalized drift comparison equation. -/
def normalizedDriftForcing (x : ℝ) : ℝ :=
  4/3-5*k x*t x/36+u x^(2 : ℕ)/27-u x*J x/18

private theorem dNormalizedDrift {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedDriftDefect
      ((4*u x*(k x+1/3)-2*J x)*normalizedDriftDefect x+normalizedDriftForcing x) x := by
  convert (dNormalized hx).sub ((du hx).div_const 36) using 1
  all_goals first | rfl | (dsimp [normalizedDriftDefect, normalizedDriftForcing, t]; ring)

private theorem dNormalizedForcing {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedDriftForcing
      (u x*t x*(36*k x^(2 : ℕ)-1)/162+
        (u x/3-J x)*(t x*(k x/3+5/54)+u x^(2 : ℕ)*(k x+2/3)/9)) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert (((((dk hx).mul (dt hx)).const_mul 5).div_const 36).const_sub (4/3 : ℝ)).add
    (((du hx).pow 2).div_const 27) |>.sub (((du hx).mul (dJ hx)).div_const 18) using 1
  all_goals first | rfl |
    (funext y; dsimp [normalizedDriftForcing, t]; ring) |
    (dsimp [normalizedDriftForcing, D, t]; field_simp [hk]; ring)

private theorem normalizedForcing_deriv_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ deriv normalizedDriftForcing x := by
  rw [(dNormalizedForcing hx).deriv]
  have hu := thetaCuspModularMassDrift_nonneg hx
  have ht := t_pos hx
  have hk := k_gt hx
  have hb := J_le_third_drift hx
  have hs : 0 ≤ 36*k x^(2 : ℕ)-1 := by nlinarith only [hk, sq_nonneg (k x-5/4)]
  have hB : 0 ≤ u x/3-J x := sub_nonneg.mpr hb
  have hk1 : 0 ≤ k x/3+5/54 := by linarith only [hk]
  have hk2 : 0 ≤ k x+2/3 := by linarith only [hk]
  positivity

private theorem normalizedForcing_mono : MonotoneOn normalizedDriftForcing (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (dNormalizedForcing hx).continuousAt.continuousWithinAt)
    (fun x hx => (dNormalizedForcing (show 0 ≤ x from
      (show 0 < x by simpa [interior_Ici] using hx).le)).differentiableAt.differentiableWithinAt)
  intro x hx
  exact normalizedForcing_deriv_nonneg (show 0 ≤ x from
    (show 0 < x by simpa [interior_Ici] using hx).le)

private theorem driftCoefficient_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 4*u x*(k x+1/3)-2*J x := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hk := k_gt hx
  have hj := J_le_third_drift hx
  have hm := mul_nonneg hu (show 0 ≤ 4*k x+2/3 by linarith only [hk])
  nlinarith only [hj, hm]

private theorem normalizedDrift_zero : normalizedDriftDefect 0 = 0 := by
  simp [normalizedDriftDefect, normalizedDefect, barrierDefect, J_zero, u]

private theorem normalizedDrift_upper {x : ℝ} (hx : 0 ≤ x) :
    normalizedDriftDefect x ≤ 1 := by
  have h := (normalized_barrierDefect_bounds hx).2
  have hu := thetaCuspModularMassDrift_nonneg hx
  change normalizedDefect x < 1/12 at h
  dsimp [normalizedDriftDefect]
  linarith only [h, hu]

/-- The normalized source defect vanishes at least as fast as the modular drift. -/
theorem normalizedDefect_le_drift {b : ℝ} (hb : 0 ≤ b) :
    normalizedDefect b ≤ u b/36 := by
  suffices normalizedDriftDefect b ≤ 0 by
    dsimp [normalizedDriftDefect] at this
    linarith only [this]
  by_contra hn
  have hFb : 0 < normalizedDriftDefect b := lt_of_not_ge hn
  have hb0 : 0 < b := by
    rcases hb.eq_or_lt with he | he
    · subst b
      simp [normalizedDrift_zero] at hFb
    · exact he
  by_cases hf : normalizedDriftForcing b < 0
  · have hle : normalizedDriftDefect b ≤ 0 := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := normalizedDriftDefect) (f' := deriv normalizedDriftDefect)
        (a := 0) (b := b)
        (fun y hy => (dNormalizedDrift hy.1).continuousAt.continuousWithinAt)
        (fun y hy => (dNormalizedDrift hy.1).differentiableAt.hasDerivAt.hasDerivWithinAt)
        (B := fun _ => 0) (B' := fun _ => 0)
        (by rw [normalizedDrift_zero]) (fun y => hasDerivAt_const y (0 : ℝ)) ?_ ⟨hb, le_rfl⟩
      intro y hy he
      rw [(dNormalizedDrift hy.1).deriv, he, mul_zero, zero_add]
      exact (normalizedForcing_mono hy.1 hb hy.2.le).trans_lt hf
    exact (not_lt_of_ge hle) hFb
  have hf0 : 0 ≤ normalizedDriftForcing b := le_of_not_gt hf
  have hub : 0 < u b := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hb0)
  let c : ℝ := u b*normalizedDriftDefect b
  have hc : 0 < c := mul_pos hub hFb
  have hderiv {y : ℝ} (hy : b ≤ y)
      (hFy : normalizedDriftDefect b ≤ normalizedDriftDefect y) :
      c ≤ deriv normalizedDriftDefect y := by
    have hy0 := hb.trans hy
    have huy := u_mono hb hy0 hy
    have hu0 := thetaCuspModularMassDrift_nonneg hy0
    have hk := k_gt_fiveFourths hy0
    have hj := J_le_third_drift hy0
    have hm := mul_nonneg hu0 (show 0 ≤ 4*k y-1/3 by linarith only [hk])
    have hcoef : u b ≤ 4*u y*(k y+1/3)-2*J y := by
      nlinarith only [hm, huy, hj]
    have hprod := mul_le_mul hcoef hFy hFb.le
      (show 0 ≤ 4*u y*(k y+1/3)-2*J y from driftCoefficient_nonneg hy0)
    have hforce : 0 ≤ normalizedDriftForcing y :=
      hf0.trans (normalizedForcing_mono hb hy0 hy)
    rw [(dNormalizedDrift hy0).deriv]
    exact hprod.trans (le_add_of_nonneg_right hforce)
  have hbound : ∀ x, b ≤ x → normalizedDriftDefect b ≤ normalizedDriftDefect x := by
    intro x hbx
    have h : -normalizedDriftDefect x ≤ -normalizedDriftDefect b := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun y => -normalizedDriftDefect y) (f' := fun y => -deriv normalizedDriftDefect y)
        (a := b) (b := x)
        (fun y hy => (dNormalizedDrift (hb.trans hy.1)).neg.continuousAt.continuousWithinAt)
        (fun y hy => ((dNormalizedDrift (hb.trans hy.1)).differentiableAt.hasDerivAt.neg).hasDerivWithinAt)
        (B := fun _ => -normalizedDriftDefect b) (B' := fun _ => 0)
        le_rfl (fun y => hasDerivAt_const y (-normalizedDriftDefect b)) ?_ ⟨hbx, le_rfl⟩
      intro y hy he
      have hFy : normalizedDriftDefect b ≤ normalizedDriftDefect y := by linarith only [he]
      have hd := hderiv hy.1 hFy
      linarith only [hd, hc]
    linarith only [h]
  have hmono : MonotoneOn (fun y => normalizedDriftDefect y-c*y) (Ici b) := by
    have hd (y : ℝ) (hy : b ≤ y) :
        HasDerivAt (fun z => normalizedDriftDefect z-c*z) (deriv normalizedDriftDefect y-c) y := by
      convert (dNormalizedDrift (hb.trans hy)).differentiableAt.hasDerivAt.sub
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
  have hu := normalizedDrift_upper (hb.trans hbx)
  nlinarith only [hinc, he, hu, hFb]

/-- Explicit linear bound in the original center coordinate. -/
theorem normalizedDefect_le_center {x : ℝ} (hx : 0 ≤ x) :
    normalizedDefect x ≤ x/3 := by
  have hdu {y : ℝ} (hy : 0 ≤ y) : k y*t y < 12 := by
    have hk := k_gt_fiveFourths hy
    have ht := t_pos hy
    have hg := kineticGap_lt hy
    have hp : 0 ≤ k y*t y := mul_nonneg (by linarith only [hk]) ht.le
    have hm := mul_nonneg (show 0 ≤ k y-5/4 by linarith only [hk]) hp
    nlinarith only [hg, hm]
  have hu : u x ≤ 12*x := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := u) (f' := fun y => k y*t y) (a := 0) (b := x)
      (fun y hy => (du hy.1).continuousAt.continuousWithinAt)
      (fun y hy => (du hy.1).hasDerivWithinAt)
      (B := fun y => 12*y) (B' := fun _ => 12)
      (by simp [u]) (fun y => by simpa using (hasDerivAt_id y).const_mul (12 : ℝ))
      (fun y hy _ => hdu hy.1) ⟨hx, le_rfl⟩
  exact (normalizedDefect_le_drift hx).trans (by linarith only [hu])

private theorem gapBound {x : ℝ} (hx : 0 ≤ x) : t x*(k x+1/3) ≤ 72/5 := by
  have he := thetaCuspModularStrongEnergy_lt hx
  have hc := gap_eq_ratio_coordinates hx
  change A x+(4/3 : ℝ)*u x^(2 : ℕ) < 96/5 at he
  nlinarith only [he, hc, sq_nonneg (u x)]

private theorem barrierMass_center_upper {x : ℝ} (hx : 0 ≤ x) :
    barrierMass x ≤ sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*x/3 := by
  have hk := k_gt hx
  have ht := t_pos hx
  have hd : 0 < t x*(k x+1/3) := by positivity
  have hb := (div_le_iff₀ hd).mp (normalizedDefect_le_center hx)
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (sourceAmplitude x))
  dsimp [barrierMass]
  nlinarith only [hm]

private theorem barrierMass_deriv_cost {x : ℝ} (hx : 0 ≤ x) :
    deriv barrierMass x ≤ sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))/12 := by
  have hk := k_gt_fiveFourths hx
  have ht := t_pos hx
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hb := barrierDefect_nonneg hx
  have hneg : u x*(5/3-2*k x)*barrierDefect x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hu (by linarith only [hk])) hb
  have hfirst := mul_le_mul_of_nonneg_left
    (show 4/3-k x ≤ 1/12 by linarith only [hk])
    (show 0 ≤ t x*(k x+1/3) by positivity)
  have hm := mul_le_mul_of_nonneg_left
    (show t x*(k x+1/3)*(4/3-k x)+u x*(5/3-2*k x)*barrierDefect x ≤
      t x*(k x+1/3)/12 by linarith only [hneg, hfirst]) (sq_nonneg (sourceAmplitude x))
  rw [(dBarrierMass hx).deriv]
  linarith only [hm]

private theorem hyperbolicCost (y : ℝ) : y*Real.cosh y ≤ (1+y)*Real.sinh y := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*y)) (Real.exp_pos (-y)).le
  have he : Real.exp (2*y)*Real.exp (-y) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith only [h]

/-- The literal correction has a uniform inner cost in units of the full source square. -/
theorem barrierFlux_deriv_inner_cost {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 0 ≤ x) (hxu : x ≤ 2/3) :
    deriv (barrierFlux a) x ≤
      (504/169 : ℝ)*(4*x*Real.sinh (2*a*x))*thetaCuspFullSource x^(2 : ℕ) := by
  have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
  have hb := barrierMass_nonneg hx
  have hh := hyperbolicCost (2*a*x)
  have ha' : 2*a*x ≤ x := by nlinarith only [mul_le_mul_of_nonneg_right ha hx]
  have hm := mul_le_mul_of_nonneg_right ha' hs
  have hc := mul_le_mul_of_nonneg_right
    (show Real.sinh (2*a*x)+2*a*x*Real.cosh (2*a*x) ≤ (2+x)*Real.sinh (2*a*x) by
      nlinarith only [hh, hm]) hb
  have hm0 := mul_le_mul_of_nonneg_left (barrierMass_center_upper hx)
    (show 0 ≤ (2+x)*Real.sinh (2*a*x) by positivity)
  have hm1 := mul_le_mul_of_nonneg_left (barrierMass_deriv_cost hx) (mul_nonneg hx hs)
  have hT := gapBound hx
  have ht := t_pos hx
  have hk := k_gt_fiveFourths hx
  have hTu : 0 ≤ t x*(k x+1/3) := by positivity
  have hscale : (3/16 : ℝ)+x/12 ≤ 35/144 := by linarith only [hxu]
  have hbound := mul_le_mul hT hscale (by positivity : 0 ≤ (3/16 : ℝ)+x/12)
    (by norm_num : (0 : ℝ) ≤ 72/5)
  have hsource : (169/144 : ℝ)*sourceAmplitude x^(2 : ℕ) ≤ thetaCuspFullSource x^(2 : ℕ) := by
    rw [source_eq_ratio_coordinates hx]
    have hv : (169/144 : ℝ) ≤ (k x-1/6)^(2 : ℕ) := by
      nlinarith only [hk, sq_nonneg (k x-5/4)]
    have hh := mul_le_mul_of_nonneg_left hv (sq_nonneg (sourceAmplitude x))
    nlinarith only [hh]
  have hbudget : sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*((3/16 : ℝ)+x/12) ≤
      (504/169 : ℝ)*thetaCuspFullSource x^(2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hbound (sq_nonneg (sourceAmplitude x))
    nlinarith only [h, hsource]
  have hfinal := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ 4*x*Real.sinh (2*a*x) by positivity)
  rw [(dBarrierFlux hx a).deriv]
  nlinarith only [hc, hm0, hm1, hfinal]

/-- The same explicit cost ceiling holds on the complete actual half-orbit. -/
theorem barrierFlux_deriv_global_cost {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 0 ≤ x) :
    deriv (barrierFlux a) x ≤
      (504/169 : ℝ)*(4*x*Real.sinh (2*a*x))*thetaCuspFullSource x^(2 : ℕ) := by
  rcases le_total x (2/3 : ℝ) with hi | ho
  · exact barrierFlux_deriv_inner_cost ha0 ha hx hi
  · have hd := barrierFlux_deriv_upper ha0 ha ho
    have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
    have hb := barrierMass_nonneg hx
    have hn : -(2/9 : ℝ)*Real.sinh (2*a*x)*barrierMass x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs) hb
    exact (hd.trans hn).trans (by positivity)

/-- Full-orbit flux cost in the same modular coordinates as the native determinant. -/
theorem barrierFlux_deriv_polynomial_cost {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 0 ≤ x) :
    deriv (barrierFlux a) x ≤ 4*x*Real.sinh (2*a*x)*sourceAmplitude x^(2 : ℕ)*
      (t x*(k x+1/3))*((6-3*k x+(u x*(k x-2/3)-J x)/4)/12) := by
  have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
  have hb := barrierMass_nonneg hx
  have hh := hyperbolicCost (2*a*x)
  have ha' : 2*a*x ≤ x := by nlinarith only [mul_le_mul_of_nonneg_right ha hx]
  have hm := mul_le_mul_of_nonneg_right ha' hs
  have hc := mul_le_mul_of_nonneg_right
    (show Real.sinh (2*a*x)+2*a*x*Real.cosh (2*a*x) ≤ (2+x)*Real.sinh (2*a*x) by
      nlinarith only [hh, hm]) hb
  have hm0 := mul_le_mul_of_nonneg_left (barrierMass_center_upper hx)
    (show 0 ≤ (2+x)*Real.sinh (2*a*x) by positivity)
  have hk := k_gt_fiveFourths hx
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hB := barrierDefect_nonneg hx
  have hnegative : u x*(5/3-2*k x)*barrierDefect x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hu (by linarith only [hk])) hB
  have hd : deriv barrierMass x ≤ sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*(4/3-k x) := by
    rw [(dBarrierMass hx).deriv]
    have h := mul_le_mul_of_nonneg_left
      (show t x*(k x+1/3)*(4/3-k x)+u x*(5/3-2*k x)*barrierDefect x ≤
        t x*(k x+1/3)*(4/3-k x) by linarith only [hnegative])
      (sq_nonneg (sourceAmplitude x))
    nlinarith only [h]
  have hm1 := mul_le_mul_of_nonneg_left hd (mul_nonneg hx hs)
  have hcoord : (6+x-3*k x)/12 ≤ (6-3*k x+(u x*(k x-2/3)-J x)/4)/12 := by
    linarith only [center_le_retained_ratio hx]
  have ht := t_pos hx
  rw [(dBarrierFlux hx a).deriv]
  calc
    _ ≤ (2+x)*Real.sinh (2*a*x)*(sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*x/3)+
        x*Real.sinh (2*a*x)*(sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*(4/3-k x)) :=
      add_le_add (hc.trans hm0) hm1
    _ = 4*x*Real.sinh (2*a*x)*sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3))*
        ((6+x-3*k x)/12) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoord (by positivity)



end
end RHTower.ThetaCuspModularRatio
