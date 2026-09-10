import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyFloor

/-! # A global ratio bound for the actual modular theta orbit

The complete source orbit forces its gap-to-drift ratio to be nondecreasing.
The resulting shear bound constrains the native reflection-jet coordinates;
positivity of the rank-seven signed form is a separate, unresolved question.
-/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open RHTower

abbrev u := thetaCuspModularMassDrift
abbrev A := thetaCuspModularGapAmplitude
abbrev w := thetaCuspModularTransverseShear
def t (x : ℝ) : ℝ := 9-u x^2
def k (x : ℝ) : ℝ := 3*(A x/t x)/4-1/3
def J (x : ℝ) : ℝ := u x*k x-w x
def D (x : ℝ) : ℝ := t x-6/k x-4/k x^2

theorem t_pos {x : ℝ} (hx : 0 ≤ x) : 0 < t x := by
  have h0 := thetaCuspModularMassDrift_nonneg hx
  have h3 := thetaCuspModularMassDrift_lt_three hx
  dsimp [t]
  nlinarith

theorem kt {x : ℝ} (hx : 0 ≤ x) : k x*t x = 3*A x/4-t x/3 := by
  have ht := (t_pos hx).ne'
  dsimp [k]
  field_simp [ht]

theorem k_gt {x : ℝ} (hx : 0 ≤ x) : 2/3 < k x := by
  have hE := thetaCuspModularStrongEnergy_gt_twelve hx
  have he := kt hx
  have ht := t_pos hx
  by_contra hn
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) ht.le
  dsimp [t, u, A] at he hm hE
  nlinarith

theorem du {x : ℝ} (hx : 0 ≤ x) : HasDerivAt u (k x*t x) x := by
  convert hasDerivAt_thetaCuspModularMassDrift x using 1
  rw [kt hx]
  dsimp [t]
  ring

theorem dt {x : ℝ} (hx : 0 ≤ x) : HasDerivAt t (-2*u x*k x*t x) x := by
  convert ((du hx).pow 2).const_sub 9 using 1 <;> first | rfl | ring

theorem dk {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt k (2*(k x+1/3)*J x) x := by
  have ht := (t_pos hx).ne'
  convert ((((hasDerivAt_thetaCuspModularGapAmplitude x).div (dt hx) ht).const_mul 3).div_const 4).sub_const (1/3 : ℝ) using 1
  all_goals first | rfl | (dsimp [k, J]; field_simp [ht]; ring)

theorem dw {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt w (4+6*k x-2*u x*J x/3) x := by
  have ht := (t_pos hx).ne'
  have he := kt hx
  convert hasDerivAt_thetaCuspModularTransverseShear x using 1
  dsimp [J, t, u, A, w, thetaCuspModularMassDrift] at he ⊢
  nlinarith [he]

theorem dJ {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt J (k x^2*D x+2*u x*(k x+2/3)*J x) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert ((du hx).mul (dk hx)).sub (dw hx) using 1
  all_goals first | rfl | (dsimp [D]; field_simp [hk]; ring)

theorem dD {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt D
      (-2*u x*k x*t x+2*(k x+1/3)*(6/k x^2+8/k x^3)*J x) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert ((dt hx).sub ((hasDerivAt_const x (6 : ℝ)).div (dk hx) hk)).sub
    ((hasDerivAt_const x (4 : ℝ)).div ((dk hx).pow 2) (pow_ne_zero 2 hk)) using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; field_simp [hk]; ring)

theorem dD_neg {x : ℝ} (hx : 0 < x) (hJ : J x ≤ 0) :
    deriv D x < 0 := by
  rw [(dD hx.le).deriv]
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx.le)
  have ht := t_pos hx.le
  have hneg : -2*u x*k x*t x < 0 := by
    have hp : 0 < 2*u x*k x*t x := by positivity
    nlinarith only [hp]
  have hc : 0 ≤ 2*(k x+1/3)*(6/k x^2+8/k x^3) := by positivity
  exact add_neg_of_neg_of_nonpos hneg (mul_nonpos_of_nonneg_of_nonpos hc hJ)

theorem dJ_neg {x : ℝ} (hx : 0 < x) (hJ : J x < 0) (hD : D x ≤ 0) :
    deriv J x < 0 := by
  rw [(dJ hx.le).deriv]
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx.le)
  have hc : 0 < 2*u x*(k x+2/3) := by positivity
  exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD)
    (mul_neg_of_pos_of_neg hc hJ)

open Set Filter Topology

theorem J_zero : J 0 = 0 := by
  simp [J, u, w, thetaCuspModularTransverseShear, thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]

theorem D_neg_of_J_neg {b : ℝ} (hb : 0 < b) (hJb : J b < 0) : D b < 0 := by
  have hc : ContinuousOn J (Icc 0 b) :=
    fun x hx => (dJ hx.1).continuousAt.continuousWithinAt
  let S : Set ℝ := Icc 0 b ∩ J ⁻¹' {0}
  have hs : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hne : S.Nonempty := ⟨0, ⟨⟨le_rfl, hb.le⟩, J_zero⟩⟩
  obtain ⟨a, ha, hmax⟩ := hs.exists_isGreatest hne
  have ha0 : 0 ≤ a := ha.1.1
  have haz : J a = 0 := ha.2
  have hab : a < b := by
    have hal : a ≤ b := ha.1.2
    rcases hal.eq_or_lt with heq | hlt
    · subst a
      exact False.elim ((ne_of_lt hJb) haz)
    · exact hlt
  have hneg : ∀ y ∈ Ioc a b, J y < 0 := by
    intro y hy
    by_contra hny
    have hJy : 0 ≤ J y := le_of_not_gt hny
    have hcy : ContinuousOn J (Icc y b) := fun z hz =>
      (dJ (ha0.trans (hy.1.le.trans hz.1))).continuousAt.continuousWithinAt
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hy.2 hcy ⟨hJb.le, hJy⟩
    have hzS : z ∈ S := ⟨⟨ha0.trans (hy.1.le.trans hz.1), hz.2⟩, hz0⟩
    have hza := hmax hzS
    linarith [hz.1, hy.1]
  have hdja : k a^2*D a+2*u a*(k a+2/3)*J a ≤ 0 := by
    apply le_of_tendsto ((dJ ha0).tendsto_slope.mono_left (nhdsGT_le_nhdsNE a))
    have hlt : ∀ᶠ y in 𝓝[>] a, y < b :=
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with y hy hyb
    have hjy := hneg y ⟨hy, hyb.le⟩
    rw [slope_def_field, haz, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg hjy.le (sub_pos.mpr hy).le
  have hDa : D a ≤ 0 := by
    have hka : 0 < k a := lt_trans (by norm_num) (k_gt ha0)
    simp only [haz, mul_zero, add_zero] at hdja
    by_contra hn
    have hp := mul_pos (sq_pos_of_pos hka) (lt_of_not_ge hn)
    exact (not_lt_of_ge hdja) hp
  have hanti : StrictAntiOn D (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b)
      (fun x hx => (dD (ha0.trans hx.1)).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    exact dD_neg (lt_of_le_of_lt ha0 hx.1) (hneg x ⟨hx.1, hx.2.le⟩).le
  exact (hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).trans_le hDa

theorem J_deriv_neg_of_neg {x : ℝ} (hx : 0 < x) (hJx : J x < 0) : deriv J x < 0 :=
  dJ_neg hx hJx (D_neg_of_J_neg hx hJx).le

theorem J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ J x := by
  by_contra hn
  have hJx : J x < 0 := lt_of_not_ge hn
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with heq | hlt
    · subst x
      simp [J_zero] at hJx
    · exact hlt
  have hbound : ∀ y, x ≤ y → J y ≤ J x := by
    intro y hxy
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := J) (f' := fun z => k z^2*D z+2*u z*(k z+2/3)*J z)
      (a := x) (b := y)
      (fun z hz => (dJ (hx.trans hz.1)).continuousAt.continuousWithinAt)
      (fun z hz => (dJ (hx.trans hz.1)).hasDerivWithinAt)
      (B := fun _ => J x) (B' := fun _ => 0) le_rfl
      (fun z => hasDerivAt_const z (J x)) ?_ ⟨hxy, le_rfl⟩
    intro z hz heq
    have hd := J_deriv_neg_of_neg (lt_of_lt_of_le hx0 hz.1) (by simpa [heq] using hJx)
    rwa [(dJ (hx.trans hz.1)).deriv] at hd
  have hkbound : ∀ y, x ≤ y → 2*(k y+1/3)*J y ≤ 2*J x := by
    intro y hxy
    have hj := hbound y hxy
    have hky := k_gt (hx.trans hxy)
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ k y-2/3 by linarith) (hj.trans hJx.le)
    nlinarith only [hm, hj]
  have ha : AntitoneOn (fun y => k y-(2*J x)*y) (Ici x) := by
    have hd (y : ℝ) (hy : x ≤ y) : HasDerivAt (fun z => k z-(2*J x)*z)
        (2*(k y+1/3)*J y-2*J x) y := by
      convert (dk (hx.trans hy)).sub ((hasDerivAt_id y).const_mul (2*J x)) using 1
      all_goals first | rfl | simp
    apply antitoneOn_of_deriv_nonpos (convex_Ici x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (by simpa [interior_Ici] using (le_of_lt (show x < y by simpa [interior_Ici] using hy)))).differentiableAt.differentiableWithinAt)
    intro y hy
    have hxy : x ≤ y := (show x < y by simpa [interior_Ici] using hy).le
    rw [(hd y hxy).deriv]
    exact sub_nonpos.mpr (hkbound y hxy)
  let b := x+(k x+1)/(-2*J x)
  have hden : 0 < -2*J x := by nlinarith only [hJx]
  have hkx : 0 < k x := lt_trans (by norm_num) (k_gt hx)
  have hxb : x ≤ b := by
    dsimp [b]
    have hp : 0 ≤ (k x+1)/(-2*J x) := div_nonneg (by linarith) hden.le
    linarith
  have hab := ha (show x ∈ Ici x by simp) (show b ∈ Ici x by exact hxb) hxb
  have hi : (2*J x)*(b-x) = -(k x+1) := by
    dsimp [b]
    field_simp [hJx.ne]
    ring
  have hkb : 0 < k b := lt_trans (by norm_num) (k_gt (hx.trans hxb))
  nlinarith only [hab, hi, hkb]

/-- The actual modular speed is nondecreasing on the positive ray. -/
theorem k_mono : MonotoneOn k (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (dk hx).continuousAt.continuousWithinAt)
    (fun x hx => (dk (show 0 ≤ x from (show 0 < x by simpa [interior_Ici] using hx).le)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx0 : 0 ≤ x := (show 0 < x by simpa [interior_Ici] using hx).le
  rw [(dk hx0).deriv]
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx0)
  have hj := J_nonneg hx0
  positivity

private theorem k_zero : k 0 = A 0/12-1/3 := by
  simp [k, t, u]
  ring

/-- The gap amplitude divided by the actual remaining drift gap is nondecreasing. -/
theorem ratio_mono : MonotoneOn (fun x => A x/(9-u x^2)) (Ici 0) := by
  intro x hx y hy hxy
  have hm := k_mono hx hy hxy
  dsimp [k, t] at hm
  linarith only [hm]

/-- A global lower bound retaining the exact self-dual source amplitude. -/
theorem gap_lower {x : ℝ} (hx : 0 ≤ x) :
    A 0*(9-u x^2)/9 ≤ A x := by
  have hm := mul_le_mul_of_nonneg_right
    (k_mono (show 0 ∈ Ici (0 : ℝ) by simp) hx hx) (t_pos hx).le
  rw [k_zero] at hm
  have he := kt hx
  dsimp [t] at hm he
  nlinarith only [hm, he]

/-- The native transverse shear is bounded by the same global ratio. -/
theorem shear_upper {x : ℝ} (hx : 0 ≤ x) :
    w x ≤ u x*(3*(A x/(9-u x^2))/4-1/3) := by
  have hj := J_nonneg hx
  dsimp [J, k, t] at hj
  linarith only [hj]

end
end RHTower.ThetaCuspModularRatio
