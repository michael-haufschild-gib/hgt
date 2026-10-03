import GaloisForLFunctions.RHTower.ThetaTailGaussianCoarea

/-! Strict submodularity of the actual theta potential in Gaussian coarea.
Comparison amplitudes above every nonnegative anchor decrease in the common mass. -/

noncomputable section
open Set
namespace RHTower.ThetaGaussianCoarea

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem positive_after {f g : ℝ → ℝ} {x z : ℝ}
    (hf : ∀ s, x ≤ s → HasDerivAt f (g s) s) (hx : f x=0)
    (hg : ∀ s, x < s → 0 < g s) (hxz : x < z) : 0 < f z := by
  have hm : StrictMonoOn f (Ici x) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro s hs; exact (hf s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hxs : x < s := by simpa only [interior_Ici,mem_Ioi] using hs
      rw [(hf s hxs.le).deriv]
      exact hg s hxs
  have h := hm (show x ∈ Ici x by simp) hxz.le hxz
  rwa [hx] at h

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem curvature_strictMono : StrictMonoOn c (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t _; exact (hasDerivAt_thetaCuspLogCurvature t).continuousAt.continuousWithinAt
  · intro t ht
    rw [(hasDerivAt_thetaCuspLogCurvature t).deriv]
    exact thetaCuspLogCurvatureJet_pos_of_pos (by simpa only [interior_Ici,mem_Ioi] using ht)

private theorem tangent_gap {t : ℝ} (ht : 0 < t) : 0 < t*c t-p t := by
  apply positive_after (g := fun s => s*v s) ?_ ?_ ?_ ht
  · intro s _
    convert! ((hasDerivAt_id s).mul (hasDerivAt_thetaCuspLogCurvature s)).sub
      (hasDerivAt_thetaCuspLogDecaySlope s) using 1
    dsimp; ring
  · simp only [zero_mul,p_zero,sub_self]
  · intro s hs; exact mul_pos hs (thetaCuspLogCurvatureJet_pos_of_pos hs)

private theorem curvature_tangent_gap {t : ℝ} (ht : 0 < t) :
    0 < c 0-c t+t*v t := by
  apply positive_after (g := fun s => s*a s) ?_ ?_ ?_ ht
  · intro s _
    convert! ((hasDerivAt_const s (c 0)).sub (hasDerivAt_thetaCuspLogCurvature s)).add
      ((hasDerivAt_id s).mul (hasDerivAt_thetaCuspLogCurvatureJet s)) using 1
    dsimp; ring
  · simp only [sub_self,zero_mul,add_zero]
  · intro s hs; exact mul_pos hs (thetaCuspLogCurvatureJetTwo_pos_all s)

private theorem curvature_trapezoid {t : ℝ} (ht : 0 < t) :
    0 < t*(c 0+c t)-2*p t := by
  apply positive_after (g := fun s => c 0-c s+s*v s) ?_ ?_ ?_ ht
  · intro s _
    convert! ((hasDerivAt_id s).mul
      ((hasDerivAt_thetaCuspLogCurvature s).const_add (c 0))).sub
      ((hasDerivAt_thetaCuspLogDecaySlope s).const_mul 2) using 1
    dsimp; ring
  · simp only [zero_mul,p_zero,mul_zero,sub_self]
  · exact fun s hs => curvature_tangent_gap hs

/-- Strict sign of the numerator in the mixed coarea derivative. -/
theorem mixed_margin_pos {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    0 < (s+r)*(c s+c r)-2*(p s+p r) := by
  have hcS := curvature_strictMono.monotoneOn (show (0:ℝ) ∈ Ici 0 by simp) hs.le hs.le
  have hcR := curvature_strictMono.monotoneOn (show (0:ℝ) ∈ Ici 0 by simp) hr.le hr.le
  have h1 := mul_nonneg hs.le (sub_nonneg.mpr hcR)
  have h2 := mul_nonneg hr.le (sub_nonneg.mpr hcS)
  nlinarith only [curvature_trapezoid hs,curvature_trapezoid hr,h1,h2]

theorem length_hasDerivAt_left (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => length z y u) ((x+y)/length x y u) x := by
  have hd := ((((hasDerivAt_id x).add_const y).pow 2).add_const (4*u)).sqrt
    (ne_of_gt (by nlinarith [sq_nonneg (x+y)] : 0 < (x+y)^2+4*u))
  convert! hd using 1
  dsimp only [length,Pi.pow_apply,id_eq]
  field_simp [(show Real.sqrt ((x+y)^2+4*u) ≠ 0 from (length_pos x y hu).ne')]
  ring

theorem shift_hasDerivAt_left (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => shift z y u) (-shift x y u/length x y u) x := by
  convert! (((length_hasDerivAt_left x y hu).sub (hasDerivAt_id x)).sub_const y).div_const 2 using 1
  unfold shift
  field_simp [(length_pos x y hu).ne']
  ring

theorem shift_hasDerivAt_right (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => shift x z u) (-shift x y u/length x y u) y := by
  have hf : (fun z => shift x z u)=(fun z => shift z x u) := by
    funext z
    unfold shift length
    rw [add_comm x z]
    ring
  have hL : length y x u=length x y u := by simp only [length,add_comm y x]
  have htEq : shift y x u=shift x y u := by
    unfold shift length
    rw [add_comm y x]
    ring
  rw [hf]
  simpa only [← hf,hL,htEq] using shift_hasDerivAt_left y x hu

theorem length_hasDerivAt_right (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => length x z u) ((x+y)/length x y u) y := by
  simpa only [length,add_comm] using length_hasDerivAt_left y x hu

theorem shift_hasDerivAt_mass (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (shift x y) (1/length x y u) u := by
  have hd := (((hasDerivAt_id u).const_mul 4).const_add ((x+y)^2)).sqrt
    (ne_of_gt (by nlinarith [sq_nonneg (x+y)] : 0 < (x+y)^2+4*u))
  convert! ((hd.sub_const x).sub_const y).div_const 2 using 1
  dsimp only [length,id_eq]
  field_simp [(show Real.sqrt ((x+y)^2+4*u) ≠ 0 from (length_pos x y hu).ne')]
  ring

/-- Derivative with respect to the first endpoint, with coarea mass fixed. -/
def leftDerivative (x y u : ℝ) : ℝ :=
  p (x+shift x y u)-p x-
    shift x y u*(p (x+shift x y u)+p (y+shift x y u))/length x y u

theorem potential_hasDerivAt_left (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => potential z y u) (leftDerivative x y u) x := by
  have ht := shift_hasDerivAt_left x y hu
  have hs := (ThetaCoordinate.sourcePotential_hasDerivAt (x+shift x y u)).comp x
    ((hasDerivAt_id x).add ht)
  have hr := (ThetaCoordinate.sourcePotential_hasDerivAt (y+shift x y u)).comp x
    (ht.const_add y)
  convert! ((hs.add hr).sub (ThetaCoordinate.sourcePotential_hasDerivAt x)).sub_const
    (ThetaCoordinate.sourcePotential y) using 1
  unfold leftDerivative
  ring

/-- The exact mixed derivative retains the whole source curvature margin. -/
theorem leftDerivative_hasDerivAt_right (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => leftDerivative x z u)
      (-u*((x+y+2*shift x y u)*(c (x+shift x y u)+c (y+shift x y u))-
        2*(p (x+shift x y u)+p (y+shift x y u)))/length x y u^3) y := by
  have ht := shift_hasDerivAt_right x y hu
  have hs := (hasDerivAt_thetaCuspLogDecaySlope (x+shift x y u)).comp y (ht.const_add x)
  have hr := (hasDerivAt_thetaCuspLogDecaySlope (y+shift x y u)).comp y
    ((hasDerivAt_id y).add ht)
  convert! (hs.sub_const (p x)).sub
    ((ht.mul (hs.add hr)).div (length_hasDerivAt_right x y hu) (length_pos x y hu).ne') using 1
  have huEq : u=shift x y u*(shift x y u+x+y) := (coordinate_shift hu.le).symm
  have hsum := length_eq x y u
  dsimp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  field_simp [(length_pos x y hu).ne']
  generalize shift x y u=t at *
  rw [hsum,huEq]
  ring

private theorem leftDerivative_strictAnti {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) :
    StrictAntiOn (fun y => leftDerivative x y u) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro y _; exact (leftDerivative_hasDerivAt_right x y hu).continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ici,mem_Ioi] using hy
    have ht := shift_pos hx hy0.le hu
    rw [(leftDerivative_hasDerivAt_right x y hu).deriv]
    have hm := mixed_margin_pos (show 0 < x+shift x y u by linarith)
      (show 0 < y+shift x y u by linarith)
    have hm' : 0 < (x+y+2*shift x y u)*(c (x+shift x y u)+c (y+shift x y u))-
        2*(p (x+shift x y u)+p (y+shift x y u)) := by nlinarith only [hm]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hu) hm')
      (pow_pos (length_pos x y hu) 3)

/-- Strict rectangle comparison above an arbitrary nonnegative anchor. -/
theorem potential_submodular_at {b x y u : ℝ} (hb : 0 ≤ b)
    (hx : b < x) (hy : b < y) (hu : 0 < u) :
    potential x y u+potential b b u < potential b x u+potential b y u := by
  have h : 0 < (potential x b u-potential x y u)-(potential b b u-potential b y u) := by
    apply positive_after (g := fun z => leftDerivative z b u-leftDerivative z y u) ?_ ?_ ?_ hx
    · intro z _
      exact ((potential_hasDerivAt_left z b hu).sub (potential_hasDerivAt_left z y hu)).sub_const _
    · ring
    · intro z hz
      exact sub_pos.mpr (leftDerivative_strictAnti (hb.trans hz.le) hu hb (hb.trans hy.le) hy)
  rw [potential_comm x b u] at h
  linarith only [h]

/-- Strict rectangle comparison for actual finite endpoints. -/
theorem potential_submodular {x y u : ℝ} (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) :
    potential x y u+potential 0 0 u < potential 0 x u+potential 0 y u :=
  potential_submodular_at (le_refl (0:ℝ)) hx hy hu

/-- Mass derivative of the coarea potential. -/
def massRate (x y u : ℝ) : ℝ :=
  (p (x+shift x y u)+p (y+shift x y u))/length x y u

theorem potential_hasDerivAt_mass (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (potential x y) (massRate x y u) u := by
  have ht := shift_hasDerivAt_mass x y hu
  have hs := (ThetaCoordinate.sourcePotential_hasDerivAt (x+shift x y u)).comp u
    (ht.const_add x)
  have hr := (ThetaCoordinate.sourcePotential_hasDerivAt (y+shift x y u)).comp u
    (ht.const_add y)
  convert! ((hs.add hr).sub_const (ThetaCoordinate.sourcePotential x)).sub_const
    (ThetaCoordinate.sourcePotential y) using 1
  unfold massRate
  ring

/-- Moving the larger endpoint retains an additional anchor-curvature contribution. -/
theorem massRate_hasDerivAt_right (b x : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y => massRate b y u)
      ((length b x u*((b+x+shift b x u)*c (x+shift b x u)-
        shift b x u*c (b+shift b x u))-
        (b+x)*(p (b+shift b x u)+p (x+shift b x u)))/length b x u^3) x := by
  have ht := shift_hasDerivAt_right b x hu
  have hs := (hasDerivAt_thetaCuspLogDecaySlope (b+shift b x u)).comp x (ht.const_add b)
  have hr := (hasDerivAt_thetaCuspLogDecaySlope (x+shift b x u)).comp x
    ((hasDerivAt_id x).add ht)
  convert! (hs.add hr).div (length_hasDerivAt_right b x hu) (length_pos b x hu).ne' using 1
  dsimp only [Pi.add_apply,Function.comp_apply,id_eq]
  field_simp [(length_pos b x hu).ne']
  rw [length_eq b x u]
  ring

theorem massRate_strictMono_above {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    StrictMonoOn (fun x => massRate b x u) (Ici b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _; exact (massRate_hasDerivAt_right b x hu).continuousAt.continuousWithinAt
  · intro x hx
    have hbx : b < x := by simpa only [interior_Ici,mem_Ioi] using hx
    have ht := shift_pos hb (hb.trans hbx.le) hu
    have hs : 0 < b+shift b x u := by linarith
    have hr : 0 < x+shift b x u := by linarith
    have hcr := curvature_strictMono hs.le hr.le
      (by linarith : b+shift b x u < x+shift b x u)
    have hprod := mul_pos hs (sub_pos.mpr hcr)
    have hsum : 0 < length b x u*c (x+shift b x u)-
        (p (b+shift b x u)+p (x+shift b x u)) := by
      rw [length_eq b x u]
      nlinarith only [tangent_gap hs,tangent_gap hr,hprod]
    have hm := mul_nonneg hb (mixed_margin_pos hs hr).le
    have hfirst := mul_pos (sub_pos.mpr hbx) hsum
    have hsecond := mul_pos (length_pos b x hu) hprod
    have hnum : 0 < length b x u*((b+x+shift b x u)*c (x+shift b x u)-
        shift b x u*c (b+shift b x u))-
        (b+x)*(p (b+shift b x u)+p (x+shift b x u)) := by
      rw [length_eq b x u] at hfirst hsecond ⊢
      nlinarith only [hfirst,hsecond,hm]
    rw [(massRate_hasDerivAt_right b x hu).deriv]
    exact div_pos hnum (pow_pos (length_pos b x hu) 3)

/-- Comparison against any nonnegative diagonal anchor in the common coarea mass. -/
def anchoredAmplitude (b x u : ℝ) : ℝ := Real.exp (potential b b u-potential b x u)

theorem anchoredAmplitude_pos (b x u : ℝ) : 0 < anchoredAmplitude b x u := Real.exp_pos _

theorem anchoredAmplitude_continuous (b x : ℝ) : Continuous (anchoredAmplitude b x) :=
  Real.continuous_exp.comp ((potential_continuous b b).sub (potential_continuous b x))

theorem anchoredAmplitude_zero {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    anchoredAmplitude b x 0=1 := by
  simp only [anchoredAmplitude,potential_zero hb hb,potential_zero hb hx,sub_self,Real.exp_zero]

theorem anchoredAmplitude_strictAnti {b x : ℝ} (hb : 0 ≤ b) (hx : b < x) :
    StrictAntiOn (anchoredAmplitude b x) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact (anchoredAmplitude_continuous b x).continuousOn
  · intro u hu
    have hu0 : 0 < u := by simpa only [interior_Ici,mem_Ioi] using hu
    have hd : HasDerivAt (anchoredAmplitude b x)
        (Real.exp (potential b b u-potential b x u)*(massRate b b u-massRate b x u)) u := by
      convert! ((potential_hasDerivAt_mass b b hu0).sub
        (potential_hasDerivAt_mass b x hu0)).exp using 1
    rw [hd.deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr
      (massRate_strictMono_above hb hu0 (show b ∈ Ici b from le_refl b) hx.le hx))

theorem anchoredAmplitude_le_one {b x u : ℝ} (hb : 0 ≤ b) (hx : b < x) (hu : 0 ≤ u) :
    anchoredAmplitude b x u ≤ 1 := by
  have h := (anchoredAmplitude_strictAnti hb hx).antitoneOn (show (0:ℝ) ∈ Ici 0 by simp) hu hu
  rwa [anchoredAmplitude_zero hb (hb.trans hx.le)] at h

theorem density_anchored_product_lt {b x y u : ℝ} (hb : 0 ≤ b)
    (hx : b < x) (hy : b < y) (hu : 0 < u) :
    density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u < density x y u := by
  have he : density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u =
      Real.exp (potential b b u-potential b x u-potential b y u) := by
    unfold density anchoredAmplitude
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [he,density,Real.exp_lt_exp]
  linarith only [potential_submodular_at hb hx hy hu]

/-- Both center comparison amplitudes move in the same direction under the common mass. -/
def amplitude (x u : ℝ) : ℝ := Real.exp (potential 0 0 u-potential 0 x u)

theorem amplitude_pos (x u : ℝ) : 0 < amplitude x u := Real.exp_pos _

theorem amplitude_continuous (x : ℝ) : Continuous (amplitude x) :=
  Real.continuous_exp.comp ((potential_continuous 0 0).sub (potential_continuous 0 x))

theorem amplitude_zero {x : ℝ} (hx : 0 ≤ x) : amplitude x 0=1 := by
  simp only [amplitude,potential_zero (le_refl (0:ℝ)) hx,
    potential_zero (le_refl (0:ℝ)) (le_refl (0:ℝ)),sub_self,Real.exp_zero]

theorem amplitude_strictAnti {x : ℝ} (hx : 0 < x) : StrictAntiOn (amplitude x) (Ici 0) := by
  exact anchoredAmplitude_strictAnti (le_refl (0:ℝ)) hx

theorem amplitude_le_one {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) : amplitude x u ≤ 1 := by
  have h := (amplitude_strictAnti hx).antitoneOn (show (0:ℝ) ∈ Ici 0 by simp) hu hu
  rwa [amplitude_zero hx.le] at h

/-- The actual finite-pair density strictly dominates its center-product comparison. -/
theorem density_center_product_lt {x y u : ℝ} (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) :
    density 0 0 u*amplitude x u*amplitude y u < density x y u := by
  exact density_anchored_product_lt (le_refl (0:ℝ)) hx hy hu

end RHTower.ThetaGaussianCoarea
