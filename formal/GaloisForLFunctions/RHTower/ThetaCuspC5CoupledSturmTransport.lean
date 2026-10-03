import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectPrimitiveTransport
import GaloisForLFunctions.RHTower.ThetaCuspC5PositiveDescentIntegral
/-! Finite source comparison for the full C5 descent numerator.
The decreasing projective curvature yields an endpoint square reserve.
Together with exact primitive transport, it makes the affine adjoint
positive and retains sufficient lower-jet mass. A strictly decreasing
source auxiliary then proves the denominator-coupled Sturm inequality
throughout 0<t<=u, using no assumed source signs. Transport through the
remaining Green descent and full C5 compensation are still open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "B" => thetaCuspLogCurvatureJetTwo
local notation "q" => thetaCuspLikelihoodCoordinate


theorem sourceVelocity_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ v x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [thetaCuspLogCurvatureJet,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),neg_zero,le_refl]
  · exact (thetaCuspLogCurvatureJet_pos_of_pos hx).le

theorem sourceDefectJet_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sourceDefectJet x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [sourceDefectJet,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 from ⟨2,rfl⟩),
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),
      mul_zero,sub_self,le_refl]
  · exact (source_defect_pos hx).le

private theorem source_projective_interval_slope {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*c a*B b ≤ c b*(v b-v a) := by
  have hc := thetaCuspLogCurvature_pos b
  have hmono : MonotoneOn (fun x => c b*v x-c a*B b*x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x _
      exact (((hasDerivAt_thetaCuspLogCurvatureJet x).const_mul (c b)).sub
        ((hasDerivAt_id x).const_mul (c a*B b))).continuousAt.continuousWithinAt
    · intro x _
      exact (((hasDerivAt_thetaCuspLogCurvatureJet x).const_mul (c b)).sub
        ((hasDerivAt_id x).const_mul (c a*B b))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxab : x ∈ Icc a b := interior_subset hx
      have hax := sourceCurvature_strictMonoOn.monotoneOn ha (ha.trans hxab.1) hxab.1
      have hrat := projectiveRatio_strictAntiOn.antitoneOn (ha.trans hxab.1)
        (ha.trans hab) hxab.2
      have hcross := (div_le_div_iff₀ hc (thetaCuspLogCurvature_pos x)).mp hrat
      change B b*c x ≤ B x*c b at hcross
      have hd : HasDerivAt (fun z => c b*v z-c a*B b*z)
          (c b*B x-c a*B b) x := by
        convert! ((hasDerivAt_thetaCuspLogCurvatureJet x).const_mul (c b)).sub
          ((hasDerivAt_id x).const_mul (c a*B b)) using 1
        simp only [mul_one]
      rw [hd.deriv]
      have hh := mul_le_mul_of_nonneg_right hax (thetaCuspLogCurvatureJetTwo_pos_all b).le
      nlinarith only [hcross,hh]
  have h := hmono (show a ∈ Icc a b from ⟨le_rfl,hab⟩)
    (show b ∈ Icc a b from ⟨hab,le_rfl⟩) hab
  dsimp only at h
  nlinarith only [h]

/-- Finite endpoint reserve forced by the actual decreasing projective curvature. -/
theorem sourceCurvature_endpoint_reserve {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (b-a)*c a*v b < (c b)^2-(c a)^2 := by
  let Q : ℝ → ℝ := fun x => (c x)^2-(c a)^2-(x-a)*c a*v x
  have hd (x : ℝ) : HasDerivAt Q
      (2*c x*v x-c a*v x-(x-a)*c a*B x) x := by
    convert! (((hasDerivAt_thetaCuspLogCurvature x).pow 2).sub_const ((c a)^2)).sub
      (((((hasDerivAt_id x).sub_const a).mul_const (c a))).mul
        (hasDerivAt_thetaCuspLogCurvatureJet x)) using 1
    dsimp only [id_eq]
    ring
  have hm : StrictMonoOn Q (Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      have hax : a < x := by simpa only [interior_Ici,mem_Ioi] using hx
      rw [(hd x).deriv]
      have hs := source_projective_interval_slope ha hax.le
      have hca := sourceCurvature_strictMonoOn ha (ha.trans hax.le) hax
      have hvx := thetaCuspLogCurvatureJet_pos_of_pos (ha.trans_lt hax)
      have hpos := mul_pos (sub_pos.mpr hca) hvx
      have hnonneg := mul_nonneg (thetaCuspLogCurvature_pos x).le (sourceVelocity_nonneg ha)
      nlinarith only [hs,hpos,hnonneg]
  have h := hm (show a ∈ Ici a from mem_Ici.mpr le_rfl) hab.le hab
  dsimp only [Q] at h
  nlinarith only [h]

/-- The complete source factor combination needed by the coupled adjoint. -/
theorem source_factor_adjoint_reserve {x : ℝ} (hx : 0 ≤ x) :
    factorCurvature (q x)-6*factorLogSlope (q x) < 324 := by
  have hqa := sourceCoordinate_actual_lower hx
  have hpi := Real.pi_gt_d2
  have hq : (8/5:ℝ) ≤ q x := by linarith
  have hq0 : 0 < q x := by linarith
  have hq3 : 0 < q x+3 := by linarith
  have hy : 0 ≤ q x-8/5 := by linarith
  have he : 0 < (324+6*factorLogSlope (q x)-factorCurvature (q x))*((q x)^2*(q x+3)^2) := by
    rw [show q x=(8/5:ℝ)+(q x-8/5) by ring]
    generalize q x-8/5=y at *
    unfold factorCurvature factorLogSlope
    field_simp
    ring_nf
    positivity
  have h := (mul_pos_iff_of_pos_right (by positivity : 0 < (q x)^2*(q x+3)^2)).mp he
  linarith


/-- A finite lower-jet reserve that must be retained during adjoint absorption. -/
theorem source_velocity_square_gap {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    4*((c b)^2-(c a)^2) < (v b)^2-(v a)^2 := by
  have hd (x : ℝ) : HasDerivAt (fun z => (v z)^2-4*(c z)^2)
      (2*v x*curvatureDefect x) x := by
    convert! ((hasDerivAt_thetaCuspLogCurvatureJet x).pow 2).sub
      (((hasDerivAt_thetaCuspLogCurvature x).pow 2).const_mul 4) using 1
    unfold curvatureDefect
    ring
  have hm : StrictMonoOn (fun x => (v x)^2-4*(c x)^2) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
      rw [(hd x).deriv]
      exact mul_pos (mul_pos (by norm_num) (thetaCuspLogCurvatureJet_pos_of_pos hx0))
        (curvatureDefect_pos hx0.le)
  have h := hm ha (ha.trans hab.le) hab
  dsimp only at h
  linarith

theorem sourceDefect_secant_lt_velocity {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (b-a)*curvatureDefect b < v b-v a := by
  have hd (x : ℝ) : HasDerivAt (fun z => v z-curvatureDefect b*z)
      (B x-curvatureDefect b) x := by
    convert! (hasDerivAt_thetaCuspLogCurvatureJet x).sub
      ((hasDerivAt_id x).const_mul (curvatureDefect b)) using 1
    simp only [mul_one]
  have hm : StrictMonoOn (fun x => v x-curvatureDefect b*x) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      have hxab : x ∈ Icc a b := interior_subset hx
      have hB := curvatureDefect_strictAntiOn.antitoneOn (ha.trans hxab.1)
        (ha.trans hab.le) hxab.2
      have hc := thetaCuspLogCurvature_pos x
      rw [(hd x).deriv]
      unfold curvatureDefect at hB ⊢
      linarith
  have h := hm (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hab
  dsimp only at h
  nlinarith only [h]

theorem sourceCoordinate_gt_six_mul {x : ℝ} (hx : 0 ≤ x) : 6*x < q x := by
  have he := Real.add_one_le_exp (x+x)
  rw [Real.exp_add] at he
  have hpos : 0 < x+x+1 := by linarith
  have hpi := mul_lt_mul_of_pos_right Real.pi_gt_three hpos
  have hmul := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  unfold thetaCuspLikelihoodCoordinate
  nlinarith only [hpi,hmul]

theorem sourceDefect_endpoint_weight {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    t*sourceDefectJet (u+t)/2 < 2*c (u+t)+curvatureDefect (u+t)/2 := by
  have ha : 0 ≤ u-t := sub_nonneg.mpr htu
  have hb : 0 < u+t := by linarith
  have hab : u-t < u+t := by linarith
  have hq := thetaCuspLikelihoodCoordinate_pos hb.le
  have hspan : 12*t < q (u+t) := by
    have h := sourceCoordinate_gt_six_mul hb.le
    linarith
  have hrat : 6*t/q (u+t) < (1/2:ℝ) := by
    rw [div_lt_iff₀ hq]
    linarith
  have hbb := curvatureDefect_pos hb.le
  have hs := sourceDefect_secant_lt_velocity ha hab
  have hva := sourceVelocity_nonneg ha
  have hsec : 2*t*curvatureDefect (u+t) < v (u+t) := by nlinarith only [hs,hva]
  have hR := mul_lt_mul_of_pos_right hrat hbb
  have hH := mul_lt_mul_of_pos_left (curvatureDefect_slope_comparison hb.le) (div_pos ht (by norm_num : (0:ℝ)<2))
  have hv := ThetaCurvature.velocityGap_pos hb.le
  have heq : (t/2)*((4+12/q (u+t))*curvatureDefect (u+t)) =
      2*t*curvatureDefect (u+t)+(6*t/q (u+t))*curvatureDefect (u+t) := by ring
  rw [heq] at hH
  nlinarith only [hH,hR,hsec,hv]

def descentAuxiliary (u t : ℝ) : ℝ :=
  8*completedCurvatureEven u t+2*(curvatureDefect (u+t)+curvatureDefect (u-t))-
    t*(sourceDefectJet (u+t)-sourceDefectJet (u-t))/2

theorem descentAuxiliary_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < descentAuxiliary u t := by
  have ha : 0 ≤ u-t := sub_nonneg.mpr htu
  have hb : 0 ≤ u+t := by linarith
  have h := sourceDefect_endpoint_weight ht htu
  have hHa := sourceDefectJet_nonneg ha
  have hta := mul_nonneg ht.le hHa
  have hca := thetaCuspLogCurvature_pos (u-t)
  have hcb := thetaCuspLogCurvature_pos (u+t)
  have hba := curvatureDefect_pos ha
  have hbb := curvatureDefect_pos hb
  unfold descentAuxiliary completedCurvatureEven
  nlinarith only [h,hta,hca,hcb,hba,hbb]


def descentAuxiliaryJet (u t : ℝ) : ℝ :=
  4*(v (u+t)-v (u-t))-
    (5/2)*(sourceDefectJet (u+t)-sourceDefectJet (u-t))-
    t*(sourceDefectJetSlope (u+t)+sourceDefectJetSlope (u-t))/2

def localDescentSturmReserve (u t : ℝ) : ℝ :=
  (18*completedCurvatureEven u t*completedLocalDenominator u t+descentAuxiliary u t)*
      localDescentNumerator u t-
    completedCurvatureOddJet u t*completedLocalDenominator u t*descentAuxiliaryJet u t-
    (completedLocalDenominator u t)^2*(sourceDefectJetSlope (u+t)-sourceDefectJetSlope (u-t))/2

/-- Strict finite-displacement source inequality, with the varying denominator retained. -/
theorem localDescentSturmReserve_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < localDescentSturmReserve u t := by
  let a := u-t
  let b := u+t
  let e := completedCurvatureEven u t
  let n := completedCurvatureOddJet u t
  let p := (v b-v a)/2
  let d := completedLocalDenominator u t
  let J := localDescentNumerator u t
  let k := e^2/c a
  have ha : 0 ≤ a := sub_nonneg.mpr htu
  have hb : 0 < b := by dsimp only [b]; linarith
  have hab : a < b := by dsimp only [a,b]; linarith
  have hca := thetaCuspLogCurvature_pos a
  have hcb := thetaCuspLogCurvature_pos b
  have hca18 := sourceCurvature_gt_eighteen ha
  have hepos : 0 < e := completedCurvatureEven_pos u t
  have hdpos : 0 < d := completedLocalDenominator_pos_nonneg u ht.le
  have hJpos : 0 < J := localDescentNumerator_pos ht htu
  have hva := sourceVelocity_nonneg ha
  have hvb := thetaCuspLogCurvatureJet_pos_of_pos hb
  have hn : 0 < n := by dsimp only [n,completedCurvatureOddJet]; change 0 < (v b+v a)/2; positivity
  have hp : 0 < p := div_pos (sub_pos.mpr (thetaCuspLogCurvatureJet_strictMono hab)) (by norm_num)
  have hba := curvatureDefect_pos ha
  have hbb := curvatureDefect_pos hb.le
  have hcab := sourceCurvature_strictMonoOn ha hb.le hab
  have hea : c a ≤ e := by dsimp only [e,completedCurvatureEven]; change c a ≤ (c b+c a)/2; linarith
  have he18 : 18 < e := hca18.trans_le hea
  have hk : 0 < k := div_pos (sq_pos_of_pos hepos) hca
  have hek : e ≤ k := by
    apply (le_div_iff₀ hca).mpr
    nlinarith only [mul_nonneg hepos.le (sub_nonneg.mpr hea)]
  have hn2 : n < 2*e := by
    have h1 := ThetaCurvature.velocityGap_pos ha
    have h2 := ThetaCurvature.velocityGap_pos hb.le
    dsimp only [n,e,completedCurvatureEven,completedCurvatureOddJet]
    change (v b+v a)/2 < 2*((c b+c a)/2)
    linarith
  have hnk : n < 2*k := by linarith
  have hupper : (d+t*n)/2 < k := by
    have h := sourceCurvature_endpoint_reserve ha hab
    have hid : e^2-c a*((d+t*n)/2)=
        ((c b)^2-(c a)^2-(b-a)*c a*v b)/4 := by
      dsimp only [e,d,n,a,b,completedCurvatureEven,completedLocalDenominator,completedCurvatureOddJet]
      ring
    apply (lt_div_iff₀ hca).mpr
    nlinarith only [h,hid]
  have hsec : v a*(b-a) ≤ c b-c a := by
    apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (fun x _ => (hasDerivAt_thetaCuspLogCurvature x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_thetaCuspLogCurvature x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_) a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩ hab.le
    rw [(hasDerivAt_thetaCuspLogCurvature x).deriv]
    exact thetaCuspLogCurvatureJet_strictMono.monotone (interior_subset hx).1
  have hmin : 0 < d-t*n := by
    have hid : d-t*n=c a+c b-t*v a := by
      dsimp only [d,n,a,b,completedLocalDenominator,completedCurvatureEven,completedCurvatureOddJet]
      ring
    rw [hid]
    have hspan : b-a=2*t := by dsimp only [a,b]; ring
    rw [hspan] at hsec
    nlinarith only [hsec,hca,hcb]
  let w : ℝ → ℝ := fun x => d*(d-n*(x-u))/2
  have hwpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < w x := by
    have hxu : x-u ≤ t := by have h := hx.2; dsimp only [b] at h; linarith
    have hprod := mul_nonneg hn.le (sub_nonneg.mpr hxu)
    have hh : 0 < d-n*(x-u) := by nlinarith only [hprod,hmin]
    exact div_pos (mul_pos hdpos hh) (by norm_num)
  have hcap (x : ℝ) (hx : x ∈ Icc a b) :
      w x*factorCurvature (q x)-3*n*d*factorLogSlope (q x) < 18*e^2*d := by
    have hx0 := ha.trans hx.1
    have hq := thetaCuspLikelihoodCoordinate_pos hx0
    have hf := factorLogSlope_neg hq
    have hbeta : 0 < factorCurvature (q x) := by unfold factorCurvature; positivity
    have hxu : -t ≤ x-u := by have h := hx.1; dsimp only [a] at h; linarith
    have hprod := mul_nonneg hn.le (sub_nonneg.mpr hxu)
    have hA : (d-n*(x-u))/2 < k := by nlinarith only [hprod,hupper]
    have h1 := mul_lt_mul_of_pos_right hA hbeta
    have h2 := mul_lt_mul_of_pos_right hnk (neg_pos.mpr hf)
    have h3 := mul_lt_mul_of_pos_left (source_factor_adjoint_reserve hx0) hk
    have h4 : 324*k < 18*e^2 := by
      have h := mul_lt_mul_of_pos_left (show (324:ℝ) < 18*c a by linarith) hk
      have hid : k*(18*c a)=18*e^2 := by dsimp only [k]; field_simp
      rw [hid] at h
      nlinarith only [h]
    have h5 : ((d-n*(x-u))/2)*factorCurvature (q x)-3*n*factorLogSlope (q x) < 18*e^2 := by
      nlinarith only [h1,h2,h3,h4]
    have h6 := mul_lt_mul_of_pos_right h5 hdpos
    dsimp only [w]
    nlinarith only [h6]
  let T : ℝ → ℝ := fun x => w x*sourceDefectJetSlope x-
    (5/2)*n*d*sourceDefectJet x+18*e^2*d*curvatureDefect x
  have hw (x : ℝ) : HasDerivAt w (-d*n/2) x := by
    convert! (((((hasDerivAt_id x).sub_const u).const_mul n).const_sub d).const_mul d).div_const 2 using 1
    ring
  have hdT (x : ℝ) : HasDerivAt T
      (w x*(iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)-
        3*n*d*sourceDefectJetSlope x-18*e^2*d*sourceDefectJet x) x := by
    have hB : HasDerivAt curvatureDefect (-sourceDefectJet x) x := by
      convert! hasDerivAt_curvatureDefect x using 1
      unfold thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet sourceDefectJet
      ring
    convert! (((hw x).mul (hasDerivAt_sourceDefectJetSlope x)).sub
      ((hasDerivAt_sourceDefectJet x).const_mul ((5/2)*n*d))).add
      (hB.const_mul (18*e^2*d)) using 1
    ring
  have hT : StrictAntiOn T (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro x _
      exact (hdT x).continuousAt.continuousWithinAt
    · intro x hx
      have hxab : x ∈ Icc a b := interior_subset hx
      have hxo : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      have hax : a < x := hxo.1
      have hx0 := ha.trans_lt hax
      rw [(hdT x).deriv]
      have hc := mul_lt_mul_of_pos_left (sourceDefect_curvature_upper hx0) (hwpos x hxab)
      have hs := mul_lt_mul_of_pos_left (sourceDefect_slope_lower hx0) (show 0 < 3*n*d by positivity)
      have hH := source_defect_pos hx0
      have hce := mul_lt_mul_of_pos_right (hcap x hxab) hH
      dsimp only [sourceDefectJet,sourceDefectJetSlope]
      nlinarith only [hc,hs,hce]
  have hTd : 0 < T a-T b := sub_pos.mpr
    (hT (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩) (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hab)
  have hJlower : 0 < J-e*(curvatureDefect a-curvatureDefect b)-n*p := by
    have hgap := source_velocity_square_gap ha hab
    have hid : J-e*(curvatureDefect a-curvatureDefect b)-n*p =
        ((v b)^2-(v a)^2-4*((c b)^2-(c a)^2))/2+
        2*t*(c a*v b+c b*v a)+(t/2)*(v b*curvatureDefect a+v a*curvatureDefect b) := by
      dsimp only [J,e,n,p,a,b,localDescentNumerator,completedCurvatureEven,
        completedCurvatureOddJet,completedLocalDenominator,curvatureDefect]
      ring
    rw [hid]
    have hgap0 : 0 < (v b)^2-(v a)^2-4*((c b)^2-(c a)^2) := by linarith only [hgap]
    positivity
  have hg := descentAuxiliary_pos ht htu
  have hid : localDescentSturmReserve u t =
      (18*e*d)*(J-e*(curvatureDefect a-curvatureDefect b)-n*p)+
        n*d*p*(18*e-8)+descentAuxiliary u t*J+(T a-T b) := by
    dsimp only [localDescentSturmReserve,descentAuxiliaryJet,T,w,J,e,n,d,p,a,b]
    ring
  rw [hid]
  have he8 : 0 < 18*e-8 := by linarith
  positivity


def descentDenominatorJet (u t : ℝ) : ℝ :=
  3*((v (u+t)-v (u-t))/2)+t*((B (u+t)+B (u-t))/2)

def descentOddSecondJet (u t : ℝ) : ℝ := (B (u+t)-B (u-t))/2

def localDescentNumeratorJet (u t : ℝ) : ℝ :=
  completedCurvatureOddJet u t*descentAuxiliary u t+
    ((sourceDefectJet (u+t)+sourceDefectJet (u-t))/2)*completedLocalDenominator u t

def localDescentNumeratorJetTwo (u t : ℝ) : ℝ :=
  descentOddSecondJet u t*descentAuxiliary u t+
    completedCurvatureOddJet u t*descentAuxiliaryJet u t+
    ((sourceDefectJetSlope (u+t)-sourceDefectJetSlope (u-t))/2)*completedLocalDenominator u t+
    ((sourceDefectJet (u+t)+sourceDefectJet (u-t))/2)*descentDenominatorJet u t

theorem hasDerivAt_descentAuxiliary (u t : ℝ) :
    HasDerivAt (descentAuxiliary u) (descentAuxiliaryJet u t) t := by
  have hbp := (hasDerivAt_curvatureDefect (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hbm := (hasDerivAt_curvatureDefect (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  have hHp := (hasDerivAt_sourceDefectJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hHm := (hasDerivAt_sourceDefectJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (((hasDerivAt_completedCurvatureEven u t).const_mul 8).add
    ((hbp.add hbm).const_mul 2)).sub (((hasDerivAt_id t).mul (hHp.sub hHm)).div_const 2) using 1
  dsimp only [id_eq,Pi.sub_apply,Pi.add_apply,Function.comp_apply]
  unfold descentAuxiliaryJet sourceDefectJet sourceDefectJetSlope
    thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
  ring

theorem hasDerivAt_descentDenominatorJet (u t : ℝ) :
    HasDerivAt (descentDenominatorJet u)
      (4*completedLocalDenominator u t+descentAuxiliary u t) t := by
  have hvp := (hasDerivAt_thetaCuspLogCurvatureJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hvm := (hasDerivAt_thetaCuspLogCurvatureJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  have hBp := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hBm := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (((hvp.sub hvm).div_const 2).const_mul 3).add
    ((hasDerivAt_id t).mul ((hBp.add hBm).div_const 2)) using 1
  dsimp only [id_eq,Pi.sub_apply,Pi.add_apply,Function.comp_apply]
  unfold descentAuxiliary completedLocalDenominator completedCurvatureEven curvatureDefect
    sourceDefectJet thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
  ring

theorem hasDerivAt_descentOddSecondJet (u t : ℝ) :
    HasDerivAt (descentOddSecondJet u)
      (4*completedCurvatureOddJet u t-(sourceDefectJet (u+t)+sourceDefectJet (u-t))/2) t := by
  have hBp := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hBm := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hBp.sub hBm).div_const 2 using 1
  unfold completedCurvatureOddJet sourceDefectJet thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
  ring

theorem hasDerivAt_localDescentNumerator (u t : ℝ) :
    HasDerivAt (localDescentNumerator u) (localDescentNumeratorJet u t) t := by
  have hn : HasDerivAt (completedCurvatureOddJet u) (descentOddSecondJet u t) t :=
    hasDerivAt_completedCurvatureOddJet u t
  have hd : HasDerivAt (completedLocalDenominator u) (descentDenominatorJet u t) t :=
    hasDerivAt_completedLocalDenominator u t
  convert! (hn.mul (hasDerivAt_descentDenominatorJet u t)).sub
    ((hasDerivAt_descentOddSecondJet u t).mul hd) using 1
  unfold localDescentNumeratorJet
  ring

theorem hasDerivAt_localDescentNumeratorJet (u t : ℝ) :
    HasDerivAt (localDescentNumeratorJet u) (localDescentNumeratorJetTwo u t) t := by
  have hn : HasDerivAt (completedCurvatureOddJet u) (descentOddSecondJet u t) t :=
    hasDerivAt_completedCurvatureOddJet u t
  have hd : HasDerivAt (completedLocalDenominator u) (descentDenominatorJet u t) t :=
    hasDerivAt_completedLocalDenominator u t
  have hHp := (hasDerivAt_sourceDefectJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hHm := (hasDerivAt_sourceDefectJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hn.mul (hasDerivAt_descentAuxiliary u t)).add (((hHp.add hHm).div_const 2).mul hd) using 1
  dsimp only [Pi.add_apply,Function.comp_apply]
  unfold localDescentNumeratorJetTwo
  ring

theorem iteratedDeriv_two_localDescentNumerator (u t : ℝ) :
    iteratedDeriv 2 (localDescentNumerator u) t=localDescentNumeratorJetTwo u t := by
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (localDescentNumerator u)=localDescentNumeratorJet u :=
    funext (fun s => (hasDerivAt_localDescentNumerator u s).deriv)
  rw [he]
  exact (hasDerivAt_localDescentNumeratorJet u t).deriv

/-- Actual denominator-coupled Sturm inequality throughout the full physical chamber. -/
theorem localDescentNumerator_sturm_subsolution {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    iteratedDeriv 2 (localDescentNumerator u) t-
      (deriv (completedLocalDenominator u) t/completedLocalDenominator u t)*
        deriv (localDescentNumerator u) t <
      18*completedCurvatureEven u t*localDescentNumerator u t := by
  have hd := completedLocalDenominator_pos_nonneg u ht.le
  have hr := localDescentSturmReserve_pos ht htu
  rw [iteratedDeriv_two_localDescentNumerator,(hasDerivAt_completedLocalDenominator u t).deriv,
    (hasDerivAt_localDescentNumerator u t).deriv]
  have hid : completedLocalDenominator u t*
      (18*completedCurvatureEven u t*localDescentNumerator u t-
        (localDescentNumeratorJetTwo u t-
          (descentDenominatorJet u t/completedLocalDenominator u t)*localDescentNumeratorJet u t))=
      localDescentSturmReserve u t := by
    field_simp [hd.ne']
    dsimp only [localDescentSturmReserve,localDescentNumeratorJetTwo,localDescentNumeratorJet,
      localDescentNumerator,descentOddSecondJet,descentDenominatorJet]
    ring
  change localDescentNumeratorJetTwo u t-
      (descentDenominatorJet u t/completedLocalDenominator u t)*localDescentNumeratorJet u t < _
  have h := (mul_pos_iff_of_pos_left hd).mp (show 0 < completedLocalDenominator u t*
      (18*completedCurvatureEven u t*localDescentNumerator u t-
        (localDescentNumeratorJetTwo u t-
          (descentDenominatorJet u t/completedLocalDenominator u t)*localDescentNumeratorJet u t)) by
    rw [hid]
    exact hr)
  exact sub_pos.mp h

end
end RHTower.ThetaCuspDefect
