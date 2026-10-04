import GaloisForLFunctions.RHTower.ThetaCuspC5CoupledShapeDynamics
/-! Strict growth of the actual normalized intrinsic inverse reserve.
The coupled curvature dynamics absorb the complete adverse fourth-jet
contribution. Every source inequality is discharged on 0 < t <= u;
two positive polynomial decompositions complete the derivative sign.
This is a component of the inverse-source/clock comparison. That full
comparison and zero-endpoint Green recovery are not asserted here. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "Q" => thetaCuspReflectedLogAction

private theorem reserve_growth_algebra {t Z a g b d eps x y v : ℝ}
    (ht : 0 < t) (hZ : 18*t^2 ≤ Z) (ha : 1 ≤ a) (hg : 1 ≤ g) (hga : g ≤ a)
    (hb : 0 ≤ b) (hb9 : b ≤ 9*t^2) (hd : 0 ≤ d) (hd9 : d ≤ 9*a*t^2)
    (heps : eps ≤ 846*t^4) (hepsb : eps ≤ 166*t^2*b)
    (hx : 0 < x) (hy : b < y) (hyeq : y=(2-a)*b+d) (hv : 0 < v)
    (hL : 3*b+d < (2*a+b)*(1+3*Z/8)) :
    0 <
      let D := 2*a+b
      let L := 3*b+d
      let A := 9+12*Z+16*g
      let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
      (2*P+5*D)*x+(P+25*D-15*A)*y+
        (D*(384*Z+192*g+208)-80*L)*v+
        (D*(288*Z+384*g+156)-60*L)*Z*(1+a)-5*A*((3-a)*d+eps) := by
  let D := 2*a+b
  let L := 3*b+d
  let A := 9+12*Z+16*g
  let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
  change 0 < (2*P+5*D)*x+(P+25*D-15*A)*y+
    (D*(384*Z+192*g+208)-80*L)*v+
    (D*(288*Z+384*g+156)-60*L)*Z*(1+a)-5*A*((3-a)*d+eps)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hg0 : 0 < g := lt_of_lt_of_le (by norm_num) hg
  have ha1 : 0 ≤ a-1 := sub_nonneg.mpr ha
  have hg1 : 0 ≤ g-1 := sub_nonneg.mpr hg
  have hag : 0 ≤ a-g := sub_nonneg.mpr hga
  have hZ0 : 0 < Z := (mul_pos (by norm_num) (sq_pos_of_pos ht)).trans_le hZ
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 < P := by
    have hi : P=144*Z^2+384*Z*g+96*g^2+156*Z+208*(g-1)+199+5*a+25*b := by dsimp [P]; ring
    rw [hi]; positivity
  have hfirst : 0 < (2*P+5*D)*x := by positivity
  have hy0 : 0 < y := hb.trans_lt hy
  have hyup : y ≤ b+d := by
    have hh := mul_nonneg ha1 hb
    rw [hyeq]
    nlinarith only [hh]
  have htail : 0 ≤ P+25*D-15*A+25-144*Z^2 := by
    have hid : P+25*D-15*A+25-144*Z^2=
        (384*g-24)*Z+96*(g-1)^2+160*(g-1)+55*(a-1)+50*b := by dsimp [P,D,A]; ring
    rw [hid]
    have h384 : 0 ≤ 384*g-24 := by linarith
    positivity
  have hyterm : 144*Z^2*b-25*(b+d) ≤ (P+25*D-15*A)*y := by
    have h1 := mul_nonneg htail hy0.le
    have h2 := mul_le_mul_of_nonneg_left hy.le (show 0 ≤ 144*Z^2 by positivity)
    nlinarith only [h1,h2,hyup]
  have hgcoef : 0 ≤ D*(384*Z+192*g+208)-80*L := by
    have hh : L ≤ D*(1+3*Z/8) := hL.le
    have hp0 : 0 ≤ D*(354*Z+192*g+128) := by positivity
    nlinarith only [hh,hp0]
  have hgterm : 0 ≤ (D*(384*Z+192*g+208)-80*L)*v := mul_nonneg hgcoef hv.le
  have hzcoef : D*((531/2)*Z+384*g+96) ≤ D*(288*Z+384*g+156)-60*L := by
    have hh : L ≤ D*(1+3*Z/8) := hL.le
    nlinarith only [hh]
  have hzterm := mul_le_mul_of_nonneg_right hzcoef (show 0 ≤ Z*(1+a) by positivity)
  have hdstep : (3-a)*d ≤ 2*d := by
    have hh := mul_nonneg ha1 hd
    nlinarith only [hh]
  have hdterm := mul_le_mul_of_nonneg_left hdstep (show 0 ≤ 5*A by positivity)
  have heps1 := mul_le_mul_of_nonneg_left heps (show 0 ≤ 45+80*g by positivity)
  have heps2 := mul_le_mul_of_nonneg_left hepsb (show 0 ≤ 60*Z by positivity)
  have hepspay : 5*A*eps ≤ (45+80*g)*846*t^4+60*Z*166*t^2*b := by
    dsimp only [A]
    nlinarith only [heps1,heps2]
  have ht2 : t^2 ≤ Z/18 := by linarith only [hZ]
  have ht4 : t^4 ≤ Z^2/324 := by
    have hh := mul_self_le_mul_self (sq_nonneg t) ht2
    nlinarith only [hh]
  have hbpay : 25*b ≤ (25/2)*Z := by linarith only [hb9,ht2]
  have hdpay : (25+10*A)*d ≤ (a/2)*Z*(115+120*Z+160*g) := by
    have hh := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 9*a by positivity)
    have hd' : d ≤ a*Z/2 := by nlinarith only [hd9,hh]
    have hh' := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 25+10*A by positivity)
    dsimp only [A] at hh'
    nlinarith only [hh']
  have hepay : (45+80*g)*846*t^4 ≤ (235/18)*(9+16*g)*Z^2 := by
    have hh := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ (45+80*g)*846 by positivity)
    nlinarith only [hh]
  have hebpay : 60*Z*166*t^2*b ≤ (1660/3)*b*Z^2 := by
    have hh := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 60*Z*166*b by positivity)
    nlinarith only [hh]
  let C2 := (531/2)*D*(1+a)-(1228/3)*b-60*a-(235/18)*(9+16*g)
  let C1 := D*(384*g+96)*(1+a)-(a/2)*(115+160*g)-25/2
  have hC2 : 0 < C2 := by
    have hi : C2=531*(a-1)^2+(11917/9)*(a-1)+12161/18+
        (365/3)*b+(531/2)*(a-1)*b+(1880/9)*(a-g) := by dsimp [C2,D]; ring
    rw [hi]; positivity
  have hC1 : 0 < C1 := by
    have hi : C1=(384*g+96)*(2*a*(a-1)+b*(1+a))+
        1456*a*(g-1)+(3565/2)*(a-1)+1770 := by dsimp [C1,D]; ring
    rw [hi]; positivity
  have hreserve : 0 < C2*Z^2+C1*Z := by positivity
  have hlo : C2*Z^2+C1*Z ≤
      144*Z^2*b+D*((531/2)*Z+384*g+96)*Z*(1+a)-25*(b+d)-
        10*A*d-(45+80*g)*846*t^4-60*Z*166*t^2*b := by
    dsimp only [C2,C1,A] at *
    nlinarith only [hbpay,hdpay,hepay,hebpay]
  nlinarith only [hfirst,hyterm,hgterm,hzterm,hdterm,hepspay,hlo,hreserve]


private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem p_nonneg (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p u t := by
  unfold shapeCurvatureSlope
  exact div_nonneg (sub_nonneg.mpr
    (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)
private theorem hp_deriv (u t : ℝ) : HasDerivAt (p u) (r u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem r_pos (u t : ℝ) : 0 < r u t := by
  unfold shapeCurvatureSecond
  exact div_pos (add_pos (thetaCuspLogCurvatureJetTwo_pos_all (u+t))
    (thetaCuspLogCurvatureJetTwo_pos_all (u-t))) (by norm_num)
private theorem r_upper {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : r u t < 9*e u t := by
  have hp := source_projective_upper (show 0 ≤ u+t by linarith)
  have hm := source_projective_upper (show 0 ≤ u-t by linarith)
  unfold shapeCurvatureSecond completedCurvatureEven
  linarith

private theorem chamber_nonneg {f g : ℝ → ℝ} {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (h0 : f 0=0) (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, 0 < s → s < u → 0 ≤ g s) : 0 ≤ f t := by
  have hm : MonotoneOn f (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 u := by simpa only [interior_Icc] using hs
      rw [(hd s).deriv]
      exact hg s hs'.1 hs'.2
  simpa only [h0] using hm ⟨le_rfl,ht.trans htu⟩ ⟨ht,htu⟩ ht

private theorem alpha_lower {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 1 ≤ curvatureShapeAlpha u t := by
  have hd (s : ℝ) : HasDerivAt (fun s => s*e u s-E u s) (s*p u s) s := by
    convert! ((hasDerivAt_id s).mul (hasDerivAt_completedCurvatureEven u s)).sub
      (hasDerivAt_completedDecayEvenPrimitive u s) using 1
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    change s*p u s=1*e u s+s*p u s-e u s
    ring
  have hh : 0 ≤ t*e u t-E u t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero]) hd
    intro s hs _; exact mul_nonneg hs.le (p_nonneg u hs.le)
  unfold curvatureShapeAlpha
  exact (le_div_iff₀ (E_pos u ht)).mpr (by linarith only [hh])

private theorem action_lower {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 18*t^2 ≤ curvatureShapeAction u t := by
  have hd (s : ℝ) : HasDerivAt (fun s => E u s-18*s) (e u s-18) s := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u s).sub ((hasDerivAt_id s).const_mul 18) using 1
    ring
  have hh : 0 ≤ E u t-18*t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero]) hd
    intro s hs hsu
    have hp := sourceCurvature_gt_eighteen (show 0 ≤ u+s by linarith)
    have hm := sourceCurvature_gt_eighteen (show 0 ≤ u-s by linarith)
    unfold completedCurvatureEven
    linarith
  have hmul := mul_nonneg ht.le hh
  unfold curvatureShapeAction
  nlinarith only [hmul]

private theorem beta_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : curvatureShapeBeta u t ≤ 9*t^2 := by
  have hd (s : ℝ) : HasDerivAt (fun s => 9*E u s-p u s) (9*e u s-r u s) s :=
    ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul 9).sub (hp_deriv u s)
  have hh : 0 ≤ 9*E u t-p u t := by
    apply chamber_nonneg ht.le htu (by simp [completedDecayEvenPrimitive_zero,shapeCurvatureSlope]) hd
    intro s hs hsu; exact sub_nonneg.mpr (r_upper hs.le hsu.le).le
  unfold curvatureShapeBeta
  apply (div_le_iff₀ (E_pos u ht)).mpr
  have hmul := mul_nonneg (sq_nonneg t) hh
  nlinarith only [hmul]

private theorem delta_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeDelta u t ≤ 9*curvatureShapeAlpha u t*t^2 := by
  have hh := mul_le_mul_of_nonneg_left (r_upper ht.le htu).le
    (div_nonneg (pow_nonneg ht.le 3) (E_pos u ht).le)
  unfold curvatureShapeDelta curvatureShapeAlpha
  convert! hh using 1 <;> field_simp [(E_pos u ht).ne']

private theorem gamma_bounds {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 ≤ curvatureShapeGamma u t ∧ curvatureShapeGamma u t ≤ curvatureShapeAlpha u t := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hg0 : 0 < curvatureShapeGamma u t := by unfold curvatureShapeGamma; positivity
  have ha := alpha_lower ht htu
  constructor
  · have hh := two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
      (fun x _ => (thetaCuspLogCurvatureJetTwo_pos_all x).le)
    unfold thetaCuspReflectedActionVelocity at hh
    rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hh
    unfold curvatureShapeGamma
    exact (le_div_iff₀ hQ).mpr (by linarith only [hh])
  · have hd : 0 < t*deriv (curvatureShapeGamma u) t := by
      rw [(hasDerivAt_curvatureShapeGamma u ht).deriv]
      exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu) (sq_pos_of_pos hQ))
    rw [curvatureShapeGamma_evolution u ht] at hd
    have hinner : 0 < 1+curvatureShapeAlpha u t-2*curvatureShapeGamma u t := by
      by_contra hn
      have hh := mul_nonpos_of_nonneg_of_nonpos hg0.le (le_of_not_gt hn)
      linarith only [hd,hh]
    linarith only [ha,hinner]

private theorem epsilon_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeEpsilon u t ≤ 846*t^4 := by
  have hh := mul_le_mul_of_nonneg_left (quadratureCurvatureThird_lt_primitive ht htu).le
    (div_nonneg (pow_nonneg ht.le 4) (E_pos u ht).le)
  unfold curvatureShapeEpsilon
  convert! hh using 1 <;> field_simp [(E_pos u ht).ne']

private theorem normalized_denominator_budget {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    3*curvatureShapeBeta u t+curvatureShapeDelta u t <
      (2*curvatureShapeAlpha u t+curvatureShapeBeta u t)*(1+3*curvatureShapeAction u t/8) := by
  have hh := mul_lt_mul_of_pos_left (actionProfile_denominator_budget ht htu) (div_pos ht (E_pos u ht))
  unfold curvatureShapeBeta curvatureShapeDelta curvatureShapeAlpha curvatureShapeAction
  convert! hh using 1 <;>
    dsimp [descentDenominatorJet,completedLocalDenominator,shapeCurvatureSlope,shapeCurvatureSecond] <;>
    field_simp [(E_pos u ht).ne']

/-- Exact scaled derivative of the inverse reserve in coupled shape variables. -/
def normalizedInverseReserveFlow (u t : ℝ) : ℝ :=
  let Z := curvatureShapeAction u t
  let a := curvatureShapeAlpha u t
  let g := curvatureShapeGamma u t
  let b := curvatureShapeBeta u t
  let d := curvatureShapeDelta u t
  let eps := curvatureShapeEpsilon u t
  let D := 2*a+b
  let L := 3*b+d
  let A := 9+12*Z+16*g
  let P := 144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b
  ((2*P+5*D)*(a+b-a^2)+(P+25*D-15*A)*((2-a)*b+d)+
    (D*(384*Z+192*g+208)-80*L)*(g*(1+a-2*g))+
    (D*(288*Z+384*g+156)-60*L)*Z*(1+a)-5*A*((3-a)*d+eps))/25

theorem hasDerivAt_normalizedActionInverseReserve (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (normalizedActionInverseReserve u) (normalizedInverseReserveFlow u t/t) t := by
  let Z := curvatureShapeAction u
  let a := curvatureShapeAlpha u
  let g := curvatureShapeGamma u
  let b := curvatureShapeBeta u
  let d := curvatureShapeDelta u
  let D := fun s => 2*a s+b s
  let L := fun s => 3*b s+d s
  let A := fun s => 9+12*Z s+16*g s
  let P := fun s => 144*(Z s)^2+384*Z s*g s+96*(g s)^2+156*Z s+208*g s-9+5*a s+25*b s
  have hZ : HasDerivAt Z (deriv Z t) t :=
    (hasDerivAt_mul_completedDecayEvenPrimitive u t).congr_deriv
      (hasDerivAt_mul_completedDecayEvenPrimitive u t).deriv.symm
  have ha : HasDerivAt a (deriv a t) t := (hasDerivAt_curvatureShapeAlpha u ht).congr_deriv
    (hasDerivAt_curvatureShapeAlpha u ht).deriv.symm
  have hg : HasDerivAt g (deriv g t) t := (hasDerivAt_curvatureShapeGamma u ht).congr_deriv
    (hasDerivAt_curvatureShapeGamma u ht).deriv.symm
  have hb : HasDerivAt b (deriv b t) t := (hasDerivAt_curvatureShapeBeta u ht).congr_deriv
    (hasDerivAt_curvatureShapeBeta u ht).deriv.symm
  have hd : HasDerivAt d (deriv d t) t := (hasDerivAt_curvatureShapeDelta u ht).congr_deriv
    (hasDerivAt_curvatureShapeDelta u ht).deriv.symm
  have hD := (ha.const_mul 2).add hb
  have hL := (hb.const_mul 3).add hd
  have hA := ((hZ.const_mul 12).const_add 9).add (hg.const_mul 16)
  have hP := ((((((((hZ.pow 2).const_mul 144).add ((hZ.const_mul 384).mul hg)).add
    ((hg.pow 2).const_mul 96)).add (hZ.const_mul 156)).add (hg.const_mul 208)).sub_const 9).add
    (ha.const_mul 5)).add (hb.const_mul 25)
  let slope := ((2*P t+5*D t)*deriv a t+(P t+25*D t-15*A t)*deriv b t+
    (D t*(384*Z t+192*g t+208)-80*L t)*deriv g t+
    (D t*(288*Z t+384*g t+156)-60*L t)*deriv Z t-5*A t*deriv d t)/25
  have hpoly : HasDerivAt (fun s => D s*P s/25-L s*A s/5) slope t := by
    convert! ((hD.mul hP).div_const 25).sub ((hL.mul hA).div_const 5) using 1
    dsimp only [D,L,A,P,slope,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
    ring
  have heq : normalizedActionInverseReserve u =ᶠ[nhds t] (fun s => D s*P s/25-L s*A s/5) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact normalizedActionInverseReserve_polynomial u hs
  have hs : t*slope=normalizedInverseReserveFlow u t := by
    have he1 := curvatureShapeAlpha_evolution u ht
    have he2 := curvatureShapeBeta_evolution u ht
    have he3 := curvatureShapeGamma_evolution u ht
    have he4 := curvatureShapeAction_evolution u ht
    have he5 := curvatureShapeDelta_evolution u ht
    change t*deriv a t=a t+b t-(a t)^2 at he1
    change t*deriv b t=(2-a t)*b t+d t at he2
    change t*deriv g t=g t*(1+a t-2*g t) at he3
    change t*deriv Z t=Z t*(1+a t) at he4
    change t*deriv d t=(3-a t)*d t+curvatureShapeEpsilon u t at he5
    change t*slope=((2*P t+5*D t)*(a t+b t-(a t)^2)+
      (P t+25*D t-15*A t)*((2-a t)*b t+d t)+
      (D t*(384*Z t+192*g t+208)-80*L t)*(g t*(1+a t-2*g t))+
      (D t*(288*Z t+384*g t+156)-60*L t)*Z t*(1+a t)-
      5*A t*((3-a t)*d t+curvatureShapeEpsilon u t))/25
    dsimp only [slope]
    linear_combination ((2*P t+5*D t)/25)*he1+((P t+25*D t-15*A t)/25)*he2+
      ((D t*(384*Z t+192*g t+208)-80*L t)/25)*he3+
      ((D t*(288*Z t+384*g t+156)-60*L t)/25)*he4-(A t/5)*he5
  apply (hpoly.congr_of_eventuallyEq heq).congr_deriv
  exact (eq_div_iff ht.ne').mpr (by nlinarith only [hs])

/-- No jet-sign premise remains: the actual normalized inverse reserve grows. -/
theorem normalizedInverseReserveFlow_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < normalizedInverseReserveFlow u t := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hb : 0 ≤ curvatureShapeBeta u t := by
    unfold curvatureShapeBeta
    exact div_nonneg (mul_nonneg (sq_nonneg t) (p_nonneg u ht.le)) hE.le
  have hd : 0 ≤ curvatureShapeDelta u t := by
    unfold curvatureShapeDelta
    exact div_nonneg (mul_nonneg (pow_nonneg ht.le 3) (r_pos u t).le) hE.le
  have hx : 0 < curvatureShapeAlpha u t+curvatureShapeBeta u t-(curvatureShapeAlpha u t)^2 := by
    rw [←curvatureShapeAlpha_evolution u ht,(hasDerivAt_curvatureShapeAlpha u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeAlpha_current_pos ht htu) (sq_pos_of_pos hE))
  have hy : curvatureShapeBeta u t <
      (2-curvatureShapeAlpha u t)*curvatureShapeBeta u t+curvatureShapeDelta u t := by
    rw [←curvatureShapeBeta_evolution u ht]
    exact curvatureShapeBeta_growth ht htu
  have hv : 0 < curvatureShapeGamma u t*(1+curvatureShapeAlpha u t-2*curvatureShapeGamma u t) := by
    rw [←curvatureShapeGamma_evolution u ht,(hasDerivAt_curvatureShapeGamma u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu) (sq_pos_of_pos hQ))
  have heps : curvatureShapeEpsilon u t ≤ 166*t^2*curvatureShapeBeta u t := by
    have hh := curvatureShapeEpsilon_affine_upper ht htu
    have h4 := pow_nonneg ht.le 4
    linarith
  have hh := reserve_growth_algebra ht (action_lower ht htu) (alpha_lower ht htu)
    (gamma_bounds ht htu).1 (gamma_bounds ht htu).2 hb (beta_upper ht htu) hd (delta_upper ht htu)
    (epsilon_upper ht htu) heps hx hy rfl hv (normalized_denominator_budget ht htu)
  exact div_pos hh (by norm_num)

theorem normalizedActionInverseReserve_deriv_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < deriv (normalizedActionInverseReserve u) t := by
  rw [(hasDerivAt_normalizedActionInverseReserve u ht).deriv]
  exact div_pos (normalizedInverseReserveFlow_pos ht htu) ht

theorem normalizedActionInverseReserve_strictMonoOn (u : ℝ) :
    StrictMonoOn (normalizedActionInverseReserve u) (Ioc 0 u) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro s hs; exact (hasDerivAt_normalizedActionInverseReserve u hs.1).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 u := by simpa only [interior_Ioc] using hs
    exact normalizedActionInverseReserve_deriv_pos hs'.1 hs'.2.le


end
end RHTower.ThetaCuspDefect
