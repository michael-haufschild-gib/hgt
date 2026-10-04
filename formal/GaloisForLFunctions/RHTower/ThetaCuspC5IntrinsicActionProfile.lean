import GaloisForLFunctions.RHTower.ThetaCuspC5DenominatorClockComparison
import GaloisForLFunctions.RHTower.ThetaCuspC5ClockSourceOrientation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-! A positive inverse-Green source satisfying the intrinsic-action Bose budget.
The literal profile t^(9/5) Q^(8/5) exp(6Q/5) has positive inverse Green
operator throughout the full same-half-line chamber, and satisfies the
complete Bose compensation inequality. Its positive source has not yet
been compared with the denominator-clock source. That nonlocal order and
zero-endpoint Green recovery remain required; the actual C5 gate and
arbitrary-degree positivity are not asserted here. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "B" => thetaCuspLogCurvatureJetTwo
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "Q" => thetaCuspReflectedLogAction
local notation "d" => completedLocalDenominator
local notation "d₁" => descentDenominatorJet
local notation "y" => completedFirstDenominator

private theorem primitive_center_floor (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    c u*t ≤ E u t := by
  have hd (s : ℝ) : HasDerivAt (fun r => E u r-c u*r) (e u s-c u) s := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u s).sub
      ((hasDerivAt_id s).const_mul (c u)) using 1
    simp only [mul_one]
  have hm : MonotoneOn (fun s => E u s-c u*s) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s).deriv]
      exact sub_nonneg.mpr (centerCurvature_le_completedCurvatureEven u (interior_subset hs))
  have h := hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht ht
  simpa only [completedDecayEvenPrimitive_zero,mul_zero,sub_zero,sub_nonneg] using h

private theorem primitive_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t :=
  (mul_pos (thetaCuspLogCurvature_pos u) ht).trans_le (primitive_center_floor u ht.le)

private theorem action_le_mul_primitive {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    Q u t ≤ t*E u t := by
  have hv := two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
    (fun x _ => (thetaCuspLogCurvatureJetTwo_pos_all x).le)
  unfold thetaCuspReflectedActionVelocity at hv
  rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hv
  linarith

/-- The denominator's growth is controlled in the intrinsic-action variables. -/
theorem actionProfile_denominator_budget {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    t*d₁ u t < (1+3*t*E u t/8)*d u t := by
  let p := (v (u+t)-v (u-t))/2
  let r := (B (u+t)+B (u-t))/2
  have ha : 0 ≤ u-t := sub_nonneg.mpr htu
  have hb : 0 ≤ u+t := by linarith
  have hep := completedCurvatureEven_pos u t
  have hp0 : 0 ≤ p := div_nonneg (sub_nonneg.mpr
    (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith : u-t ≤ u+t))) (by norm_num)
  have hp : p < 2*e u t := by
    have h1 := ThetaCurvature.velocityGap_pos hb
    have h2 := sourceVelocity_nonneg ha
    have h3 := thetaCuspLogCurvature_pos (u-t)
    dsimp only [p,completedCurvatureEven]
    linarith
  have hr : r < 9*e u t := by
    have h1 := source_projective_upper ha
    have h2 := source_projective_upper hb
    dsimp only [r,completedCurvatureEven]
    linarith
  have hd : d u t=2*e u t+t*p := rfl
  have hd1 : d₁ u t=3*p+t*r := rfl
  have hd2 : 2*e u t ≤ d u t := by rw [hd]; nlinarith only [mul_nonneg ht.le hp0]
  have hd0 := completedLocalDenominator_pos_nonneg u ht.le
  have hE : 18*t < E u t :=
    (mul_lt_mul_of_pos_right (sourceCurvature_gt_eighteen (ht.le.trans htu)) ht).trans_le
      (primitive_center_floor u ht.le)
  have h1 : t*d₁ u t < (6*t+9*t^2)*e u t := by
    rw [hd1]
    have ha1 := mul_lt_mul_of_pos_left hp (show 0 < 3*t by positivity)
    have ha2 := mul_lt_mul_of_pos_left hr (sq_pos_of_pos ht)
    nlinarith only [ha1,ha2]
  have h2 : (6*t+9*t^2)*e u t ≤ (3*t+9*t^2/2)*d u t := by
    have h := mul_le_mul_of_nonneg_left hd2 (show 0 ≤ 3*t+9*t^2/2 by positivity)
    nlinarith only [h]
  have h3 : 3*t+9*t^2/2 < 1+3*t*E u t/8 := by
    have hs := sq_nonneg (3*t/2-1)
    have h := mul_lt_mul_of_pos_left hE (show 0 < 3*t/8 by positivity)
    nlinarith only [hs,h]
  exact h1.trans_le h2 |>.trans (mul_lt_mul_of_pos_right h3 hd0)

def actionProfileLogRate (u t : ℝ) : ℝ := 9/(5*t)+12*E u t/5+16*E u t/(5*Q u t)
def actionProfileLogRateJet (u t : ℝ) : ℝ :=
  -9/(5*t^2)+12*e u t/5+16*e u t/(5*Q u t)-32*(E u t)^2/(5*(Q u t)^2)

theorem hasDerivAt_actionProfileLogRate (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (actionProfileLogRate u) (actionProfileLogRateJet u t) t := by
  have hQ : HasDerivAt (Q u) (2*E u t) t := by
    convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
    rw [completedDecayEvenPrimitive_eq]
    ring
  have h := (((hasDerivAt_const t (9:ℝ)).div ((hasDerivAt_id t).const_mul 5) (by positivity)).add
    ((hasDerivAt_completedDecayEvenPrimitive u t).const_mul 12 |>.div_const 5)).add
    (((hasDerivAt_completedDecayEvenPrimitive u t).const_mul 16).div (hQ.const_mul 5)
      (mul_ne_zero (by norm_num) (thetaCuspReflectedLogAction_pos (u := u) ht).ne'))
  convert! h using 1
  simp only [id_eq]
  unfold actionProfileLogRateJet
  field_simp [ht.ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  ring

/-- Cleared inverse-Green source of the intrinsic action comparison profile. -/
def actionProfileInverseReserve (u t : ℝ) : ℝ :=
  d u t*descentDenominator u t*((actionProfileLogRate u t)^2+actionProfileLogRateJet u t)-
    (d₁ u t*descentDenominator u t+d u t*y u t)*actionProfileLogRate u t+(d u t)^2

theorem actionProfileInverseReserve_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < actionProfileInverseReserve u t := by
  have hE := primitive_pos u ht
  have he := completedCurvatureEven_pos u t
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hd := completedLocalDenominator_pos_nonneg u ht.le
  have hγ : 0 ≤ t*E u t/Q u t-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hQ).mpr (by simpa only [one_mul] using action_le_mul_primitive ht htu)
  let p := (v (u+t)-v (u-t))/2
  have hp : 0 ≤ p := div_nonneg (sub_nonneg.mpr
    (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith : u-t ≤ u+t))) (by norm_num)
  let T := (243/2:ℝ)*(t*E u t)^2+354*(t*E u t)*(t*E u t/Q u t)+
    (633/8)*(t*E u t)+96*(t*E u t/Q u t-1)^2+320*(t*E u t/Q u t-1)+170+
    5*(t*e u t/E u t)+25*(t^2*p/E u t)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hh : 0 < actionProfileLogRate u t := by unfold actionProfileLogRate; positivity
  have hbudget := actionProfile_denominator_budget ht htu
  have hbudget' : d₁ u t < (1/t+3*E u t/8)*d u t := by
    apply (mul_lt_mul_iff_right₀ ht).mp
    convert! hbudget using 1
    field_simp [ht.ne']
  have hidentity : actionProfileInverseReserve u t=
      E u t*d u t/(25*t)*T+
      ((1/t+3*E u t/8)*d u t-d₁ u t)*descentDenominator u t*actionProfileLogRate u t := by
    unfold actionProfileInverseReserve actionProfileLogRate actionProfileLogRateJet
      descentDenominator completedFirstDenominator completedLocalDenominator
    dsimp only [T,p]
    field_simp [ht.ne',hE.ne',hQ.ne']
    ring
  rw [hidentity]
  have hfirst : 0 < E u t*d u t/(25*t)*T := by positivity
  have hsecond : 0 < ((1/t+3*E u t/8)*d u t-d₁ u t)*descentDenominator u t*actionProfileLogRate u t :=
    mul_pos (mul_pos (sub_pos.mpr hbudget') (descentDenominator_pos u ht)) hh
  exact add_pos hfirst hsecond

/-- Intrinsic action comparison profile; its Green inverse is strictly positive. -/
def intrinsicActionProfile (u t : ℝ) : ℝ :=
  t^((9:ℝ)/5)*(Q u t)^((8:ℝ)/5)*Real.exp (6*Q u t/5)

theorem intrinsicActionProfile_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < intrinsicActionProfile u t := by
  unfold intrinsicActionProfile
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos ht _)
    (Real.rpow_pos_of_pos (thetaCuspReflectedLogAction_pos (u := u) ht) _)) (Real.exp_pos _)

theorem hasDerivAt_intrinsicActionProfile (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (intrinsicActionProfile u)
      (intrinsicActionProfile u t*actionProfileLogRate u t) t := by
  have hQ : HasDerivAt (Q u) (2*E u t) t := by
    convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
    rw [completedDecayEvenPrimitive_eq]
    ring
  have ha := (hasDerivAt_id t).rpow_const (p := (9:ℝ)/5) (Or.inl ht.ne')
  have hb := hQ.rpow_const (p := (8:ℝ)/5) (Or.inl (thetaCuspReflectedLogAction_pos (u := u) ht).ne')
  have hc := ((hQ.const_mul 6).div_const 5).exp
  convert! (ha.mul hb).mul hc using 1
  simp only [id_eq,Pi.mul_apply]
  unfold intrinsicActionProfile actionProfileLogRate
  rw [Real.rpow_sub_one ht.ne',Real.rpow_sub_one (thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  field_simp [ht.ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  ring

theorem hasDerivAt_intrinsicActionProfileJet (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => intrinsicActionProfile u s*actionProfileLogRate u s)
      (intrinsicActionProfile u t*((actionProfileLogRate u t)^2+actionProfileLogRateJet u t)) t := by
  convert! (hasDerivAt_intrinsicActionProfile u ht).mul (hasDerivAt_actionProfileLogRate u ht) using 1
  ring

theorem iteratedDeriv_two_intrinsicActionProfile (u : ℝ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (intrinsicActionProfile u) t=
      intrinsicActionProfile u t*((actionProfileLogRate u t)^2+actionProfileLogRateJet u t) := by
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (intrinsicActionProfile u) =ᶠ[nhds t]
      (fun s => intrinsicActionProfile u s*actionProfileLogRate u s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_intrinsicActionProfile u hs).deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_intrinsicActionProfileJet u ht).deriv

/-- The actual second-order inverse-Green operator is positive on the profile.
The subsequent denominator-clock Sturm supersolution inequality is not asserted. -/
theorem intrinsicActionProfile_inverseGreen_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < d u t*descentDenominator u t*iteratedDeriv 2 (intrinsicActionProfile u) t-
      (d₁ u t*descentDenominator u t+d u t*y u t)*deriv (intrinsicActionProfile u) t+
      (d u t)^2*intrinsicActionProfile u t := by
  have h := mul_pos (intrinsicActionProfile_pos u ht) (actionProfileInverseReserve_pos ht htu)
  rw [iteratedDeriv_two_intrinsicActionProfile u ht,(hasDerivAt_intrinsicActionProfile u ht).deriv]
  unfold actionProfileInverseReserve at h
  nlinarith only [h]

/-- Positive source obtained by inverting the Green operator on the action profile. -/
def intrinsicActionInverseSource (u t : ℝ) : ℝ :=
  intrinsicActionProfile u t*actionProfileInverseReserve u t/(4*(descentDenominator u t)^2)

theorem intrinsicActionInverseSource_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < intrinsicActionInverseSource u t := by
  unfold intrinsicActionInverseSource
  exact div_pos (mul_pos (intrinsicActionProfile_pos u ht) (actionProfileInverseReserve_pos ht htu))
    (mul_pos (by norm_num) (sq_pos_of_pos (descentDenominator_pos u ht)))

/-- The action profile meets the full Bose budget throughout positive displacement. -/
theorem intrinsicActionProfile_bose_budget (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (c5CompletedBoseWeight u t-5)*intrinsicActionProfile u t-
      5*t*deriv (intrinsicActionProfile u) t := by
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hE := primitive_pos u ht
  have hr : 0 < Real.exp (Q u t)-1 := by
    have h := Real.exp_lt_exp.mpr hQ
    rw [Real.exp_zero] at h
    linarith
  have hp := exp_padé_floor hQ.le
  have hf : 0 ≤ 4+8/(Real.exp (Q u t)-1)-8/Q u t := by
    have hid : (4+8/(Real.exp (Q u t)-1)-8/Q u t)*
        (Q u t*(Real.exp (Q u t)-1))=
        4*((Q u t-2)*Real.exp (Q u t)+Q u t+2) := by
      field_simp [hQ.ne',hr.ne']
      ring
    have hh : 0 ≤ (4+8/(Real.exp (Q u t)-1)-8/Q u t)*
        (Q u t*(Real.exp (Q u t)-1)) := by rw [hid]; positivity
    exact (mul_nonneg_iff_of_pos_right (mul_pos hQ hr)).mp hh
  have hfactor : 0 ≤ c5CompletedBoseWeight u t-5-5*t*actionProfileLogRate u t := by
    have hid : c5CompletedBoseWeight u t-5-5*t*actionProfileLogRate u t=
        (2*t*E u t)*(4+8/(Real.exp (Q u t)-1)-8/Q u t) := by
      unfold c5CompletedBoseWeight thetaCuspReflectedActionVelocity actionProfileLogRate
      rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring]
      field_simp [ht.ne',hQ.ne',hr.ne']
      ring
    rw [hid]
    exact mul_nonneg (by positivity) hf
  rw [(hasDerivAt_intrinsicActionProfile u ht).deriv]
  have h := mul_nonneg hfactor (intrinsicActionProfile_pos u ht).le
  nlinarith only [h]



end
end RHTower.ThetaCuspDefect
