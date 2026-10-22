import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CoupledShapeDynamics
/-! Source-linked energy reserves for the actual denominator clock.
The projective curvature at the physical interval endpoint controls its
whole reflected source. Integrating the resulting acceleration reserve
preserves the actual center scale in the clock-coordinate energy cone.
Global inverse-source/clock order is not asserted. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction
local notation "Z" => curvatureShapeAction
local notation "y" => completedFirstDenominator
local notation "d" => completedLocalDenominator
local notation "k" => denominatorClockRate

private theorem positive_from_chamber_derivative {f g : ℝ → ℝ} {u t : ℝ}
    (ht : 0 < t) (htu : t ≤ u) (h0 : f 0=0)
    (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, 0 < s → s < u → 0 < g s) : 0 < f t := by
  have hm : StrictMonoOn f (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 u := by simpa only [interior_Icc] using hs
      rw [(hd s).deriv]
      exact hg s hs'.1 hs'.2
  simpa only [h0] using hm ⟨le_rfl,ht.le.trans htu⟩ ⟨ht.le,htu⟩ ht
private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem p_deriv (u s : ℝ) : HasDerivAt (p u) (r u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem Q_deriv (u s : ℝ) : HasDerivAt (Q u) (2*E u s) s := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u s using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring
private theorem r_upper {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) : r u s < 9*e u s := by
  have hp := source_projective_upper (show 0 ≤ u+s by linarith)
  have hm := source_projective_upper (sub_nonneg.mpr hsu)
  unfold shapeCurvatureSecond completedCurvatureEven
  linarith only [hp,hm]
private theorem p_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : p u t < 9*E u t := by
  have hd (s : ℝ) : HasDerivAt (fun s => 9*E u s-p u s) (9*e u s-r u s) s :=
    ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul 9).sub (p_deriv u s)
  have hh := positive_from_chamber_derivative ht htu
    (by simp [completedDecayEvenPrimitive_zero,shapeCurvatureSlope]) hd
    (fun s hs hsu => sub_pos.mpr (r_upper hs.le hsu.le))
  exact sub_pos.mp hh
private theorem curvature_gap_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    e u t-c u < 9*Q u t/2 := by
  have hd (s : ℝ) : HasDerivAt (fun s => 9*Q u s/2-e u s+c u) (9*E u s-p u s) s := by
    convert! ((((Q_deriv u s).const_mul 9).div_const 2).sub
      (hasDerivAt_completedCurvatureEven u s)).add_const (c u) using 1
    dsimp only [shapeCurvatureSlope]
    ring
  have hh := positive_from_chamber_derivative ht htu
    (by simp [Q_zero,completedCurvatureEven]) hd
    (fun s hs hsu => sub_pos.mpr (p_upper hs hsu.le))
  linarith only [hh]
private theorem action_le_Z {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : Q u t ≤ Z u t := by
  have hh := two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
    (fun x _ => (thetaCuspLogCurvatureJetTwo_pos_all x).le)
  unfold thetaCuspReflectedActionVelocity at hh
  rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hh
  unfold curvatureShapeAction
  linarith only [hh]

/-- The clock acceleration is controlled by its actual accumulated source coordinate. -/
theorem clockAcceleration_lt_sourceCoordinate {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    d u t < c u*(2+Z u t) := by
  have he := curvature_gap_upper ht htu
  have hp := mul_lt_mul_of_pos_left (p_upper ht htu) ht
  have hq := action_le_Z ht htu
  have hc := mul_lt_mul_of_pos_right (sourceCurvature_gt_eighteen (ht.le.trans htu))
    (show 0 < Z u t from mul_pos ht (E_pos u ht))
  have hd : d u t=2*e u t+t*p u t := rfl
  change Q u t ≤ t*E u t at hq
  change 18*(t*E u t)<c u*(t*E u t) at hc
  rw [hd]
  unfold curvatureShapeAction
  nlinarith only [he,hp,hq,hc]

/-- Source-linked energy of the actual integrated clock coordinate. -/
def intrinsicClockEnergy (u t : ℝ) : ℝ := c u*Z u t*(4+Z u t)-(y u t)^2

theorem hasDerivAt_intrinsicClockEnergy (u t : ℝ) :
    HasDerivAt (intrinsicClockEnergy u) (2*y u t*(c u*(2+Z u t)-d u t)) t := by
  have hZ : HasDerivAt (Z u) (y u t) t := hasDerivAt_mul_completedDecayEvenPrimitive u t
  have hh := (((hZ.const_mul (c u)).mul (hZ.const_add 4)).sub
    ((hasDerivAt_completedFirstDenominator u t).pow 2))
  convert! hh using 1
  ring

theorem intrinsicClockEnergy_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < intrinsicClockEnergy u t := by
  apply positive_from_chamber_derivative ht htu
    (by simp [intrinsicClockEnergy,curvatureShapeAction,completedFirstDenominator,completedDecayEvenPrimitive_zero])
    (hasDerivAt_intrinsicClockEnergy u)
  intro s hs hsu
  exact mul_pos (mul_pos (by norm_num) (completedFirstDenominator_pos u hs))
    (sub_pos.mpr (clockAcceleration_lt_sourceCoordinate hs hsu.le))

/-- The actual clock coordinate lies inside its source-energy cone. -/
theorem denominatorClockCoordinate_energy_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (k u*y u t)^2 < 18*Z u t+(9/2)*(Z u t)^2 := by
  have hg := intrinsicClockEnergy_pos ht htu
  have hk := denominatorClockRate_sq u
  have hh := mul_pos (sq_pos_of_pos (denominatorClockRate_pos u)) hg
  have hkc : (k u)^2*c u=9/2 := by nlinarith only [hk]
  unfold intrinsicClockEnergy at hh
  have hid : (k u)^2*(c u*Z u t*(4+Z u t)-(y u t)^2)=
      18*Z u t+(9/2)*(Z u t)^2-(k u*y u t)^2 := by
    calc
      _=((k u)^2*c u)*Z u t*(4+Z u t)-(k u*y u t)^2 := by ring
      _=_ := by rw [hkc]; ring
  rw [hid] at hh
  exact sub_pos.mp hh


/-- Actual projective curvature at the left endpoint of the physical interval. -/
def intervalProjectiveCurvature (u t : ℝ) : ℝ :=
  thetaCuspCompletedCurvatureProjectiveRatio (u-t)

private theorem intervalProjectiveCurvature_pos (u t : ℝ) : 0 < intervalProjectiveCurvature u t := by
  unfold intervalProjectiveCurvature thetaCuspCompletedCurvatureProjectiveRatio
  exact div_pos (thetaCuspLogCurvatureJetTwo_pos_all (u-t)) (thetaCuspLogCurvature_pos (u-t))

private theorem r_interval_upper {u t s : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hs : s ∈ Icc 0 t) : r u s < intervalProjectiveCurvature u t*e u s := by
  have ha : 0 ≤ u-t := sub_nonneg.mpr htu
  have hp : 0 ≤ u+s := by linarith [hs.1]
  have hm : 0 ≤ u-s := by linarith [hs.2]
  have hplus := projectiveRatio_strictAntiOn ha hp (show u-t < u+s by linarith [hs.1])
  have hminus := projectiveRatio_strictAntiOn.antitoneOn ha hm (show u-t ≤ u-s by linarith [hs.2])
  change thetaCuspLogCurvatureJetTwo (u+s)/c (u+s) < intervalProjectiveCurvature u t at hplus
  change thetaCuspLogCurvatureJetTwo (u-s)/c (u-s) ≤ intervalProjectiveCurvature u t at hminus
  have hplus' := (div_lt_iff₀ (thetaCuspLogCurvature_pos (u+s))).mp hplus
  have hminus' := (div_le_iff₀ (thetaCuspLogCurvature_pos (u-s))).mp hminus
  unfold shapeCurvatureSecond completedCurvatureEven
  nlinarith only [hplus',hminus']

private theorem p_interval_upper {u t s : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hs : 0 < s) (hst : s ≤ t) : p u s < intervalProjectiveCurvature u t*E u s := by
  have hd (v : ℝ) : HasDerivAt (fun v => intervalProjectiveCurvature u t*E u v-p u v)
      (intervalProjectiveCurvature u t*e u v-r u v) v :=
    ((hasDerivAt_completedDecayEvenPrimitive u v).const_mul _).sub (p_deriv u v)
  have hh := positive_from_chamber_derivative hs hst
    (by simp [completedDecayEvenPrimitive_zero,shapeCurvatureSlope]) hd
    (fun v hv hvt => sub_pos.mpr (r_interval_upper ht htu ⟨hv.le,hvt.le⟩))
  exact sub_pos.mp hh

private theorem curvature_gap_interval_upper {u t s : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hs : 0 < s) (hst : s ≤ t) :
    e u s-c u < intervalProjectiveCurvature u t*Q u s/2 := by
  have hd (v : ℝ) : HasDerivAt (fun v => intervalProjectiveCurvature u t*Q u v/2-e u v+c u)
      (intervalProjectiveCurvature u t*E u v-p u v) v := by
    convert! ((((Q_deriv u v).const_mul _).div_const 2).sub
      (hasDerivAt_completedCurvatureEven u v)).add_const (c u) using 1
    dsimp only [shapeCurvatureSlope]
    ring
  have hh := positive_from_chamber_derivative hs hst
    (by simp [Q_zero,completedCurvatureEven]) hd
    (fun v hv hvt => sub_pos.mpr (p_interval_upper ht htu hv hvt.le))
  linarith only [hh]

/-- Acceleration retains the actual source curvature throughout the same interval. -/
theorem clockAcceleration_lt_intervalSource {u t s : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hs : 0 < s) (hst : s ≤ t) :
    d u s < 2*c u+2*intervalProjectiveCurvature u t*Z u s := by
  have he := curvature_gap_interval_upper ht htu hs hst
  have hp := mul_lt_mul_of_pos_left (p_interval_upper ht htu hs hst) hs
  have hq := mul_le_mul_of_nonneg_left (action_le_Z hs (hst.trans htu))
    (intervalProjectiveCurvature_pos u t).le
  have hd : d u s=2*e u s+s*p u s := rfl
  change intervalProjectiveCurvature u t*Q u s ≤ intervalProjectiveCurvature u t*(s*E u s) at hq
  rw [hd]
  unfold curvatureShapeAction
  nlinarith only [he,hp,hq]

/-- A source-specific energy reserve; the interval curvature is frozen only at its actual endpoint. -/
def projectiveClockEnergy (u t s : ℝ) : ℝ :=
  4*c u*Z u s+2*intervalProjectiveCurvature u t*(Z u s)^2-(y u s)^2

theorem hasDerivAt_projectiveClockEnergy (u t s : ℝ) :
    HasDerivAt (projectiveClockEnergy u t)
      (2*y u s*(2*c u+2*intervalProjectiveCurvature u t*Z u s-d u s)) s := by
  have hZ : HasDerivAt (Z u) (y u s) s := hasDerivAt_mul_completedDecayEvenPrimitive u s
  have hh := (((hZ.const_mul (4*c u)).add
    ((hZ.pow 2).const_mul (2*intervalProjectiveCurvature u t))).sub
    ((hasDerivAt_completedFirstDenominator u s).pow 2))
  convert! hh using 1
  ring

theorem projectiveClockEnergy_pos {u t s : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hs : 0 < s) (hst : s ≤ t) : 0 < projectiveClockEnergy u t s := by
  apply positive_from_chamber_derivative hs hst
    (by simp [projectiveClockEnergy,curvatureShapeAction,completedFirstDenominator,completedDecayEvenPrimitive_zero])
    (hasDerivAt_projectiveClockEnergy u t)
  intro v hv hvt
  exact mul_pos (mul_pos (by norm_num) (completedFirstDenominator_pos u hv))
    (sub_pos.mpr (clockAcceleration_lt_intervalSource ht htu hv hvt.le))

/-- Full source-dependent clock-coordinate energy, including its actual center scale. -/
theorem denominatorClockCoordinate_projective_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (k u*y u t)^2 < 18*Z u t+(9*intervalProjectiveCurvature u t/c u)*(Z u t)^2 := by
  have hg := projectiveClockEnergy_pos ht htu ht le_rfl
  have hk := denominatorClockRate_sq u
  have hh := mul_pos (sq_pos_of_pos (denominatorClockRate_pos u)) hg
  have hkc : (k u)^2*c u=9/2 := by nlinarith only [hk]
  have hk' : (k u)^2=9/(2*c u) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (thetaCuspLogCurvature_pos u).ne')).mpr
    exact hk
  unfold projectiveClockEnergy at hh
  have hid : (k u)^2*(4*c u*Z u t+2*intervalProjectiveCurvature u t*(Z u t)^2-(y u t)^2)=
      18*Z u t+(9*intervalProjectiveCurvature u t/c u)*(Z u t)^2-(k u*y u t)^2 := by
    simp only [mul_pow,hk']
    field_simp [(thetaCuspLogCurvature_pos u).ne']
    ring
  rw [hid] at hh
  exact sub_pos.mp hh

end
end RHTower.ThetaCuspDefect
