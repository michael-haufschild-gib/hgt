import GaloisForLFunctions.RHTower.ArithmeticStationaryReflectedTail

/-!
# A positive reserve below the initial-clock sine ceiling

For positive frequency and nonnegative logarithmic height, two further reciprocal
clock derivatives express the difference between the initial reciprocal weight and
the actual sine integral as a nonnegative integral. This halves the positive-mode
ceiling while retaining every stationary term, boundary, and Bernoulli mean.
The cumulative incoming-head comparison and RH remain open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Positive numerator of the second reciprocal-clock dissipation. -/
def positiveClockSecondPolynomial (β u γ : ℝ) : ℝ :=
  β*(β+1)*u^2+(2*(β-2)^2+7*(β-2)+4)*u*γ+(β-1)^2*γ^2

/-- Positive numerator of the third reciprocal-clock dissipation. -/
def positiveClockThirdPolynomial (β u γ : ℝ) : ℝ :=
  β*(β+1)*(β+2)*u^3+(3*(β-2)^3+21*(β-2)^2+40*(β-2)+14)*u^2*γ+
    (3*(β-2)^3+15*(β-2)^2+17*(β-2)+6)*u*γ^2+(β-1)^3*γ^3

/-- The first dissipation divided by the actual phase derivative. -/
def positiveClockSecondWeight (β γ ω x : ℝ) : ℝ :=
  x^(1-β)*(β*ω*x+(β-1)*γ)/(ω*x+γ)^3

/-- Negative derivative of the second reciprocal weight. -/
def positiveClockSecondDissipation (β γ ω x : ℝ) : ℝ :=
  x^(-β)*positiveClockSecondPolynomial β (ω*x) γ/(ω*x+γ)^4

/-- The second dissipation divided by the actual phase derivative. -/
def positiveClockThirdWeight (β γ ω x : ℝ) : ℝ :=
  x^(1-β)*positiveClockSecondPolynomial β (ω*x) γ/(ω*x+γ)^5

/-- Negative derivative of the third reciprocal weight. -/
def positiveClockThirdDissipation (β γ ω x : ℝ) : ℝ :=
  x^(-β)*positiveClockThirdPolynomial β (ω*x) γ/(ω*x+γ)^6

/-- The polynomial forms expose all signs in the required source chamber. -/
theorem positiveClock_polynomials_nonneg {β u γ : ℝ} (hβ : 2 ≤ β) (hu : 0 ≤ u) (hγ : 0 ≤ γ) :
    0 ≤ positiveClockSecondPolynomial β u γ ∧ 0 ≤ positiveClockThirdPolynomial β u γ := by
  have hδ : 0 ≤ β-2 := by linarith
  have hb : 0 ≤ β := by linarith
  have hb1 : 0 ≤ β-1 := by linarith
  constructor
  · unfold positiveClockSecondPolynomial; positivity
  · unfold positiveClockThirdPolynomial; positivity

/-- Both new dissipation densities are nonnegative without a zero premise. -/
theorem positiveClock_dissipations_nonneg {β γ ω x : ℝ} (hβ : 2 ≤ β) (hγ : 0 ≤ γ)
    (hω : 0 < ω) (hx : 0 < x) :
    0 ≤ positiveClockSecondDissipation β γ ω x ∧ 0 ≤ positiveClockThirdDissipation β γ ω x := by
  have hpoly := positiveClock_polynomials_nonneg hβ (mul_pos hω hx).le hγ
  have hd : 0 < ω*x+γ := by positivity
  constructor
  · exact div_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) hpoly.1) (pow_nonneg hd.le _)
  · exact div_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) hpoly.2) (pow_nonneg hd.le _)

/-- Exact second reciprocal-weight derivative, with no sign assumptions needed. -/
theorem hasDerivAt_positiveClockSecondWeight {β γ ω x : ℝ} (hx : 0 < x) (hd : ω*x+γ ≠ 0) :
    HasDerivAt (positiveClockSecondWeight β γ ω) (-positiveClockSecondDissipation β γ ω x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := 1-β) (Or.inl hx.ne')
  have hn := ((hasDerivAt_id x).const_mul (β*ω)).add_const ((β-1)*γ)
  have hden := (((hasDerivAt_id x).const_mul ω).add_const γ).pow 3
  convert! (hp.mul hn).div hden (pow_ne_zero _ hd) using 1
  dsimp only [positiveClockSecondWeight,positiveClockSecondDissipation,positiveClockSecondPolynomial,id,
    Pi.mul_apply,Pi.pow_apply,mul_one]
  rw [show 1-β-1 = -β by ring, ←endpoint_power_identity hx]
  field_simp
  ring

/-- Exact derivative of the second numerator after insertion of the linear frequency. -/
theorem hasDerivAt_positiveClockSecondPolynomial (β γ ω x : ℝ) :
    HasDerivAt (fun x => positiveClockSecondPolynomial β (ω*x) γ)
      (2*β*(β+1)*ω^2*x+(2*(β-2)^2+7*(β-2)+4)*ω*γ) x := by
  have hu := (hasDerivAt_id x).const_mul ω
  have h := (((hu.pow 2).const_mul (β*(β+1))).add
    ((hu.const_mul (2*(β-2)^2+7*(β-2)+4)).mul_const γ)).add_const ((β-1)^2*γ^2)
  convert! h using 1
  dsimp only [positiveClockSecondPolynomial,id,Pi.mul_apply,Pi.pow_apply]
  ring

/-- Exact third reciprocal-weight derivative, including every lower-degree term. -/
theorem hasDerivAt_positiveClockThirdWeight {β γ ω x : ℝ} (hx : 0 < x) (hd : ω*x+γ ≠ 0) :
    HasDerivAt (positiveClockThirdWeight β γ ω) (-positiveClockThirdDissipation β γ ω x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := 1-β) (Or.inl hx.ne')
  have hn := hasDerivAt_positiveClockSecondPolynomial β γ ω x
  have hden := (((hasDerivAt_id x).const_mul ω).add_const γ).pow 5
  convert! (hp.mul hn).div hden (pow_ne_zero _ hd) using 1
  dsimp only [positiveClockThirdWeight,positiveClockThirdDissipation,positiveClockSecondPolynomial,
    positiveClockThirdPolynomial,id,Pi.mul_apply,Pi.pow_apply,mul_one]
  rw [show 1-β-1 = -β by ring, ←endpoint_power_identity hx]
  field_simp
  ring

/-- The second weight recovers the actual first dissipation under the clock. -/
theorem positiveClockSecondWeight_mul_phase_deriv {β γ ω x : ℝ} (hx : 0 < x) (_hd : ω*x+γ ≠ 0) :
    positiveClockSecondWeight β γ ω x*(ω+γ/x) = reciprocalLogDissipation β γ ω x := by
  unfold positiveClockSecondWeight reciprocalLogDissipation
  rw [←endpoint_power_identity hx]
  field_simp
  ring

/-- The third weight recovers the second dissipation under the clock. -/
theorem positiveClockThirdWeight_mul_phase_deriv {β γ ω x : ℝ} (hx : 0 < x) (_hd : ω*x+γ ≠ 0) :
    positiveClockThirdWeight β γ ω x*(ω+γ/x) = positiveClockSecondDissipation β γ ω x := by
  unfold positiveClockThirdWeight positiveClockSecondDissipation
  rw [←endpoint_power_identity hx]
  field_simp

/-- Inverse powers of the positive-frequency clock denominator vanish at infinity. -/
theorem tendsto_positiveClock_inverse_power {ω : ℝ} (hω : 0 < ω) (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => (ω*x+γ)⁻¹^n) atTop (𝓝 0) := by
  have hd : Tendsto (fun x : ℝ => ω*x+γ) atTop atTop :=
    tendsto_atTop_add_const_right atTop γ ((tendsto_const_mul_atTop_of_pos hω).mpr tendsto_id)
  have hi := (tendsto_inv_atTop_zero.comp hd).pow n
  simpa only [zero_pow hn, Function.comp_apply] using hi

/-- The second weight has a genuine zero endpoint at infinity. -/
theorem tendsto_positiveClockSecondWeight {β ω : ℝ} (hβ : 1 < β) (hω : 0 < ω) (γ : ℝ) :
    Tendsto (positiveClockSecondWeight β γ ω) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x^(1-β)) atTop (𝓝 0) := by
    simpa only [show -(β-1)=1-β by ring] using tendsto_rpow_neg_atTop (by linarith : 0 < β-1)
  have h2 := tendsto_positiveClock_inverse_power hω γ (by norm_num : (2:ℕ) ≠ 0)
  have h3 := tendsto_positiveClock_inverse_power hω γ (by norm_num : (3:ℕ) ≠ 0)
  have h := hp.mul ((h2.const_mul β).sub (h3.const_mul γ))
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop ((|γ|+1)/ω)] with x hx
  have hd : ω*x+γ ≠ 0 := by
    have he := (div_lt_iff₀ hω).mp hx
    have ha := neg_abs_le γ
    nlinarith
  dsimp only [positiveClockSecondWeight]
  field_simp
  ring

/-- The third weight has a genuine zero endpoint at infinity. -/
theorem tendsto_positiveClockThirdWeight {β ω : ℝ} (hβ : 1 < β) (hω : 0 < ω) (γ : ℝ) :
    Tendsto (positiveClockThirdWeight β γ ω) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x^(1-β)) atTop (𝓝 0) := by
    simpa only [show -(β-1)=1-β by ring] using tendsto_rpow_neg_atTop (by linarith : 0 < β-1)
  have h3 := tendsto_positiveClock_inverse_power hω γ (by norm_num : (3:ℕ) ≠ 0)
  have h4 := tendsto_positiveClock_inverse_power hω γ (by norm_num : (4:ℕ) ≠ 0)
  have h5 := tendsto_positiveClock_inverse_power hω γ (by norm_num : (5:ℕ) ≠ 0)
  have h := hp.mul (((h3.const_mul (β*(β+1))).sub (h4.const_mul ((3*β+2)*γ))).add (h5.const_mul (3*γ^2)))
  simp only [mul_zero,sub_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop ((|γ|+1)/ω)] with x hx
  have hd : ω*x+γ ≠ 0 := by
    have he := (div_lt_iff₀ hω).mp hx
    have ha := neg_abs_le γ
    nlinarith
  dsimp only [positiveClockThirdWeight,positiveClockSecondPolynomial]
  field_simp
  ring

/-- The nonnegative derivative densities are absolutely integrable from their proved zero limits. -/
theorem integrable_positiveClock_dissipations {a β γ ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hγ : 0 ≤ γ) (hω : 0 < ω) :
    IntegrableOn (positiveClockSecondDissipation β γ ω) (Ioi a) ∧
      IntegrableOn (positiveClockThirdDissipation β γ ω) (Ioi a) := by
  have hd (x : ℝ) (hx : a ≤ x) : ω*x+γ ≠ 0 := ne_of_gt (by have := ha.trans_le hx; positivity)
  constructor
  · have h := integrableOn_Ioi_deriv_of_nonpos'
      (fun x (hx : x ∈ Ici a) => hasDerivAt_positiveClockSecondWeight (β := β) (ha.trans_le hx) (hd x hx))
      (fun x (hx : x ∈ Ioi a) => neg_nonpos.mpr (positiveClock_dissipations_nonneg hβ.le hγ hω (ha.trans hx)).1)
      (tendsto_positiveClockSecondWeight (by linarith : 1 < β) hω γ)
    exact integrable_neg_iff.mp h
  · have h := integrableOn_Ioi_deriv_of_nonpos'
      (fun x (hx : x ∈ Ici a) => hasDerivAt_positiveClockThirdWeight (β := β) (ha.trans_le hx) (hd x hx))
      (fun x (hx : x ∈ Ioi a) => neg_nonpos.mpr (positiveClock_dissipations_nonneg hβ.le hγ hω (ha.trans hx)).2)
      (tendsto_positiveClockThirdWeight (by linarith : 1 < β) hω γ)
    exact integrable_neg_iff.mp h


/-- A vanishing real amplitude times a uniformly bounded factor has zero limit. -/
theorem tendsto_positiveClock_bounded_product {f g : ℝ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ x, ‖g x‖ ≤ C) :
    Tendsto (fun x => f x*g x) atTop (𝓝 0) := by
  have h := hf.norm.mul_const C
  simp only [norm_zero, zero_mul] at h
  apply squeeze_zero_norm' (Eventually.of_forall (fun x => ?_)) h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)

/-- Absolute integrability of a density times the actual sine, cosine, and cosine defect. -/
theorem integrable_positiveClock_trig {a γ ω : ℝ} {f : ℝ → ℝ} (ha : 0 < a)
    (hf : IntegrableOn f (Ioi a)) :
    IntegrableOn (fun x => f x*Real.sin (anchoredLogPhase a γ ω x)) (Ioi a) ∧
    IntegrableOn (fun x => f x*Real.cos (anchoredLogPhase a γ ω x)) (Ioi a) ∧
    IntegrableOn (fun x => f x*(1-Real.cos (anchoredLogPhase a γ ω x))) (Ioi a) := by
  have hp := continuousOn_anchoredLogPhase (γ := γ) (ω := ω) ha
  constructor
  · apply hf.mul_bdd (c := 1) (Real.continuous_sin.comp_continuousOn hp |>.aestronglyMeasurable measurableSet_Ioi)
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,Function.comp_apply] using Real.abs_sin_le_one _)
  constructor
  · apply hf.mul_bdd (c := 1) (Real.continuous_cos.comp_continuousOn hp |>.aestronglyMeasurable measurableSet_Ioi)
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,Function.comp_apply] using Real.abs_cos_le_one _)
  · apply hf.mul_bdd (c := 2)
      ((continuousOn_const.sub (Real.continuous_cos.comp_continuousOn hp)).aestronglyMeasurable measurableSet_Ioi)
    exact ae_of_all _ (fun x => by
      dsimp only [Pi.sub_apply,Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      linarith [Real.neg_one_le_cos (anchoredLogPhase a γ ω x)])

/-- First reserve integration: the actual cosine reserve equals the second-density sine. -/
theorem integral_positiveClock_cos_eq_sin {a β γ ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hγ : 0 ≤ γ) (hω : 0 < ω) :
    (∫ x in Ioi a, reciprocalLogDissipation β γ ω x*Real.cos (anchoredLogPhase a γ ω x)) =
      ∫ x in Ioi a, positiveClockSecondDissipation β γ ω x*Real.sin (anchoredLogPhase a γ ω x) := by
  have hd : 0 < ω*a+γ := by positivity
  have hβ1 : 1 < β := by linarith
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => Real.sin (anchoredLogPhase a γ ω x))
        ((ω+γ/x)*Real.cos (anchoredLogPhase a γ ω x)) x := by
    convert! (hasDerivAt_anchoredLogPhase (ha.trans hx)).sin using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      positiveClockSecondWeight β γ ω x*((ω+γ/x)*Real.cos (anchoredLogPhase a γ ω x)) =
        reciprocalLogDissipation β γ ω x*Real.cos (anchoredLogPhase a γ ω x) := by
    rw [←mul_assoc,positiveClockSecondWeight_mul_phase_deriv (ha.trans hx) (logPhase_den_pos hω hd hx.le).ne']
  have hb : Tendsto (fun x => positiveClockSecondWeight β γ ω x*Real.sin (anchoredLogPhase a γ ω x))
      (𝓝[>] a) (𝓝 0) := by
    have hc : ContinuousAt (fun x => positiveClockSecondWeight β γ ω x*Real.sin (anchoredLogPhase a γ ω x)) a := (hasDerivAt_positiveClockSecondWeight (β := β) ha hd.ne').continuousAt.mul
      ((hasDerivAt_anchoredLogPhase (a := a) (γ := γ) (ω := ω) ha).sin).continuousAt
    simpa [anchoredLogPhase] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have htop' := tendsto_positiveClock_bounded_product (tendsto_positiveClockSecondWeight hβ1 hω γ)
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (anchoredLogPhase a γ ω x))
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_positiveClockSecondWeight (ha.trans hx) (logPhase_den_pos hω hd hx.le).ne') hv
    (((integrable_positiveClock_trig (γ := γ) (ω := ω) ha (integrable_reciprocalLogDissipation ha hβ1 hω hd)).2.1).congr_fun
      (fun x hx => (he x hx).symm) measurableSet_Ioi)
    (((integrable_positiveClock_trig (γ := γ) (ω := ω) ha (integrable_positiveClock_dissipations ha hβ hγ hω).1).1).neg.congr_fun
      (fun x _ => by simp) measurableSet_Ioi) hb htop'
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul,integral_neg,sub_self,zero_sub,neg_neg] using hi

/-- Second reserve integration: the second-density sine is a nonnegative third-density defect. -/
theorem integral_positiveClock_sin_eq_defect {a β γ ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hγ : 0 ≤ γ) (hω : 0 < ω) :
    (∫ x in Ioi a, positiveClockSecondDissipation β γ ω x*Real.sin (anchoredLogPhase a γ ω x)) =
      ∫ x in Ioi a, positiveClockThirdDissipation β γ ω x*(1-Real.cos (anchoredLogPhase a γ ω x)) := by
  have hd : 0 < ω*a+γ := by positivity
  have hβ1 : 1 < β := by linarith
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => 1-Real.cos (anchoredLogPhase a γ ω x))
        ((ω+γ/x)*Real.sin (anchoredLogPhase a γ ω x)) x := by
    convert! ((hasDerivAt_anchoredLogPhase (ha.trans hx)).cos).const_sub 1 using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      positiveClockThirdWeight β γ ω x*((ω+γ/x)*Real.sin (anchoredLogPhase a γ ω x)) =
        positiveClockSecondDissipation β γ ω x*Real.sin (anchoredLogPhase a γ ω x) := by
    rw [←mul_assoc,positiveClockThirdWeight_mul_phase_deriv (ha.trans hx) (logPhase_den_pos hω hd hx.le).ne']
  have hb : Tendsto (fun x => positiveClockThirdWeight β γ ω x*(1-Real.cos (anchoredLogPhase a γ ω x)))
      (𝓝[>] a) (𝓝 0) := by
    have hc : ContinuousAt (fun x => positiveClockThirdWeight β γ ω x*(1-Real.cos (anchoredLogPhase a γ ω x))) a := (hasDerivAt_positiveClockThirdWeight (β := β) ha hd.ne').continuousAt.mul
      (continuousAt_const.sub ((hasDerivAt_anchoredLogPhase (a := a) (γ := γ) (ω := ω) ha).cos).continuousAt)
    simpa [anchoredLogPhase] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have htop := tendsto_positiveClock_bounded_product (tendsto_positiveClockThirdWeight hβ1 hω γ)
    (g := fun x => 1-Real.cos (anchoredLogPhase a γ ω x)) (C := 2) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      linarith [Real.neg_one_le_cos (anchoredLogPhase a γ ω x)])
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_positiveClockThirdWeight (ha.trans hx) (logPhase_den_pos hω hd hx.le).ne') hv
    (((integrable_positiveClock_trig (γ := γ) (ω := ω) ha (integrable_positiveClock_dissipations ha hβ hγ hω).1).1).congr_fun
      (fun x hx => (he x hx).symm) measurableSet_Ioi)
    (((integrable_positiveClock_trig (γ := γ) (ω := ω) ha (integrable_positiveClock_dissipations ha hβ hγ hω).2).2.2).neg.congr_fun
      (fun x _ => by simp) measurableSet_Ioi) hb htop
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul,integral_neg,sub_self,zero_sub,neg_neg] using hi

/-- Exact reserve between the initial weight and the actual sine integral. -/
theorem integral_anchoredLogSine_exact_positive_reserve {a β γ ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hγ : 0 ≤ γ) (hω : 0 < ω) :
    reciprocalLogWeight β γ ω a-(∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x)) =
      ∫ x in Ioi a, positiveClockThirdDissipation β γ ω x*(1-Real.cos (anchoredLogPhase a γ ω x)) := by
  have hd : 0 < ω*a+γ := by positivity
  have hβ1 : 1 < β := by linarith
  rw [←integral_positiveClock_sin_eq_defect ha hβ hγ hω,←integral_positiveClock_cos_eq_sin ha hβ hγ hω,
    integral_anchoredLogSine_eq_budget ha hβ1 hω hd,←integral_reciprocalLogDissipation ha hβ1 hω hd]
  have he : (fun x => reciprocalLogDissipation β γ ω x*(1-Real.cos (anchoredLogPhase a γ ω x))) =
      (fun x => reciprocalLogDissipation β γ ω x-reciprocalLogDissipation β γ ω x*Real.cos (anchoredLogPhase a γ ω x)) := by
    funext x; ring
  rw [he,integral_sub (integrable_reciprocalLogDissipation ha hβ1 hω hd)
    (integrable_positiveClock_trig (γ := γ) (ω := ω) ha (integrable_reciprocalLogDissipation ha hβ1 hω hd)).2.1]
  ring

/-- The actual positive-frequency sine has the sharper initial-weight ceiling. -/
theorem integral_anchoredLogSine_le_initial_weight {a β γ ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hγ : 0 ≤ γ) (hω : 0 < ω) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x)) ≤ reciprocalLogWeight β γ ω a := by
  apply sub_nonneg.mp
  rw [integral_anchoredLogSine_exact_positive_reserve ha hβ hγ hω]
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact mul_nonneg (positiveClock_dissipations_nonneg hβ.le hγ hω (ha.trans hx)).2
    (sub_nonneg.mpr (Real.cos_le_one _))


/-- The positive-frequency ceiling retains the exact frequency and height. -/
theorem scaledBernoulliFourierAtom_pos_le_half_ceiling {s : ℂ} (hs : 0 < s.re) (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k) :
    (scaledBernoulliFourierAtom s N k).im ≤ bernoulliModeWeight k/(2*Real.pi*k*N+s.im) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw : 0 < 2*Real.pi*(k:ℝ) := by positivity
  rw [scaledBernoulliFourierAtom_im_eq hs hN]
  have hb := integral_anchoredLogSine_le_initial_weight hNp (show 2 < s.re+2 by linarith) ht hw
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Real.rpow_nonneg hNp.le (s.re+1)) (bernoulliModeWeight_nonneg k))
  apply hm.trans_eq
  have hp : (N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2))=1 := by
    rw [← Real.rpow_add hNp, show s.re+1+(1-(s.re+2))=0 by ring, Real.rpow_zero]
  unfold reciprocalLogWeight
  calc
    _ = bernoulliModeWeight k*((N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2)))/(2*Real.pi*k*N+s.im) := by ring
    _ = _ := by rw [hp, mul_one]

/-- Retain stationary atoms exactly and bound all remaining atoms by the positive ceiling. -/
theorem scaledBernoulliFourierAtom_pointwise_le_half_ceiling {s : ℂ} (hs : 0 < s.re) (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    (scaledBernoulliFourierAtom s N k).im ≤ positiveBernoulliWeight k * (1/(2*Real.pi*N+s.im)) +
      if k ∈ stationaryFourierIndices s.im N then (scaledBernoulliFourierAtom s N k).im else 0 := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd : 0 < 2*Real.pi*(N:ℝ)+s.im := by positivity
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [positiveBernoulliWeight, if_neg (not_lt.mpr hk.le), zero_mul, zero_add]
    by_cases hmem : k ∈ stationaryFourierIndices s.im N
    · simp only [if_pos hmem, le_refl]
    · rw [if_neg hmem]
      have hgt : s.im < 2*Real.pi*(-k)*N := by
        by_contra hh
        exact hmem ((mem_stationaryFourierIndices hN).mpr ⟨hk,not_lt.mp hh⟩)
      simpa only [neg_neg] using (scaledBernoulliFourierAtom_neg_im_neg hs hN (neg_pos.mpr hk) (by simpa only [Int.cast_neg] using hgt)).le
  · simp [scaledBernoulliFourierAtom, bernoulliFourierTerm, bernoulliModeWeight_zero, positiveBernoulliWeight]
  · have hmem : k ∉ stationaryFourierIndices s.im N := by
      intro hh
      exact (lt_asymm hk) ((mem_stationaryFourierIndices hN).mp hh).1
    rw [positiveBernoulliWeight, if_pos hk, if_neg hmem, add_zero]
    apply (scaledBernoulliFourierAtom_pos_le_half_ceiling hs ht hN hk).trans
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have hden : 2*Real.pi*N+s.im ≤ 2*Real.pi*(k:ℝ)*N+s.im := by
      nlinarith [mul_nonneg (show 0 ≤ 2*Real.pi*(N:ℝ) by positivity) (sub_nonneg.mpr hkR)]
    have hb := div_le_div_of_nonneg_left (bernoulliModeWeight_nonneg k) hd hden
    convert! hb using 1
    ring

/-- The complete source is bounded by its finite stationary budget plus the explicit signed error. -/
theorem normalizedWeightedRemainder_scaled_im_le_stationary_half_ceiling {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im ≤ stationaryFourierBudget s N +
      1/(24*(2*Real.pi*N+s.im)) - s.im/(12*Complex.normSq (s+1)) := by
  classical
  let F : ℤ → ℝ := fun k => if k ∈ stationaryFourierIndices s.im N then
    (scaledBernoulliFourierAtom s N k).im else 0
  have hF : HasSum F (stationaryFourierBudget s N) := by
    have h : HasSum F (∑ k ∈ stationaryFourierIndices s.im N, F k) :=
      hasSum_sum_of_ne_finset_zero (s := stationaryFourierIndices s.im N)
      (f := F) (fun k hk => by simp [F,hk])
    convert! h using 1
    unfold stationaryFourierBudget
    apply Finset.sum_congr rfl
    intro k hk
    simp [F,hk]
  have hP := summable_positiveBernoulliWeight.hasSum.mul_right (1/(2*Real.pi*N+s.im))
  rw [tsum_positiveBernoulliWeight] at hP
  have h := hasSum_le (scaledBernoulliFourierAtom_pointwise_le_half_ceiling hs ht hN)
    (hasSum_scaledBernoulliFourierAtom_im hs hs1 hN) (hP.add hF)
  have he : (1:ℝ)/24 * (1/(2*Real.pi*N+s.im)) = 1/(24*(2*Real.pi*N+s.im)) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [he] at h
  linarith

/-- A zero requires an explicit finite stationary contribution, including horizontal displacement. -/
theorem stationaryFourierBudget_lowerBound_half_ceiling_at_zero {s : ℂ} (hs : 0 < s.re)
    (hs' : s.re < 1) (ht : 0 ≤ s.im) (hz : riemannZeta s = 0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s))) +
      s.im/(12*Complex.normSq (s+1)) - 1/(24*(2*Real.pi+s.im)) ≤ stationaryFourierBudget s 1 := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs'; norm_num at hs'
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_half_ceiling hs hs1 ht (N := 1) (by rfl)
  rw [normalizedWeightedRemainder_one_eq_boundary hs hs', hz] at h
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one, zero_div, star_zero, sub_zero,
    minimumZeroBoundary_im] at h
  linarith

/-- Full-source inequality with only the pre-saddle head left outside the reflected cancellation bound. -/
theorem normalizedWeightedRemainder_scaled_im_le_incoming_half_ceiling {s : ℂ}
    (hs : 0 < s.re) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im ≤
      (stationaryIncomingSection s N ⌊s.im/(2*Real.pi*N)⌋₊).im+
      stationaryReflectedTailEnvelope s N*‖rawPrefix (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊‖+
      1/(24*(2*Real.pi*N+s.im))-s.im/(12*Complex.normSq (s+1)) := by
  have ht0 : 0 < s.im := zero_lt_one.trans_le ht
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_half_ceiling hs hs1 ht0.le hN
  rw [←stationaryComplexBudget_im ht0.le hN,
    stationaryComplexBudget_eq_incoming_add_reflected hs ht0 hN,Complex.add_im] at h
  have hc := mul_le_mul_of_nonneg_right (norm_stationaryReflectedTailFactor_le hs ht hN)
    (norm_nonneg (rawPrefix (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊))
  rw [←norm_mul] at hc
  have him := (Complex.im_le_norm _).trans hc
  linarith

/-- The zero-forced stationary lower budget transfers to the actual incoming head,
with an explicit bound for the entire outgoing sector. -/
theorem stationaryIncomingSection_im_lowerBound_half_ceiling_at_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s=0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      s.im/(12*Complex.normSq (s+1))-1/(24*(2*Real.pi+s.im))-
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ ≤
        (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  have hs0 : 0 < s.re := by linarith
  have hstat := stationary_cutoff_frequency_le (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))
  simp only [Nat.cast_one,mul_one] at hstat
  have hb := norm_negativeFourierSection_sub_incoming_le_at_zero hs0 hs' ht hz
    (by rfl : 1 ≤ (1:ℕ)) (stationary_unit_cutoff_pos_at_closed_right_zero hs hs' ht hz)
    (by simpa only [Nat.cast_one,mul_one] using hstat)
  have hc : ‖stationaryComplexBudget s 1-stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊‖ ≤
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ := by
    simpa only [stationaryComplexBudget,Nat.cast_one,mul_one] using hb
  have him := Complex.im_le_norm (stationaryComplexBudget s 1-
    stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊)
  rw [Complex.sub_im,stationaryComplexBudget_im (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))] at him
  have hl := stationaryFourierBudget_lowerBound_half_ceiling_at_zero hs0 hs' (by linarith) hz
  linarith

/-- The sharper positive ceiling leaves strictly more than half the actual Bernoulli mean. -/
theorem positiveFourier_half_ceiling_reserve {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    s.im/(24*Complex.normSq (s+1)) <
      s.im/(12*Complex.normSq (s+1))-1/(24*(2*Real.pi*N+s.im)) := by
  have h := positiveFourier_ceiling_lt_mean hs hs' ht hN
  have h1 : 1/(12*(2*Real.pi*N+s.im)) = 2*(1/(24*(2*Real.pi*N+s.im))) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have h2 : s.im/(12*Complex.normSq (s+1)) = 2*(s.im/(24*Complex.normSq (s+1))) := by ring
  rw [h1,h2] at h
  rw [h2]
  linarith

/-- Actual source comparison retains a strict half-mean margin below the stationary sector. -/
theorem normalizedWeightedRemainder_scaled_im_lt_stationary_half_mean {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im <
      stationaryFourierBudget s N-s.im/(24*Complex.normSq (s+1)) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_half_ceiling hs hs1 (by linarith) hN
  have hr := positiveFourier_half_ceiling_reserve hs hs' ht hN
  linarith

/-- The zero-forced unit budget has a half-mean margin in addition to horizontal displacement. -/
theorem stationaryFourierBudget_lowerBound_half_mean_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      s.im/(24*Complex.normSq (s+1)) < stationaryFourierBudget s 1 := by
  have h := stationaryFourierBudget_lowerBound_half_ceiling_at_zero hs hs' (by linarith) hz
  have hr := positiveFourier_half_ceiling_reserve hs hs'.le ht (by rfl : 1 ≤ (1:ℕ))
  simp only [Nat.cast_one,mul_one] at hr
  linarith

/-- The retained incoming head inherits the strict half-mean margin with the complete outgoing error. -/
theorem stationaryIncomingSection_im_lowerBound_half_mean_at_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s=0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      s.im/(24*Complex.normSq (s+1))-
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ <
        (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  have h := stationaryIncomingSection_im_lowerBound_half_ceiling_at_zero hs hs' ht hz
  have hr := positiveFourier_half_ceiling_reserve (by linarith : 0 < s.re) hs'.le ht (by rfl : 1 ≤ (1:ℕ))
  simp only [Nat.cast_one,mul_one] at hr
  linarith

end RHTower.DeletionMixedRefinement
