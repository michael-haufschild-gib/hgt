import GaloisForLFunctions.RHTower.ArithmeticStationaryEndpointOrientation
/-!
# Stationary tail quadrant and interior phase comparison

A second integration by parts gives an exact strictly positive cosine budget
for the actual logarithmic phase reanchored at its saddle. Explicit estimates
compensate the higher reciprocal poles and discharge every endpoint and
integrability obligation. Together with the sine budget, the outgoing complex
tail lies in the open fourth quadrant.

The original signed source splits into its finite head and the phase-rotated
cosine and sine tails. A saddle phase in `[pi/2,pi]` forces strict positivity
of the literal negative-frequency Bernoulli atom. This source law has no zero
premise; it does not compare the full stationary sum with the opposing unit
terms or prove RH.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The actual first dissipation divided by the stationary clock derivative. -/
def stationaryCosWeight (a β ω x : ℝ) : ℝ :=
  x^(1-β)*(β*(x-a)+a)/(ω^2*(x-a)^3)

/-- The negative derivative of the second reciprocal weight, with positive numerator. -/
def stationaryCosDissipation (a β ω x : ℝ) : ℝ :=
  x^(-β)*((β-1)*(β*(x-a)^2+a*(x-a))+x*(2*β*(x-a)+3*a))/(ω^2*(x-a)^4)

/-- The inverse logarithmic inequality gives a quadratic anchor-distance bound for the exact phase. -/
theorem endpoint_phase_le_quadratic {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : a < x) :
    anchoredLogPhase a (-ω*a) ω x ≤ ω*(x-a)^2/x := by
  have hx0 := ha.trans hx
  have hl := Real.log_le_sub_one_of_pos (div_pos ha hx0)
  rw [Real.log_div ha.ne' hx0.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl (mul_pos hω ha).le
  have he : ω*(x-a)+ω*a*(a/x-1) = ω*(x-a)^2/x := by field_simp; ring
  unfold anchoredLogPhase
  rw [← he]
  nlinarith

/-- The sine factor compensates two powers of anchor distance. -/
theorem endpoint_sin_abs_le_quadratic {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : a < x) :
    |Real.sin (anchoredLogPhase a (-ω*a) ω x)| ≤ ω*(x-a)^2/x := by
  exact (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg (endpoint_phase_bounds ha hω hx.le).1)).trans
    (endpoint_phase_le_quadratic ha hω hx)

/-- The cosine defect compensates four powers of anchor distance. -/
theorem endpoint_cos_defect_le_quartic {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : a < x) :
    1-Real.cos (anchoredLogPhase a (-ω*a) ω x) ≤ ω^2*(x-a)^4/(2*x^2) := by
  have h0 := (endpoint_phase_bounds ha hω hx.le).1
  have h1 := endpoint_phase_le_quadratic ha hω hx
  have hc := Real.one_sub_sq_div_two_le_cos (x := anchoredLogPhase a (-ω*a) ω x)
  have hs : (anchoredLogPhase a (-ω*a) ω x)^2 ≤ (ω*(x-a)^2/x)^2 := by nlinarith
  have he : (ω*(x-a)^2/x)^2/2 = ω^2*(x-a)^4/(2*x^2) := by field_simp
  rw [← he]
  linarith

/-- The second reciprocal weight is strictly positive beyond the anchor. -/
theorem stationaryCosWeight_pos {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) : 0 < stationaryCosWeight a β ω x := by
  have hx0 := ha.trans hx
  have hy : 0 < x-a := sub_pos.mpr hx
  have hβ0 : 0 < β := by linarith
  unfold stationaryCosWeight
  positivity

/-- The second reciprocal dissipation is strictly positive beyond the anchor. -/
theorem stationaryCosDissipation_pos {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) : 0 < stationaryCosDissipation a β ω x := by
  have hx0 := ha.trans hx
  have hy : 0 < x-a := sub_pos.mpr hx
  have hβ0 : 0 < β := by linarith
  have hβ1 : 0 < β-1 := by linarith
  unfold stationaryCosDissipation
  positivity

/-- Exact derivative of the second reciprocal weight, with the literal power retained. -/
theorem hasDerivAt_stationaryCosWeight {a β ω x : ℝ} (hx : 0 < x)
    (hω : ω ≠ 0) (hxa : x-a ≠ 0) :
    HasDerivAt (stationaryCosWeight a β ω) (-stationaryCosDissipation a β ω x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := 1-β) (Or.inl hx.ne')
  have hn := (((hasDerivAt_id x).sub_const a).const_mul β).add_const a
  have hd := (((hasDerivAt_id x).sub_const a).pow 3).const_mul (ω^2)
  convert! (hp.mul hn).div hd (mul_ne_zero (pow_ne_zero _ hω) (pow_ne_zero _ hxa)) using 1
  dsimp only [id, mul_one, stationaryCosDissipation, Pi.pow_apply, Pi.mul_apply]
  rw [show 1-β-1 = -β by ring, ← endpoint_power_identity hx]
  field_simp
  ring

/-- The phase derivative recovers the first dissipation exactly. -/
theorem stationaryCosWeight_mul_phase_deriv {a β ω x : ℝ} (hx : 0 < x)
    (hω : ω ≠ 0) (hxa : x-a ≠ 0) :
    stationaryCosWeight a β ω x*(ω+(-ω*a)/x) = reciprocalLogDissipation β (-ω*a) ω x := by
  unfold stationaryCosWeight reciprocalLogDissipation
  rw [← endpoint_power_identity hx]
  rw [show ω*x+(-ω*a)=ω*(x-a) by ring]
  field_simp [hω,hxa]
  ring

/-- The actual sine boundary product has a vanishing power majorant. -/
theorem endpoint_sine_boundary_bound {a β ω x : ℝ} (ha : 0 < a) (hω : 0 < ω)
    (hx : a < x) :
    |reciprocalLogWeight β (-ω*a) ω x*Real.sin (anchoredLogPhase a (-ω*a) ω x)| ≤ x^(-β)*(x-a) := by
  have hx0 := ha.trans hx
  have hy := sub_pos.mpr hx
  have hw : 0 ≤ reciprocalLogWeight β (-ω*a) ω x := by
    unfold reciprocalLogWeight
    exact div_nonneg (Real.rpow_nonneg hx0.le _) (by nlinarith)
  rw [abs_mul,abs_of_nonneg hw]
  calc
    _ ≤ reciprocalLogWeight β (-ω*a) ω x*(ω*(x-a)^2/x) :=
      mul_le_mul_of_nonneg_left (endpoint_sin_abs_le_quadratic ha hω hx) hw
    _ = _ := by
      unfold reciprocalLogWeight
      rw [← endpoint_power_identity hx0,show ω*x+(-ω*a)=ω*(x-a) by ring]
      field_simp [hω.ne',hy.ne']

/-- The first dissipation times sine has an integrable power majorant. -/
theorem endpoint_dissipation_sine_bound {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) :
    |reciprocalLogDissipation β (-ω*a) ω x*Real.sin (anchoredLogPhase a (-ω*a) ω x)| ≤
      (β+1)*x^(-β) := by
  have hx0 := ha.trans hx
  have hy := sub_pos.mpr hx
  have hd := (endpoint_dissipation_pos ha hβ hω hx).le
  rw [abs_mul,abs_of_nonneg hd]
  calc
    _ ≤ reciprocalLogDissipation β (-ω*a) ω x*(ω*(x-a)^2/x) :=
      mul_le_mul_of_nonneg_left (endpoint_sin_abs_le_quadratic ha hω hx) hd
    _ = x^(-β)*(β*(x-a)+a)/x := by
      unfold reciprocalLogDissipation
      rw [show ω*x+(-ω*a)=ω*(x-a) by ring]
      field_simp [hω.ne',hy.ne']
      ring
    _ ≤ _ := by
      apply (div_le_iff₀ hx0).mpr
      have hc : β*(x-a)+a ≤ (β+1)*x := by nlinarith
      have hp := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hx0.le (-β))
      nlinarith

/-- The second boundary product compensates its cubic reciprocal pole. -/
theorem stationaryCos_boundary_bound {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) :
    0 ≤ stationaryCosWeight a β ω x*(1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ∧
    stationaryCosWeight a β ω x*(1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ≤
      (β+1)/2*x^(-β)*(x-a) := by
  have hx0 := ha.trans hx
  have hy := sub_pos.mpr hx
  have hw := (stationaryCosWeight_pos ha hβ hω hx).le
  refine ⟨mul_nonneg hw (sub_nonneg.mpr (Real.cos_le_one _)),?_⟩
  calc
    _ ≤ stationaryCosWeight a β ω x*(ω^2*(x-a)^4/(2*x^2)) :=
      mul_le_mul_of_nonneg_left (endpoint_cos_defect_le_quartic ha hω hx) hw
    _ = x^(-β)*(β*(x-a)+a)*(x-a)/(2*x) := by
      unfold stationaryCosWeight
      rw [← endpoint_power_identity hx0]
      field_simp [hω.ne',hy.ne']
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0 < 2*x)).mpr
      have hc : β*(x-a)+a ≤ (β+1)*x := by nlinarith
      have hp := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hx0.le (-β))) hy.le
      nlinarith

/-- The second positive density compensates its quartic reciprocal pole. -/
theorem stationaryCos_budget_bound {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) :
    0 ≤ stationaryCosDissipation a β ω x*(1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ∧
    stationaryCosDissipation a β ω x*(1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ≤
      (β^2+2*β+2)/2*x^(-β) := by
  have hx0 := ha.trans hx
  have hy := sub_pos.mpr hx
  have hβ0 : 0 < β := by linarith
  have hβ1 : 0 < β-1 := by linarith
  have hd := (stationaryCosDissipation_pos ha hβ hω hx).le
  refine ⟨mul_nonneg hd (sub_nonneg.mpr (Real.cos_le_one _)),?_⟩
  calc
    _ ≤ stationaryCosDissipation a β ω x*(ω^2*(x-a)^4/(2*x^2)) :=
      mul_le_mul_of_nonneg_left (endpoint_cos_defect_le_quartic ha hω hx) hd
    _ = x^(-β)*((β-1)*(β*(x-a)^2+a*(x-a))+x*(2*β*(x-a)+3*a))/(2*x^2) := by
      unfold stationaryCosDissipation
      field_simp [hω.ne',hy.ne']
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0 < 2*x^2)).mpr
      have h1 : (β-1)*(β*(x-a)^2+a*(x-a)) ≤ (β-1)*(β*x^2+x*x) := by
        gcongr <;> linarith
      have h2 : x*(2*β*(x-a)+3*a) ≤ x*(2*β*x+3*x) := by
        gcongr
        linarith
      have hc : (β-1)*(β*(x-a)^2+a*(x-a))+x*(2*β*(x-a)+3*a) ≤ (β^2+2*β+2)*x^2 := by
        nlinarith
      have hp := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hx0.le (-β))
      nlinarith


/-- The first dissipation is continuous on the open half-line. -/
theorem continuousOn_endpoint_dissipation {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ContinuousOn (reciprocalLogDissipation β (-ω*a) ω) (Ioi a) := by
  intro x hx
  have hx0 := ha.trans hx
  have hd : ω*x+(-ω*a) ≠ 0 := ne_of_gt (by have hxa : a < x := hx; nlinarith)
  unfold reciprocalLogDissipation
  have hp := (Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx0.ne')).continuousAt
  have hn : ContinuousAt (fun x : ℝ => (β-1)*(ω*x+(-ω*a))+ω*x) x := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => (ω*x+(-ω*a))^2) x := by fun_prop
  exact ((hp.mul hn).div hden (pow_ne_zero _ hd)).continuousWithinAt

/-- The second dissipation is continuous on the open half-line. -/
theorem continuousOn_stationaryCosDissipation {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ContinuousOn (stationaryCosDissipation a β ω) (Ioi a) := by
  intro x hx
  have hx0 := ha.trans hx
  have hy : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
  unfold stationaryCosDissipation
  have hp := (Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx0.ne')).continuousAt
  have hn : ContinuousAt (fun x : ℝ => (β-1)*(β*(x-a)^2+a*(x-a))+x*(2*β*(x-a)+3*a)) x := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => ω^2*(x-a)^4) x := by fun_prop
  exact ((hp.mul hn).div hden (mul_ne_zero (pow_ne_zero _ hω.ne') (pow_ne_zero _ hy))).continuousWithinAt

/-- The actual second positive density is continuous away from its endpoint. -/
theorem continuousOn_stationaryCosBudget {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ContinuousOn (fun x => stationaryCosDissipation a β ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (Ioi a) :=
  (continuousOn_stationaryCosDissipation ha hω).mul
    (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn (continuousOn_anchoredLogPhase ha)))

/-- The literal decreasing power dominates the anchored cosine integrand. -/
theorem integrable_anchoredLogCos {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β) :
    IntegrableOn (fun x => x^(-β)*Real.cos (anchoredLogPhase a γ ω x)) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha).mul_bdd (c := 1)
    ((Real.continuous_cos.comp_continuousOn (continuousOn_anchoredLogPhase ha)).aestronglyMeasurable measurableSet_Ioi)
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using Real.abs_cos_le_one _)

/-- The first dissipation times sine is absolutely integrable. -/
theorem integrable_endpoint_dissipation_sine {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    IntegrableOn (fun x => reciprocalLogDissipation β (-ω*a) ω x *
      Real.sin (anchoredLogPhase a (-ω*a) ω x)) (Ioi a) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha).const_mul (β+1)).mono'
    (((continuousOn_endpoint_dissipation ha hω).mul
      (Real.continuous_sin.comp_continuousOn (continuousOn_anchoredLogPhase ha))).aestronglyMeasurable measurableSet_Ioi)
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ (fun x hx => by simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply] using endpoint_dissipation_sine_bound ha hβ hω hx)

/-- The second positive density is absolutely integrable. -/
theorem integrable_stationaryCosBudget {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    IntegrableOn (fun x => stationaryCosDissipation a β ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (Ioi a) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha).const_mul ((β^2+2*β+2)/2)).mono'
    ((continuousOn_stationaryCosBudget ha hω).aestronglyMeasurable measurableSet_Ioi)
  rw [ae_restrict_iff' measurableSet_Ioi]
  apply ae_of_all
  intro x hx
  obtain ⟨h0,h1⟩ := stationaryCos_budget_bound ha hβ hω hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1

/-- The common power boundary majorant vanishes at the anchor. -/
theorem tendsto_power_anchor_boundary {a β : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x^(-β)*(x-a)) (𝓝[>] a) (𝓝 0) := by
  have hc := ((Real.hasDerivAt_rpow_const (p := -β) (Or.inl ha.ne')).continuousAt).mul
    (continuousAt_id.sub_const a)
  simpa [Pi.mul_def] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The common power boundary majorant vanishes at infinity. -/
theorem tendsto_power_anchor_boundary_atTop {a β : ℝ} (ha : 0 < a) (hβ : 2 < β) :
    Tendsto (fun x : ℝ => x^(-β)*(x-a)) atTop (𝓝 0) := by
  have hl := tendsto_rpow_neg_atTop (by linarith : 0 < β-1)
  rw [show -(β-1)=1-β by ring] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_gt_atTop a] with x hx
    exact mul_nonneg (Real.rpow_nonneg (ha.trans hx).le _) (sub_pos.mpr hx).le
  · filter_upwards [eventually_gt_atTop a] with x hx
    rw [← endpoint_power_identity (ha.trans hx)]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (ha.trans hx).le _)

/-- The first sine boundary product vanishes at the saddle. -/
theorem tendsto_endpoint_sine_boundary_at_anchor {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    Tendsto (fun x => reciprocalLogWeight β (-ω*a) ω x *
      Real.sin (anchoredLogPhase a (-ω*a) ω x)) (𝓝[>] a) (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_power_anchor_boundary (β := β) ha)
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  simpa only [Real.norm_eq_abs] using endpoint_sine_boundary_bound ha hω hx

/-- The first sine boundary product vanishes at infinity. -/
theorem tendsto_endpoint_sine_boundary_atTop {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    Tendsto (fun x => reciprocalLogWeight β (-ω*a) ω x *
      Real.sin (anchoredLogPhase a (-ω*a) ω x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_power_anchor_boundary_atTop ha hβ)
  filter_upwards [eventually_gt_atTop a] with x hx
  simpa only [Real.norm_eq_abs] using endpoint_sine_boundary_bound ha hω hx

/-- The second compensated boundary product vanishes at the saddle. -/
theorem tendsto_stationaryCosBoundary_at_anchor {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    Tendsto (fun x => stationaryCosWeight a β ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (𝓝[>] a) (𝓝 0) := by
  have hl := (tendsto_power_anchor_boundary (β := β) ha).const_mul ((β+1)/2)
  simp only [mul_zero] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact (stationaryCos_boundary_bound ha hβ hω hx).1
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    simpa only [mul_assoc] using (stationaryCos_boundary_bound ha hβ hω hx).2

/-- The second compensated boundary product vanishes at infinity. -/
theorem tendsto_stationaryCosBoundary_atTop {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    Tendsto (fun x => stationaryCosWeight a β ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) atTop (𝓝 0) := by
  have hl := (tendsto_power_anchor_boundary_atTop ha hβ).const_mul ((β+1)/2)
  simp only [mul_zero] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_gt_atTop a] with x hx
    exact (stationaryCos_boundary_bound ha hβ hω hx).1
  · filter_upwards [eventually_gt_atTop a] with x hx
    simpa only [mul_assoc] using (stationaryCos_boundary_bound ha hβ hω hx).2

/-- First integration by parts retains the exact signed first-dissipation integral. -/
theorem integral_endpoint_logCos_eq_dissipation_sine {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    (∫ x in Ioi a, x^(-β)*Real.cos (anchoredLogPhase a (-ω*a) ω x)) =
      ∫ x in Ioi a, reciprocalLogDissipation β (-ω*a) ω x *
        Real.sin (anchoredLogPhase a (-ω*a) ω x) := by
  have hd (x : ℝ) (hx : x ∈ Ioi a) : ω*x+(-ω*a) ≠ 0 := ne_of_gt (by have hxa : a < x := hx; nlinarith)
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => Real.sin (anchoredLogPhase a (-ω*a) ω x))
        ((ω+(-ω*a)/x)*Real.cos (anchoredLogPhase a (-ω*a) ω x)) x := by
    convert! (hasDerivAt_anchoredLogPhase (ha.trans hx)).sin using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      reciprocalLogWeight β (-ω*a) ω x * ((ω+(-ω*a)/x)*Real.cos (anchoredLogPhase a (-ω*a) ω x)) =
      x^(-β)*Real.cos (anchoredLogPhase a (-ω*a) ω x) := by
    rw [← mul_assoc, reciprocalLogWeight_mul_phase_deriv (ha.trans hx) (hd x hx)]
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_reciprocalLogWeight (ha.trans hx) (hd x hx)) hv
    ((integrable_anchoredLogCos ha (by linarith : 1 < β)).congr_fun
      (fun x hx => (he x hx).symm) measurableSet_Ioi)
    ((integrable_endpoint_dissipation_sine ha hβ hω).neg.congr_fun (fun x _ => by simp) measurableSet_Ioi)
    (tendsto_endpoint_sine_boundary_at_anchor ha hω) (tendsto_endpoint_sine_boundary_atTop ha hβ hω)
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul, integral_neg, sub_self, zero_sub, neg_neg] using hi

/-- Second integration by parts represents the literal cosine integral by a positive density. -/
theorem integral_endpoint_logCos_eq_positive_budget {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    (∫ x in Ioi a, x^(-β)*Real.cos (anchoredLogPhase a (-ω*a) ω x)) =
      ∫ x in Ioi a, stationaryCosDissipation a β ω x *
        (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) := by
  rw [integral_endpoint_logCos_eq_dissipation_sine ha hβ hω]
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => 1-Real.cos (anchoredLogPhase a (-ω*a) ω x))
        ((ω+(-ω*a)/x)*Real.sin (anchoredLogPhase a (-ω*a) ω x)) x := by
    convert! ((hasDerivAt_anchoredLogPhase (ha.trans hx)).cos).const_sub 1 using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      stationaryCosWeight a β ω x * ((ω+(-ω*a)/x)*Real.sin (anchoredLogPhase a (-ω*a) ω x)) =
      reciprocalLogDissipation β (-ω*a) ω x*Real.sin (anchoredLogPhase a (-ω*a) ω x) := by
    rw [← mul_assoc, stationaryCosWeight_mul_phase_deriv (ha.trans hx) hω.ne' (sub_ne_zero.mpr (ne_of_gt hx))]
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_stationaryCosWeight (ha.trans hx) hω.ne' (sub_ne_zero.mpr (ne_of_gt hx))) hv
    ((integrable_endpoint_dissipation_sine ha hβ hω).congr_fun
      (fun x hx => (he x hx).symm) measurableSet_Ioi)
    ((integrable_stationaryCosBudget ha hβ hω).neg.congr_fun (fun x _ => by simp) measurableSet_Ioi)
    (tendsto_stationaryCosBoundary_at_anchor ha hβ hω) (tendsto_stationaryCosBoundary_atTop ha hβ hω)
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul, integral_neg, sub_self, zero_sub, neg_neg] using hi

/-- The actual saddle-anchored cosine integral is strictly positive. -/
theorem integral_endpoint_logCos_pos {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    0 < ∫ x in Ioi a, x^(-β)*Real.cos (anchoredLogPhase a (-ω*a) ω x) := by
  rw [integral_endpoint_logCos_eq_positive_budget ha hβ hω]
  have hn : ∀ᵐ x ∂volume.restrict (Ioi a), 0 ≤ stationaryCosDissipation a β ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun x hx => (stationaryCos_budget_bound ha hβ hω hx).1)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (integrable_stationaryCosBudget ha hβ hω)]
  have ho := (continuousOn_stationaryCosBudget (β := β) ha hω).isOpen_inter_preimage isOpen_Ioi
    (isClosed_singleton (x := (0:ℝ))).isOpen_compl
  rw [Set.inter_comm] at ho
  apply ho.measure_pos volume
  obtain ⟨x,hx,hsx⟩ := exists_endpoint_sine_ne_zero ha hω
  have hc : Real.cos (anchoredLogPhase a (-ω*a) ω x) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro he
    have hs := Real.sin_sq_add_cos_sq (anchoredLogPhase a (-ω*a) ω x)
    rw [he] at hs
    have hz : Real.sin (anchoredLogPhase a (-ω*a) ω x) = 0 := by
      nlinarith [sq_nonneg (Real.sin (anchoredLogPhase a (-ω*a) ω x))]
    exact hsx hz
  exact ⟨x,(mul_pos (stationaryCosDissipation_pos ha hβ hω hx) (sub_pos.mpr hc)).ne',hx⟩

/-- The anchored saddle phase has a global minimum at its positive anchor. -/
theorem endpoint_phase_nonneg_of_pos {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : 0 < x) :
    0 ≤ anchoredLogPhase a (-ω*a) ω x := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl (mul_pos hω ha).le
  have he : ω*a*(x/a-1)=ω*(x-a) := by field_simp
  rw [he] at hm
  unfold anchoredLogPhase
  nlinarith

/-- Exact phase transport from the initial anchor to the interior saddle. -/
theorem stationary_phase_split (a b ω x : ℝ) :
    anchoredLogPhase a (ω*b) (-ω) x =
      anchoredLogPhase a (ω*b) (-ω) b-anchoredLogPhase b (-ω*b) ω x := by
  unfold anchoredLogPhase
  ring

/-- Before the saddle the original negative-frequency phase lies between zero and its maximum. -/
theorem stationary_negative_phase_bounds {a b ω x : ℝ} (ha : 0 < a) (hω : 0 < ω)
    (hab : a ≤ b) (hx : x ∈ Icc a b) :
    0 ≤ anchoredLogPhase a (ω*b) (-ω) x ∧
      anchoredLogPhase a (ω*b) (-ω) x ≤ anchoredLogPhase a (ω*b) (-ω) b := by
  have hx0 := ha.trans_le hx.1
  have hb0 := ha.trans_le hab
  constructor
  · have hl := Real.log_le_sub_one_of_pos (div_pos ha hx0)
    rw [Real.log_div ha.ne' hx0.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl (mul_pos hω hb0).le
    have h0 : 0 ≤ ω*(x-a)*(b-x)/x := by
      exact div_nonneg (mul_nonneg (mul_nonneg hω.le (sub_nonneg.mpr hx.1)) (sub_nonneg.mpr hx.2)) hx0.le
    have he : ω*(x-a)*(b-x)/x = -ω*(x-a)-ω*b*(a/x-1) := by field_simp; ring
    rw [he] at h0
    unfold anchoredLogPhase
    nlinarith
  · rw [stationary_phase_split]
    exact sub_le_self _ (endpoint_phase_nonneg_of_pos hb0 hω hx0)

/-- The original tail retains both quadrature components and the full saddle phase. -/
theorem integral_stationary_tail_rotation (a : ℝ) {b β : ℝ} (hb : 0 < b) (hβ : 1 < β) (ω : ℝ) :
    (∫ x in Ioi b, x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x)) =
      Real.sin (anchoredLogPhase a (ω*b) (-ω) b) *
        (∫ x in Ioi b, x^(-β)*Real.cos (anchoredLogPhase b (-ω*b) ω x)) -
      Real.cos (anchoredLogPhase a (ω*b) (-ω) b) *
        (∫ x in Ioi b, x^(-β)*Real.sin (anchoredLogPhase b (-ω*b) ω x)) := by
  have he (x : ℝ) : x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x) =
      Real.sin (anchoredLogPhase a (ω*b) (-ω) b)*(x^(-β)*Real.cos (anchoredLogPhase b (-ω*b) ω x)) -
      Real.cos (anchoredLogPhase a (ω*b) (-ω) b)*(x^(-β)*Real.sin (anchoredLogPhase b (-ω*b) ω x)) := by
    rw [stationary_phase_split,Real.sin_sub]
    ring
  simp_rw [he]
  rw [integral_sub ((integrable_anchoredLogCos hb hβ).const_mul _)
    ((integrable_anchoredLogSine hb hβ).const_mul _), integral_const_mul,integral_const_mul]

/-- The complete signed source is its finite head plus the rotated saddle tail. -/
theorem integral_stationary_logSine_split {a b β ω : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ : 1 < β) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x)) =
      (∫ x in Ioc a b, x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x)) +
      Real.sin (anchoredLogPhase a (ω*b) (-ω) b) *
        (∫ x in Ioi b, x^(-β)*Real.cos (anchoredLogPhase b (-ω*b) ω x)) -
      Real.cos (anchoredLogPhase a (ω*b) (-ω) b) *
        (∫ x in Ioi b, x^(-β)*Real.sin (anchoredLogPhase b (-ω*b) ω x)) := by
  have hi := integrable_anchoredLogSine (γ := ω*b) (ω := -ω) ha hβ
  have ht := hi.mono_set (show Ioi b ⊆ Ioi a from fun x hx => hab.trans_lt hx)
  rw [← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) ht]
  rw [integral_stationary_tail_rotation a (ha.trans_le hab) hβ ω]
  ring

/-- A positive pair has a strictly positive sine projection throughout the second phase quadrant. -/
theorem rotated_positive_quadrant_pos {θ C S : ℝ} (hC : 0 < C) (hS : 0 < S)
    (hlo : Real.pi/2 ≤ θ) (hhi : θ ≤ Real.pi) :
    0 < Real.sin θ*C-Real.cos θ*S := by
  have hc : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hlo (by linarith [Real.pi_pos])
  rcases lt_or_eq_of_le hhi with hl | he
  · have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hl
    have hp := mul_pos hs hC
    have hn := mul_nonpos_of_nonpos_of_nonneg hc hS.le
    linarith
  · rw [he,Real.sin_pi,Real.cos_pi]
    linarith

/-- A saddle phase between pi/2 and pi makes the full actual signed integral strictly positive. -/
theorem integral_stationary_logSine_pos_phase_band {a b β ω : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hβ : 2 < β) (hω : 0 < ω)
    (hlo : Real.pi/2 ≤ anchoredLogPhase a (ω*b) (-ω) b)
    (hhi : anchoredLogPhase a (ω*b) (-ω) b ≤ Real.pi) :
    0 < ∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x) := by
  rw [integral_stationary_logSine_split ha hab (by linarith)]
  have hhead : 0 ≤ ∫ x in Ioc a b, x^(-β)*Real.sin (anchoredLogPhase a (ω*b) (-ω) x) := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro x hx
    have hphase := stationary_negative_phase_bounds ha hω hab ⟨hx.1.le,hx.2⟩
    exact mul_nonneg (Real.rpow_nonneg (ha.trans hx.1).le _)
      (Real.sin_nonneg_of_nonneg_of_le_pi hphase.1 (hphase.2.trans hhi))
  have htail := rotated_positive_quadrant_pos (integral_endpoint_logCos_pos (ha.trans_le hab) hβ hω)
    (integral_endpoint_logSine_pos (ha.trans_le hab) hβ hω) hlo hhi
  linarith

/-- The literal negative-frequency Bernoulli atom is positive in the proved interior phase band, without a zero premise. -/
theorem scaledBernoulliFourierAtom_neg_im_pos_of_phase_band {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k) (hinner : 2*Real.pi*k*N < s.im)
    (hlo : Real.pi/2 ≤ anchoredLogPhase N s.im (-(2*Real.pi*k)) (s.im/(2*Real.pi*k)))
    (hhi : anchoredLogPhase N s.im (-(2*Real.pi*k)) (s.im/(2*Real.pi*k)) ≤ Real.pi) :
    0 < (scaledBernoulliFourierAtom s N (-k)).im := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hω : 0 < 2*Real.pi*(k:ℝ) := by positivity
  have hb : (N:ℝ) ≤ s.im/(2*Real.pi*k) := (le_div_iff₀ hω).mpr (by nlinarith)
  have he : (2*Real.pi*k)*(s.im/(2*Real.pi*k)) = s.im := by field_simp
  rw [scaledBernoulliFourierAtom_im_eq hs hN]
  apply mul_pos (mul_pos (Real.rpow_pos_of_pos hNp _)
    (bernoulliModeWeight_pos (neg_ne_zero.mpr hk.ne')))
  simp only [Int.cast_neg,mul_neg]
  have hl' : Real.pi/2 ≤ anchoredLogPhase (N:ℝ) ((2*Real.pi*k)*(s.im/(2*Real.pi*k)))
      (-(2*Real.pi*k)) (s.im/(2*Real.pi*k)) := by simpa only [he] using hlo
  have hh' : anchoredLogPhase (N:ℝ) ((2*Real.pi*k)*(s.im/(2*Real.pi*k)))
      (-(2*Real.pi*k)) (s.im/(2*Real.pi*k)) ≤ Real.pi := by simpa only [he] using hhi
  simpa only [he] using integral_stationary_logSine_pos_phase_band hNp hb (by linarith : 2 < s.re+2) hω hl' hh'


/-- The actual outgoing complex tail has positive real part and negative imaginary part. -/
theorem integral_stationary_complex_tail_quadrant {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    0 < (∫ x in Ioi a, (x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).re ∧
    (∫ x in Ioi a, (x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).im < 0 := by
  have hi : IntegrableOn (fun x => (x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)) (Ioi a) := by
    apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha).ofReal).mul_bdd (c := 1)
      ((Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_anchoredLogPhase ha).neg).mul continuousOn_const)).aestronglyMeasurable measurableSet_Ioi)
    exact ae_of_all _ (fun x => by simp [Complex.norm_exp])
  constructor
  · have hr : (∫ x in Ioi a, ((x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).re) = (∫ x in Ioi a, (x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).re := integral_re hi
    rw [← hr]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.exp_ofReal_mul_I_re,Real.cos_neg]
    exact integral_endpoint_logCos_pos ha hβ hω
  · have hm : (∫ x in Ioi a, ((x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).im) = (∫ x in Ioi a, (x^(-β):ℝ)*Complex.exp (((-anchoredLogPhase a (-ω*a) ω x:ℝ):ℂ)*I)).im := integral_im hi
    rw [← hm]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      Complex.exp_ofReal_mul_I_im,Real.sin_neg,mul_neg,integral_neg]
    exact neg_neg_of_pos (integral_endpoint_logSine_pos ha hβ hω)

end RHTower.DeletionMixedRefinement
