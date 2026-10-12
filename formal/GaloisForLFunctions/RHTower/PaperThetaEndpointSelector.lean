import GaloisForLFunctions.RHTower.PaperThetaEndpointDensity

/-! # Exact logarithmic admission selects the Xi divisor

For the original two-ended theta mode, the L log L cost is finite exactly where
the native weighted L² cost is finite. Ordinary L¹ admission holds on the whole strip.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

namespace PaperThetaEndpoint

theorem density_le_energy (z : ℂ) (x : ℝ) :
    density z x ≤ ‖flatMode z x‖ + flatModeWeightedDensity z x := by
  have hρ := thetaSource.normalized_pos x
  have hlog := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 2 + ‖flatMode z x‖ / thetaSource.normalized x)
  have h := mul_le_mul_of_nonneg_left hlog (norm_nonneg (flatMode z x))
  exact h.trans_eq (by dsimp [flatModeWeightedDensity]; ring)

theorem integrable_density_of_zero (z : Point) (hXi : XiC z = 0) :
    Integrable (density z) := by
  refine ((integrable_flatMode z.property.1 z.property.2).norm.add
    (integrable_flatModeWeightedDensity_of_zero hXi)).mono'
      (continuous_density z).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg z x)]
  exact density_le_energy z x

/-- The nonzero connection forces positive logarithmic mass on an infinite half-line. -/
theorem exists_eventually_density_lower (z : Point) (hXi : XiC z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atBot, c ≤ density z x := by
  obtain ⟨c, hc, hu⟩ := exists_eventually_norm_lower z hXi
  refine ⟨c, hc, ?_⟩
  filter_upwards [hu, eventually_log_normalized_le,
    eventually_le_atBot (-(max 2 |Real.log c|))] with x hx hρ hxB
  have hx2 : 2 ≤ -x := by have := le_max_left (2 : ℝ) |Real.log c|; linarith
  have hxc : |Real.log c| ≤ -x := by have := le_max_right (2 : ℝ) |Real.log c|; linarith
  have hx0 : x ≤ 0 := by linarith
  have ha : x ≤ z.val.im * x := by
    simpa using mul_le_mul_of_nonpos_right z.property.2.le hx0
  have hu0 : 0 < ‖flatMode z x‖ := (mul_pos hc (Real.exp_pos _)).trans_le hx
  have hlogu := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hx
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hlogu
  have hlogratio := Real.log_le_log (div_pos hu0 (thetaSource.normalized_pos x))
    (show ‖flatMode z x‖ / thetaSource.normalized x ≤
      2 + ‖flatMode z x‖ / thetaSource.normalized x by linarith)
  rw [Real.log_div hu0.ne' (thetaSource.normalized_pos x).ne'] at hlogratio
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ -x by linarith)
  have hlog : Real.exp (-x) ≤
      Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) := by
    nlinarith [neg_abs_le (Real.log c),
      mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -x - 2 by linarith)]
  have hexp : 1 ≤ Real.exp ((z.val.im - 1) * x) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [z.property.2]) hx0
  calc
    c ≤ c * Real.exp ((z.val.im - 1) * x) := le_mul_of_one_le_right hc.le hexp
    _ = (c * Real.exp (z.val.im * x)) * Real.exp (-x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ‖flatMode z x‖ * Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x) :=
      mul_le_mul hx hlog (Real.exp_pos _).le (norm_nonneg _)
    _ = density z x := rfl

theorem not_integrable_density (z : Point) (hXi : XiC z ≠ 0) :
    ¬ Integrable (density z) := by
  intro hint
  obtain ⟨c, hc, h⟩ := exists_eventually_density_lower z hXi
  obtain ⟨X, hX⟩ := eventually_atBot.1 h
  have hon : IntegrableOn (fun _ : ℝ => c) (Iic X) := by
    refine (hint.integrableOn (s := Iic X)).mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hX x hx
  rw [integrableOn_const_iff] at hon
  rcases hon with h0 | hfin
  · exact hc.ne' (by simpa only [enorm_eq_zero] using h0)
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The exact L log L admission criterion, with no arithmetic sign assumption. -/
theorem integrable_density_iff (z : Point) :
    Integrable (density z) ↔ XiC z = 0 := by
  constructor
  · intro h
    by_contra hXi
    exact not_integrable_density z hXi h
  · exact integrable_density_of_zero z

theorem measurable_pullback (z : Point) : Measurable (flatModePullback z) :=
  ((continuous_flatMode (abs_im_lt_one_of_flat z.property.1 z.property.2)).measurable.comp
    thetaSource.measurable_quantileFun).div (measurable_metricSymbol thetaSource)

/-- All the original modes are integrable, even away from the Xi divisor. -/
theorem integrable_pullback (z : Point) : Integrable (flatModePullback z) unitIntervalMeasure := by
  rw [integrable_unitInterval_iff_cdf (measurable_pullback z).aestronglyMeasurable]
  refine (integrable_flatMode z.property.1 z.property.2).congr (Eventually.of_forall fun x => ?_)
  simp only [flatModePullback]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  rw [Complex.real_smul]
  field_simp

/-- The logarithmic cost in the literal quantile coordinate. -/
theorem integrable_pullback_log_iff (z : Point) :
    Integrable (fun t => ‖flatModePullback z t‖ * Real.log (2 + ‖flatModePullback z t‖))
      unitIntervalMeasure ↔ XiC z = 0 := by
  have hn := (measurable_pullback z).norm
  have hm : AEStronglyMeasurable
      (fun t => ‖flatModePullback z t‖ * Real.log (2 + ‖flatModePullback z t‖))
      unitIntervalMeasure :=
    (hn.mul ((measurable_const.add hn).log)).aestronglyMeasurable
  rw [integrable_unitInterval_iff_cdf hm,
    ← integrable_density_iff z]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [flatModePullback, smul_eq_mul, density]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
  field_simp [(thetaSource.normalized_pos x).ne']

end PaperThetaEndpoint
end RHTower
