import GaloisForLFunctions.RHTower.SteinhausCumulantTaylor

/-!
# The derivative of the regular-variation cumulant

The card's `(16)`.  The one-circle cumulant is `1`-Lipschitz because its derivative is the mean of
a variable bounded by one under the exponentially tilted law.  Differentiating `Λ_α` under the
integral is then dominated by the profile itself, which is integrable:

`Λ'_α(λ) = ∫₀¹ w_α(v) m(λ w_α(v)) dv`,  `m = (log I₀)'`,  `|m| ≤ 1`.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

local instance phaseCirclePositiveDeriv : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- **The one-circle cumulant is `1`-Lipschitz.** -/
theorem abs_deriv_steinhausLogLaplace_le_one (v : ℝ) :
    |deriv steinhausLogLaplace v| ≤ 1 := by
  have hmem := mem_interior_integrableExpSet v
  have hderiv : deriv steinhausLogLaplace v
      = (∫ x : PhaseCircle, steinhausProjection x *
            Real.exp (v * steinhausProjection x) ∂AddCircle.haarAddCircle)
        / ProbabilityTheory.mgf steinhausProjection AddCircle.haarAddCircle v := by
    have hfun : steinhausLogLaplace
        = ProbabilityTheory.cgf steinhausProjection AddCircle.haarAddCircle := by
      funext r
      exact steinhausLogLaplace_eq_cgf r
    rw [hfun]
    exact ProbabilityTheory.deriv_cgf hmem
  have hmgf : ProbabilityTheory.mgf steinhausProjection AddCircle.haarAddCircle v
      = steinhausLaplace v := (steinhausLaplace_eq_mgf v).symm
  have hpos : 0 < steinhausLaplace v := steinhausLaplace_pos v
  have hint : Integrable (fun x : PhaseCircle => Real.exp (v * steinhausProjection x))
      AddCircle.haarAddCircle := steinhausLaplace_integrable v
  have hnum : |∫ x : PhaseCircle, steinhausProjection x *
        Real.exp (v * steinhausProjection x) ∂AddCircle.haarAddCircle| ≤ steinhausLaplace v := by
    have hb : ∀ x : PhaseCircle,
        ‖steinhausProjection x * Real.exp (v * steinhausProjection x)‖
          ≤ Real.exp (v * steinhausProjection x) := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := abs_steinhausProjection_le_one x
      nlinarith only [this, (Real.exp_pos (v * steinhausProjection x)).le]
    have hmono := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)
    rw [Real.norm_eq_abs] at hmono
    rw [steinhausLaplace]
    exact hmono
  rw [hderiv, hmgf, abs_div, abs_of_pos hpos, div_le_one hpos]
  exact hnum

/-- The derivative of the regular-variation cumulant. -/
def rvCumulantDeriv (α lam : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, weightProfile α v * deriv steinhausLogLaplace (lam * weightProfile α v)

theorem continuous_deriv_steinhausLogLaplace : Continuous (deriv steinhausLogLaplace) :=
  continuousOn_univ.mp analyticOnNhd_deriv_steinhausLogLaplace.continuousOn

theorem measurable_weightProfile (α : ℝ) : Measurable (weightProfile α) := by
  have hfun : (weightProfile α) = fun v : ℝ => (1 - α) * v ^ (-α) := rfl
  rw [hfun]
  exact measurable_const.mul (measurable_id.pow_const (-α))

/-- **Differentiation under the integral**, the card's `(16)`. -/
theorem hasDerivAt_rvCumulant {α : ℝ} (hα : α < 1) (lam : ℝ) :
    HasDerivAt (rvCumulant α) (rvCumulantDeriv α lam) lam := by
  have hmeasw := measurable_weightProfile α
  have hF : ∀ x : ℝ, AEStronglyMeasurable
      (fun v : ℝ => steinhausLogLaplace (x * weightProfile α v))
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    intro x
    exact ((continuous_steinhausLogLaplace.measurable.comp
      (measurable_const.mul hmeasw)).aestronglyMeasurable).restrict
  have hF' : AEStronglyMeasurable
      (fun v : ℝ => weightProfile α v * deriv steinhausLogLaplace (lam * weightProfile α v))
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    exact ((hmeasw.mul (continuous_deriv_steinhausLogLaplace.measurable.comp
      (measurable_const.mul hmeasw))).aestronglyMeasurable).restrict
  have hbound : ∀ᵐ t : ℝ, t ∈ uIoc (0 : ℝ) 1 → ∀ x ∈ (univ : Set ℝ),
      ‖weightProfile α t * deriv steinhausLogLaplace (x * weightProfile α t)‖
        ≤ weightProfile α t := by
    filter_upwards with t ht x _
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hw : 0 ≤ weightProfile α t := weightProfile_nonneg hα ht.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have hd := abs_deriv_steinhausLogLaplace_le_one (x * weightProfile α t)
    nlinarith only [hd, hw]
  have hdiff : ∀ᵐ t : ℝ, t ∈ uIoc (0 : ℝ) 1 → ∀ x ∈ (univ : Set ℝ),
      HasDerivAt (fun y : ℝ => steinhausLogLaplace (y * weightProfile α t))
        (weightProfile α t * deriv steinhausLogLaplace (x * weightProfile α t)) x := by
    filter_upwards with t _ x _
    have hg : HasDerivAt steinhausLogLaplace
        (deriv steinhausLogLaplace (x * weightProfile α t)) (x * weightProfile α t) :=
      (differentiable_steinhausLogLaplace _).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * weightProfile α t) (weightProfile α t) x := by
      simpa using (hasDerivAt_id x).mul_const (weightProfile α t)
    have hcomp := hg.comp x hlin
    rw [mul_comm] at hcomp
    exact hcomp
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℝ) (v : ℝ) => steinhausLogLaplace (x * weightProfile α v))
    (F' := fun (x : ℝ) (v : ℝ) =>
      weightProfile α v * deriv steinhausLogLaplace (x * weightProfile α v))
    (bound := weightProfile α) (x₀ := lam) (s := univ) univ_mem
    (Filter.Eventually.of_forall hF) (intervalIntegrable_rvCumulant_integrand hα lam) hF'
    hbound (intervalIntegrable_weightProfile hα) hdiff
  exact hmain.2


theorem deriv_rvCumulant {α : ℝ} (hα : α < 1) (lam : ℝ) :
    deriv (rvCumulant α) lam = rvCumulantDeriv α lam :=
  (hasDerivAt_rvCumulant hα lam).deriv

theorem differentiable_rvCumulant {α : ℝ} (hα : α < 1) : Differentiable ℝ (rvCumulant α) :=
  fun lam => (hasDerivAt_rvCumulant hα lam).differentiableAt

@[simp] theorem rvCumulantDeriv_zero (α : ℝ) : rvCumulantDeriv α 0 = 0 := by
  rw [rvCumulantDeriv]
  have h : ∀ v : ℝ, weightProfile α v * deriv steinhausLogLaplace (0 * weightProfile α v) = 0 := by
    intro v
    rw [zero_mul, deriv_steinhausLogLaplace_zero, mul_zero]
  simp only [h]
  simp

/-- **The derivative is continuous.** -/
theorem continuous_rvCumulantDeriv {α : ℝ} (hα : α < 1) : Continuous (rvCumulantDeriv α) := by
  rw [Metric.continuous_iff']
  intro lam ε hε
  have hmeasw := measurable_weightProfile α
  have hdom : IntervalIntegrable (weightProfile α) volume 0 1 :=
    intervalIntegrable_weightProfile hα
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun v : ℝ => weightProfile α v * deriv steinhausLogLaplace (x * weightProfile α v))
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    intro x
    exact ((hmeasw.mul (continuous_deriv_steinhausLogLaplace.measurable.comp
      (measurable_const.mul hmeasw))).aestronglyMeasurable).restrict
  have hbound : ∀ x : ℝ, ∀ᵐ v ∂(volume.restrict (uIoc (0 : ℝ) 1)),
      ‖weightProfile α v * deriv steinhausLogLaplace (x * weightProfile α v)‖
        ≤ weightProfile α v := by
    intro x
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have hd := abs_deriv_steinhausLogLaplace_le_one (x * weightProfile α v)
    nlinarith only [hd, hw]
  have hptw : ∀ᵐ v ∂(volume.restrict (uIoc (0 : ℝ) 1)),
      Tendsto (fun x : ℝ =>
        weightProfile α v * deriv steinhausLogLaplace (x * weightProfile α v)) (𝓝 lam)
        (𝓝 (weightProfile α v * deriv steinhausLogLaplace (lam * weightProfile α v))) := by
    filter_upwards with v
    exact tendsto_const_nhds.mul (continuous_deriv_steinhausLogLaplace.tendsto _ |>.comp
      ((continuous_id.mul continuous_const).tendsto lam))
  have hdomint : IntegrableOn (weightProfile α) (uIoc (0 : ℝ) 1) volume := by
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have := hdom
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
    exact this
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (uIoc (0:ℝ) 1))
    (weightProfile α) (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound) hdomint hptw
  have hconv : Tendsto (fun x : ℝ => rvCumulantDeriv α x) (𝓝 lam)
      (𝓝 (rvCumulantDeriv α lam)) := by
    have hid : ∀ x : ℝ, rvCumulantDeriv α x
        = ∫ v in uIoc (0 : ℝ) 1,
            weightProfile α v * deriv steinhausLogLaplace (x * weightProfile α v) := by
      intro x
      rw [rvCumulantDeriv, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp only [hid]
    exact hdct
  have := hconv.eventually (Metric.ball_mem_nhds (rvCumulantDeriv α lam) hε)
  filter_upwards [this] with x hx
  exact hx


/-- **The regular-variation cumulant is strictly convex.** -/
theorem strictConvexOn_rvCumulant {α : ℝ} (hα : α < 1) :
    StrictConvexOn ℝ univ (rvCumulant α) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hpt : ∀ v ∈ Ioo (0 : ℝ) 1,
      0 < (a * steinhausLogLaplace (x * weightProfile α v)
            + b * steinhausLogLaplace (y * weightProfile α v))
          - steinhausLogLaplace ((a * x + b * y) * weightProfile α v) := by
    intro v hv
    have hw : 0 < weightProfile α v := weightProfile_pos hα hv.1
    have hne : x * weightProfile α v ≠ y * weightProfile α v := by
      intro h
      exact hxy (by
        have := mul_right_cancel₀ hw.ne' h
        exact this)
    have hstrict := strictConvexOn_steinhausLogLaplace.2 (mem_univ (x * weightProfile α v))
      (mem_univ (y * weightProfile α v)) hne ha hb hab
    simp only [smul_eq_mul] at hstrict
    have hid : a * (x * weightProfile α v) + b * (y * weightProfile α v)
        = (a * x + b * y) * weightProfile α v := by ring
    rw [hid] at hstrict
    linarith
  have hint1 := intervalIntegrable_rvCumulant_integrand hα x
  have hint2 := intervalIntegrable_rvCumulant_integrand hα y
  have hint3 := intervalIntegrable_rvCumulant_integrand hα (a * x + b * y)
  have hintD : IntervalIntegrable
      (fun v : ℝ => (a * steinhausLogLaplace (x * weightProfile α v)
        + b * steinhausLogLaplace (y * weightProfile α v))
        - steinhausLogLaplace ((a * x + b * y) * weightProfile α v)) volume 0 1 :=
    ((hint1.const_mul a).add (hint2.const_mul b)).sub hint3
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hintD hpt (by norm_num)
  rw [intervalIntegral.integral_sub (((hint1.const_mul a).add (hint2.const_mul b))) hint3,
    intervalIntegral.integral_add (hint1.const_mul a) (hint2.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hpos
  simp only [smul_eq_mul]
  rw [rvCumulant, rvCumulant, rvCumulant]
  linarith

theorem strictMono_rvCumulantDeriv {α : ℝ} (hα : α < 1) : StrictMono (rvCumulantDeriv α) := by
  have hmono := (strictConvexOn_rvCumulant hα).strictMonoOn_deriv
    (fun x _ => (differentiable_rvCumulant hα) x)
  intro x y hxy
  have h := hmono (mem_univ x) (mem_univ y) hxy
  rw [deriv_rvCumulant hα, deriv_rvCumulant hα] at h
  exact h

/-- The chord from the origin is below the derivative. -/
theorem rvCumulant_div_le_rvCumulantDeriv {α : ℝ} (hα : α < 1) {lam : ℝ} (hlam : 0 < lam) :
    rvCumulant α lam / lam ≤ rvCumulantDeriv α lam := by
  have hslope := (strictConvexOn_rvCumulant hα).convexOn.slope_le_deriv (mem_univ (0 : ℝ))
    (mem_univ lam) hlam ((differentiable_rvCumulant hα) lam)
  rw [deriv_rvCumulant hα] at hslope
  rw [slope_def_field, rvCumulant_zero, sub_zero, sub_zero] at hslope
  exact hslope

/-- **The derivative attains every value in `(0,1)`.**  This is the card's `(16)`. -/
theorem exists_rvCumulantDeriv_eq {α : ℝ} (hα : α < 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ lam : ℝ, 0 < lam ∧ rvCumulantDeriv α lam = q := by
  obtain ⟨c, hqc, hc1⟩ := exists_between hq1
  have hc0 : 0 < c := lt_trans hq0 hqc
  set K : ℝ := Real.log (arcMass c) with hK
  obtain ⟨lam₁, hlam₁⟩ : ∃ lam₁ : ℝ, 0 < lam₁ ∧ q * lam₁ < c * lam₁ + K := by
    have hgap : 0 < c - q := by linarith
    obtain ⟨M, hM⟩ := exists_nat_gt ((-K) / (c - q))
    refine ⟨max ((M : ℝ) + 1) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    have hM1 : (-K) / (c - q) < (M : ℝ) + 1 := by linarith [hM]
    rw [div_lt_iff₀ hgap] at hM1
    have hle : (M : ℝ) + 1 ≤ max ((M : ℝ) + 1) 1 := le_max_left _ _
    nlinarith [hM1, hle, hgap]
  obtain ⟨hlam₁0, hlam₁1⟩ := hlam₁
  have hbig : q < rvCumulantDeriv α lam₁ := by
    have hlow := le_rvCumulant hα hc1 hlam₁0.le
    have hdiv : q < rvCumulant α lam₁ / lam₁ := by
      rw [lt_div_iff₀ hlam₁0]
      rw [hK] at hlam₁1
      linarith [hlow]
    exact lt_of_lt_of_le hdiv (rvCumulant_div_le_rvCumulantDeriv hα hlam₁0)
  have hcont : ContinuousOn (rvCumulantDeriv α) (Icc 0 lam₁) :=
    (continuous_rvCumulantDeriv hα).continuousOn
  have hmem : q ∈ Icc (rvCumulantDeriv α 0) (rvCumulantDeriv α lam₁) := by
    rw [rvCumulantDeriv_zero]
    exact ⟨hq0.le, hbig.le⟩
  obtain ⟨lam, hlam, hval⟩ := intermediate_value_Icc hlam₁0.le hcont hmem
  refine ⟨lam, ?_, hval⟩
  rcases eq_or_lt_of_le hlam.1 with h0 | hpos
  · exfalso
    rw [← h0, rvCumulantDeriv_zero] at hval
    linarith
  · exact hpos

end

end HTGeometry
