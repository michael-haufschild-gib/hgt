import GaloisForLFunctions.RHTower.PaperThetaCutCurrent

/-! # The native differential equation behind the compact theta current

The L1 density is the full combined source expression. Its singular terms
are kept together throughout transport; no separate integrability of those
terms is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped SchwartzMap

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

def sourceLogDerivative (x : ℝ) : ℂ :=
  deriv (fun y : ℝ => (thetaSource.normalized y : ℂ)) x /
    (thetaSource.normalized x : ℂ)

private theorem normalizedComplex_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (thetaSource.normalized y : ℂ))
      (deriv (fun y : ℝ => (thetaSource.normalized y : ℂ)) x) x :=
  ((differentiable_normalized_theta x).hasDerivAt.ofReal_comp).differentiableAt.hasDerivAt

theorem flatQuotient_source_equation (z : ℂ) (x : ℝ) :
    deriv (flatQuotient z) x + I*z*flatQuotient z x +
      sourceLogDerivative x*(flatQuotient z x+1) = 0 := by
  have hρ := normalizedComplex_hasDerivAt x
  have hρ0 : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  have hF := ((hasDerivAt_flatPrimitiveMode_all z x).const_mul (-(I*z))).sub hρ
  change HasDerivAt (flatMode z) _ x at hF
  have hq := hF.div hρ hρ0
  change HasDerivAt (flatQuotient z) _ x at hq
  rw [hq.deriv, sourceLogDerivative, flatQuotient]
  field_simp
  ring

theorem sourceLogDerivative_neg (x : ℝ) :
    sourceLogDerivative (-x) = -sourceLogDerivative x := by
  let r : ℝ → ℂ := fun y => thetaSource.normalized y
  have he : (fun y : ℝ => r (-y)) = r := by
    funext y
    exact congrArg Complex.ofReal (normalized_reflection y)
  have hc := (normalizedComplex_hasDerivAt (-x)).scomp x (hasDerivAt_neg x)
  simp only [neg_smul, one_smul] at hc
  change HasDerivAt (fun y : ℝ => r (-y)) (-deriv r (-x)) x at hc
  rw [he] at hc
  have hd : deriv r (-x) = -deriv r x := by
    simpa only [neg_neg] using (congrArg (fun z : ℂ => -z) hc.deriv).symm
  change deriv r (-x)/(thetaSource.normalized (-x) : ℂ) =
    -(deriv r x/(thetaSource.normalized x : ℂ))
  rw [hd, normalized_reflection, neg_div]

theorem leftQuotient_source_equation (z : ℂ) (x : ℝ) :
    deriv (leftQuotient z) x + I*z*leftQuotient z x +
      sourceLogDerivative x*(leftQuotient z x+1) = 0 := by
  have hc := (differentiable_flatQuotient (-z) (-x)).hasDerivAt.scomp x (hasDerivAt_neg x)
  simp only [neg_smul, one_smul] at hc
  change HasDerivAt (leftQuotient z) _ x at hc
  rw [hc.deriv, leftQuotient]
  have h := flatQuotient_source_equation (-z) (-x)
  rw [sourceLogDerivative_neg] at h
  linear_combination -h

theorem cutQuotient_eventuallyEq_left (z : ℂ) {a x : ℝ} (hx : x < a) :
    cutQuotient z a =ᶠ[𝓝 x] leftQuotient z := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact cutQuotient_left z hy

theorem cutQuotient_eventuallyEq_right (z : ℂ) {a x : ℝ} (hx : a < x) :
    cutQuotient z a =ᶠ[𝓝 x] flatQuotient z := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact cutQuotient_right z hy.le

theorem differentiableAt_cutQuotient (z : ℂ) {a x : ℝ} (hx : x ≠ a) :
    DifferentiableAt ℝ (cutQuotient z a) x := by
  rcases hx.lt_or_gt with hx | hx
  · have hd : DifferentiableAt ℝ (leftQuotient z) x :=
      (differentiable_flatQuotient (-z) (-x)).comp x (by fun_prop)
    exact hd.congr_of_eventuallyEq (cutQuotient_eventuallyEq_left z hx)
  · exact (differentiable_flatQuotient z x).congr_of_eventuallyEq
      (cutQuotient_eventuallyEq_right z hx)

theorem cutQuotient_source_equation (z : ℂ) {a x : ℝ} (hx : x ≠ a) :
    deriv (cutQuotient z a) x + I*z*cutQuotient z a x +
      sourceLogDerivative x*(cutQuotient z a x+1) = 0 := by
  rcases hx.lt_or_gt with hx | hx
  · rw [(cutQuotient_eventuallyEq_left z hx).deriv_eq, cutQuotient_left z hx]
    exact leftQuotient_source_equation z x
  · rw [(cutQuotient_eventuallyEq_right z hx).deriv_eq, cutQuotient_right z hx.le]
    exact flatQuotient_source_equation z x

/-- The signed source terms are combined before integration at the singular compact endpoints. -/
def cutSourceDensity (z : ℂ) (c : Ioo (0 : ℝ) 1) (t : ℝ) : ℂ :=
  (quantileSpeed thetaSource t : ℂ) *
    (-(I*z*cutQuantileMode z c t) -
      sourceLogDerivative (thetaSource.quantileFun t)*(cutQuantileMode z c t+1))

theorem deriv_cutQuantileMode_eq_sourceDensity (z : ℂ) (c t : Ioo (0 : ℝ) 1)
    (ht : t.val ≠ c.val) :
    deriv (cutQuantileMode z c) t.val = cutSourceDensity z c t.val := by
  let a := thetaSource.quantileFun c.val
  let x := thetaSource.quantileFun t.val
  have hxa : x ≠ a := by
    intro he
    exact ht (thetaSource.strictMonoOn_quantileFun.injOn t.property c.property he)
  have hc := (differentiableAt_cutQuotient z hxa).hasDerivAt.scomp t.val
    (hasDerivAt_quantileFun thetaSource t.property)
  have he : cutQuantileMode z c =ᶠ[𝓝 t.val]
      fun y => cutQuotient z a (thetaSource.quantileFun y) := by
    filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with y hy
    exact cutQuantileMode_interior z c ⟨y, hy⟩
  have hd := (hc.congr_of_eventuallyEq he).deriv
  rw [hd, cutSourceDensity, cutQuantileMode_interior z c t]
  simp only [Complex.real_smul]
  have h := cutQuotient_source_equation z hxa
  change _ = (quantileSpeed thetaSource t.val : ℂ) *
    (-(I*z*cutQuotient z a x) - sourceLogDerivative x*(cutQuotient z a x+1))
  linear_combination (quantileSpeed thetaSource t.val : ℂ) * h

theorem cutSourceDensity_ae_deriv (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    cutSourceDensity z c =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv (cutQuantileMode z c) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (volume.ae_ne c.val)] with t ht hne
  exact (deriv_cutQuantileMode_eq_sourceDensity z c ⟨t, ht⟩ hne).symm

/-- Integrability of the full source current is produced, without separate termwise assumptions. -/
theorem intervalIntegrable_cutSourceDensity (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (cutSourceDensity z c) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)).mp (intervalIntegrable_deriv_cutQuantileMode z c)
  exact h.congr (cutSourceDensity_ae_deriv z c).symm

/-- Exact native source equation in weak form, with the complete interior Xi charge. -/
theorem cutQuantileMode_source_current (z : ℂ) (c : Ioo (0 : ℝ) 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in (0 : ℝ)..1, cutQuantileMode z c t * deriv φ t) =
      φ 0 - φ 1 - (∫ t in (0 : ℝ)..1, cutSourceDensity z c t * φ t) -
        cutCharge z (thetaSource.quantileFun c.val) * φ c.val := by
  rw [cutQuantileMode_weak_current]
  congr 2
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1 : ℝ), volume.ae_ne c.val] with t ht1 htc ht
  have hti : t ∈ Ioo (0 : ℝ) 1 := by
    rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    exact ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  rw [deriv_cutQuantileMode_eq_sourceDensity z c ⟨t, hti⟩ htc]

end RHTower.PaperThetaEndpoint
