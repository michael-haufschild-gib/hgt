import GaloisForLFunctions.HTGeometry.CircleWirtinger
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The radial derivative of a circle mean

For a `C¹` function `h : ℂ → ℂ` the circle mean `r ↦ ∫_{-π}^{π} h(r e^{iθ}) dθ` is differentiable, and
its derivative is the integral of the radial derivative.  Because the angular derivative integrates
to zero over a closed circle, the holomorphic and antiholomorphic contributions to that integral
agree, so on a circle of nonzero radius the radial derivative of the circle mean is twice the
`∂̄` term alone:

`(d/dr) ∫_{-π}^{π} h(r e^{iθ}) dθ = 2 ∫_{-π}^{π} e^{-iθ} ∂̄h(r e^{iθ}) dθ`.

This is the identity that carries all the information of the Cauchy–Pompeiu formula: integrating it
in `r` and letting the inner radius tend to zero recovers the value at the centre.

* `HTGeometry.hasDerivAt_circleMean` : differentiation under the integral sign.
* `HTGeometry.hasDerivAt_circleMean_dzbar` : only `∂̄` survives.
-/

open Complex Real intervalIntegral MeasureTheory Set
open scoped ENNReal

namespace HTGeometry

variable {h : ℂ → ℂ}

section RadialDerivative

/-- The radial derivative of `h` on the circle of radius `s`, as a function of `(s, θ)`. -/
private noncomputable def radialIntegrand (h : ℂ → ℂ) (s θ : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I) * dz h (circleMap 0 s θ)
    + Complex.exp (-(θ * Complex.I)) * dzbar h (circleMap 0 s θ)

private theorem continuous_radialIntegrand_snd (hC : ContDiff ℝ 1 h) (s : ℝ) :
    Continuous fun θ : ℝ => radialIntegrand h s θ := by
  have hc0 : Continuous fun θ : ℝ => circleMap 0 s θ := continuous_circleMap 0 s
  have hcz : Continuous fun θ : ℝ => dz h (circleMap 0 s θ) := (continuous_dz hC).comp hc0
  have hcb : Continuous fun θ : ℝ => dzbar h (circleMap 0 s θ) := (continuous_dzbar hC).comp hc0
  unfold radialIntegrand
  fun_prop

/-- **Differentiation of the circle mean under the integral sign.** -/
theorem hasDerivAt_circleMean (hC : ContDiff ℝ 1 h) (r : ℝ) :
    HasDerivAt (circleMean h)
      (∫ θ in (-π)..π, radialIntegrand h r θ) r := by
  have hd : Differentiable ℝ h := hC.differentiable one_ne_zero
  -- a uniform bound for the radial derivative over a neighbourhood of `r`
  obtain ⟨C, hCbound⟩ :=
    (isCompact_closedBall (0 : ℂ) (|r| + 1)).exists_bound_of_continuousOn
      (f := fun w : ℂ => ‖dz h w‖ + ‖dzbar h w‖)
      (((continuous_dz hC).norm.add (continuous_dzbar hC).norm).continuousOn)
  have hmem : Metric.closedBall r 1 ∈ nhds r := Metric.closedBall_mem_nhds r one_pos
  have hball : ∀ s ∈ Metric.closedBall r 1, ∀ θ : ℝ,
      circleMap 0 s θ ∈ Metric.closedBall (0 : ℂ) (|r| + 1) := by
    intro s hs θ
    have hs' : |s - r| ≤ 1 := by
      simpa [Real.dist_eq] using hs
    have : |s| ≤ |r| + 1 := by
      have := abs_sub_abs_le_abs_sub s r
      linarith
    simpa [Complex.dist_eq, norm_circleMap_zero] using this
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s θ => h (circleMap 0 s θ)) (F' := fun s θ => radialIntegrand h s θ)
    (bound := fun _ => C) (s := Metric.closedBall r 1) hmem ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with s
    exact ((hd.continuous.comp (continuous_circleMap 0 s)).aestronglyMeasurable).restrict
  · exact ((hd.continuous.comp (continuous_circleMap 0 r)).intervalIntegrable _ _)
  · exact ((continuous_radialIntegrand_snd hC r).aestronglyMeasurable).restrict
  · filter_upwards with θ _ s hs
    have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have h2 : ‖Complex.exp (-((θ : ℂ) * Complex.I))‖ = 1 := by
      have hneg : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hneg]
      exact Complex.norm_exp_ofReal_mul_I (-θ)
    calc ‖radialIntegrand h s θ‖
        ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 s θ)‖
          + ‖Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 s θ)‖ :=
          norm_add_le _ _
      _ = ‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖ := by
          rw [norm_mul, norm_mul, h1, h2, one_mul, one_mul]
      _ ≤ C := by
          have := hCbound _ (hball s hs θ)
          calc ‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖
              ≤ ‖‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖‖ := le_abs_self _
            _ ≤ C := this
  · exact intervalIntegrable_const
  · filter_upwards with θ _ s _
    exact hasDerivAt_circle_radius hd s θ

/-- **On a circle of nonzero radius only `∂̄` contributes to the radial derivative of the circle
mean.** -/
theorem hasDerivAt_circleMean_dzbar (hC : ContDiff ℝ 1 h) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (circleMean h)
      (2 * ∫ θ in (-π)..π,
        Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ)) r := by
  have hkey := circle_angle_integral_eq hC r
  have hcm : ∀ θ : ℝ, circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ; simp [circleMap]
  have hconj : ∀ θ : ℝ,
      (starRingEnd ℂ) (circleMap 0 r θ) = (r : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
    intro θ
    rw [hcm, map_mul, ← Complex.exp_conj]
    congr 1
    · simp
    · congr 1
      simp
  have hc0 : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hcz : Continuous fun θ : ℝ => dz h (circleMap 0 r θ) := (continuous_dz hC).comp hc0
  have hcb : Continuous fun θ : ℝ => dzbar h (circleMap 0 r θ) := (continuous_dzbar hC).comp hc0
  have hIz : IntervalIntegrable
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ))
      MeasureTheory.volume (-π) π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hIb : IntervalIntegrable
      (fun θ : ℝ => Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ))
      MeasureTheory.volume (-π) π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsplit : (∫ θ in (-π)..π,
      Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ)) =
      ∫ θ in (-π)..π,
        Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ) := by
    have hL : (∫ θ in (-π)..π, circleMap 0 r θ * dz h (circleMap 0 r θ)) =
        (r : ℂ) * ∫ θ in (-π)..π,
          Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hcm θ]; ring
    have hR : (∫ θ in (-π)..π,
        (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ)) =
        (r : ℂ) * ∫ θ in (-π)..π,
          Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hconj θ]; ring
    rw [hL, hR] at hkey
    exact mul_left_cancel₀ (by exact_mod_cast hr) hkey
  have hmain := hasDerivAt_circleMean hC r
  convert hmain using 1
  unfold radialIntegrand
  rw [intervalIntegral.integral_add hIz hIb, hsplit]
  ring

end RadialDerivative


section CauchyKernel

/-- **The Cauchy kernel is locally integrable in the plane.**  In polar coordinates the area
element cancels the singularity exactly, so the integral over a ball of radius `R` is bounded by
`2πR`. -/
theorem lintegral_ball_norm_inv (R : ℝ) :
    ∫⁻ w : ℂ, Set.indicator (Metric.ball (0 : ℂ) R)
        (fun w => ENNReal.ofReal ‖w‖⁻¹) w ≤ ENNReal.ofReal R * ENNReal.ofReal (2 * π) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have htgt : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [htgt]
  have hle : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      ENNReal.ofReal p.1 • Set.indicator (Metric.ball (0 : ℂ) R)
        (fun w => ENNReal.ofReal ‖w‖⁻¹) (Complex.polarCoord.symm p)
      ≤ Set.indicator (Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-π) π) (fun _ => (1 : ℝ≥0∞)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr
    by_cases hmem : r < R
    · have h1 : Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) R := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm]; exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∈ Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-π) π := ⟨⟨hr, hmem⟩, hθ⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, hnorm, smul_eq_mul,
        ← ENNReal.ofReal_mul (le_of_lt hr), mul_inv_cancel₀ (ne_of_gt hr)]
      simp
    · have h1 : Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) R := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm]; exact hmem
      rw [Set.indicator_of_notMem h1, smul_zero]
      exact bot_le
  calc ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
        ENNReal.ofReal p.1 • Set.indicator (Metric.ball (0 : ℂ) R)
          (fun w => ENNReal.ofReal ‖w‖⁻¹) (Complex.polarCoord.symm p)
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
          Set.indicator (Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-π) π) (fun _ => (1 : ℝ≥0∞)) p :=
        lintegral_mono_ae ((MeasureTheory.ae_restrict_iff'
          (measurableSet_Ioi.prod measurableSet_Ioo)).2
          (Filter.Eventually.of_forall hle))
    _ ≤ ∫⁻ p, Set.indicator (Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-π) π) (fun _ => (1 : ℝ≥0∞)) p :=
        MeasureTheory.setLIntegral_le_lintegral _ _
    _ = MeasureTheory.volume (Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
        rw [MeasureTheory.lintegral_indicator (by measurability)]
        simp
    _ = ENNReal.ofReal R * ENNReal.ofReal (2 * π) := by
        rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
          Real.volume_Ioo, Real.volume_Ioo, sub_zero, show π - -π = 2 * π from by ring]


/-- The Cauchy kernel is integrable on every ball. -/
theorem integrableOn_norm_inv_ball (R : ℝ) :
    MeasureTheory.IntegrableOn (fun w : ℂ => ‖w‖⁻¹) (Metric.ball 0 R) := by
  refine ⟨(measurable_norm.inv.aestronglyMeasurable).restrict, ?_⟩
  have hbound : (∫⁻ w in Metric.ball (0 : ℂ) R, ‖(‖w‖⁻¹ : ℝ)‖ₑ)
      ≤ ENNReal.ofReal R * ENNReal.ofReal (2 * π) := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
    refine le_trans (lintegral_mono fun w => ?_) (lintegral_ball_norm_inv R)
    by_cases hw : w ∈ Metric.ball (0 : ℂ) R
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      rw [Real.enorm_eq_ofReal (by positivity)]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  exact lt_of_le_of_lt hbound (by finiteness)

/-- **The `∂̄` Cauchy kernel of a `C¹` function is integrable on every ball.** -/
theorem integrableOn_dzbar_div_ball (hC : ContDiff ℝ 1 h) (R : ℝ) :
    MeasureTheory.IntegrableOn (fun w : ℂ => dzbar h w / w) (Metric.ball 0 R) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (f := fun w : ℂ => dzbar h w) ((continuous_dzbar hC).continuousOn)
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hM' : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖dzbar h w‖ ≤ M' :=
    fun w hw => le_trans (hM w hw) (le_max_left _ _)
  refine MeasureTheory.Integrable.mono' ((integrableOn_norm_inv_ball R).const_mul M') ?_ ?_
  · exact (((continuous_dzbar hC).measurable.mul measurable_inv).aestronglyMeasurable).restrict
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_ball (fun w hw => ?_)
    have hwc : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
    rw [norm_div]
    calc ‖dzbar h w‖ / ‖w‖ ≤ M' / ‖w‖ := by
          gcongr
          exact hM' w hwc
      _ = M' * ‖w‖⁻¹ := by rw [div_eq_mul_inv]

end CauchyKernel

section Annulus

/-- The open annulus of radii `ε` and `R` about the origin. -/
def deningerAnnulus (eps R : ℝ) : Set ℂ := {w : ℂ | eps < ‖w‖ ∧ ‖w‖ < R}

/-- The polar parametrisation is the circle map. -/
theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap]
  simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- The integrand of the `∂̄` kernel in polar coordinates. -/
private noncomputable def polarIntegrand (h : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-((p.2 : ℂ) * Complex.I)) * dzbar h (circleMap 0 p.1 p.2)

private theorem continuous_polarIntegrand (hC : ContDiff ℝ 1 h) :
    Continuous (polarIntegrand h) := by
  have hcm : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    unfold circleMap
    fun_prop
  have hb : Continuous fun p : ℝ × ℝ => dzbar h (circleMap 0 p.1 p.2) :=
    (continuous_dzbar hC).comp hcm
  unfold polarIntegrand
  fun_prop

/-- **The `∂̄` kernel over an annulus, in polar coordinates.** -/
theorem setIntegral_annulus_dzbar_div {eps R : ℝ} (hepspos : 0 < eps) :
    (∫ w in deningerAnnulus eps R, dzbar h w / w) =
      ∫ p in Set.Ioo eps R ×ˢ Set.Ioo (-π) π, polarIntegrand h p := by
  set A : Set ℂ := deningerAnnulus eps R with hA
  set f : ℂ → ℂ := fun w => dzbar h w / w with hf
  have hAopen : IsOpen A := by
    have : A = (fun w : ℂ => ‖w‖) ⁻¹' (Set.Ioo eps R) := by
      ext w; simp [hA, deningerAnnulus, Set.mem_Ioo]
    rw [this]; exact isOpen_Ioo.preimage continuous_norm
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hBmeas : MeasurableSet (Set.Ioo eps R ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hpolar := Complex.integral_comp_polarCoord_symm (Set.indicator A f)
  rw [MeasureTheory.integral_indicator hAmeas] at hpolar
  have htgt : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← hpolar, htgt]
  have key : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      p.1 • Set.indicator A f (Complex.polarCoord.symm p)
        = Set.indicator (Set.Ioo eps R ×ˢ Set.Ioo (-π) π) (polarIntegrand h) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    have hsymm : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ :=
      polarCoord_symm_eq_circleMap (r, θ)
    have hnorm : ‖circleMap 0 r θ‖ = r := by
      rw [norm_circleMap_zero, abs_of_pos hr]
    by_cases hmem : eps < r ∧ r < R
    · have h1 : circleMap 0 r θ ∈ A := by
        rw [hA]; simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]; exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∈ Set.Ioo eps R ×ˢ Set.Ioo (-π) π := ⟨hmem, hθ⟩
      rw [hsymm, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      show (r : ℝ) • (dzbar h (circleMap 0 r θ) / circleMap 0 r θ)
        = Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ)
      have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        simp [circleMap]
      have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hene : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      set D : ℂ := dzbar h (circleMap 0 r θ) with hD
      rw [Complex.real_smul, hcm, Complex.exp_neg]
      field_simp
    · have h1 : circleMap 0 r θ ∉ A := by
        rw [hA]; simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]; exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∉ Set.Ioo eps R ×ˢ Set.Ioo (-π) π := by
        intro hc; exact hmem hc.1
      rw [hsymm, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_zero]
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key,
    MeasureTheory.setIntegral_indicator hBmeas]
  have hInter : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π ∩ (Set.Ioo eps R ×ˢ Set.Ioo (-π) π)
      = Set.Ioo eps R ×ˢ Set.Ioo (-π) π :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (fun x hx => lt_trans hepspos hx.1) (subset_refl _))
  rw [hInter]

/-- The polar integrand is integrable on the closed polyrectangle, hence on the open one. -/
private theorem integrableOn_polarIntegrand (hC : ContDiff ℝ 1 h) (eps R : ℝ) :
    MeasureTheory.IntegrableOn (polarIntegrand h)
      (Set.Ioo eps R ×ˢ Set.Ioo (-π) π) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hcompact : IsCompact (Set.Icc eps R ×ˢ Set.Icc (-π) π) :=
    (isCompact_Icc).prod isCompact_Icc
  have hInt : MeasureTheory.IntegrableOn (polarIntegrand h)
      (Set.Icc eps R ×ˢ Set.Icc (-π) π) MeasureTheory.volume :=
    (continuous_polarIntegrand hC).continuousOn.integrableOn_compact hcompact
  have hsub : Set.Ioo eps R ×ˢ Set.Ioo (-π) π ⊆ Set.Icc eps R ×ˢ Set.Icc (-π) π :=
    Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  have := hInt.mono_set hsub
  rwa [← MeasureTheory.Measure.volume_eq_prod]

/-- **The `∂̄` kernel over an annulus as an iterated interval integral.** -/
theorem setIntegral_annulus_eq_intervalIntegral (hC : ContDiff ℝ 1 h) {eps R : ℝ}
    (hepspos : 0 < eps) (hle : eps ≤ R) :
    (∫ w in deningerAnnulus eps R, dzbar h w / w) =
      ∫ r in eps..R, ∫ θ in (-π)..π,
        Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ) := by
  rw [setIntegral_annulus_dzbar_div (h := h) hepspos, MeasureTheory.Measure.volume_eq_prod,
    setIntegral_prod _ (integrableOn_polarIntegrand hC eps R),
    intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rfl


/-- The `∂̄` circle integral as a function of the radius. -/
private noncomputable def dzbarCircleIntegral (h : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∫ θ in (-π)..π, Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ)

private theorem continuous_dzbarCircleIntegral (hC : ContDiff ℝ 1 h) :
    Continuous (dzbarCircleIntegral h) := by
  have huc : Continuous (Function.uncurry fun r θ => polarIntegrand h (r, θ)) := by
    have : (Function.uncurry fun r θ => polarIntegrand h (r, θ)) = polarIntegrand h := by
      funext p; cases p; rfl
    rw [this]; exact continuous_polarIntegrand hC
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := -π) huc (continuous_const)

/-- **The circle mean difference is twice the `∂̄` kernel over the annulus.**  Integrating the
radial derivative of the circle mean from `ε` to `R` and rewriting the result in polar coordinates
gives the annulus integral. -/
theorem circleMean_sub_eq_annulus (hC : ContDiff ℝ 1 h) {eps R : ℝ}
    (hepspos : 0 < eps) (hle : eps ≤ R) :
    circleMean h R - circleMean h eps = 2 * ∫ w in deningerAnnulus eps R, dzbar h w / w := by
  have hcont : Continuous fun r : ℝ => 2 * dzbarCircleIntegral h r :=
    (continuous_dzbarCircleIntegral hC).const_smul (2 : ℂ) |>.congr (fun r => by
      simp [smul_eq_mul])
  have hderiv : ∀ r ∈ Set.uIcc eps R,
      HasDerivAt (circleMean h) (2 * dzbarCircleIntegral h r) r := by
    intro r hr
    rw [Set.uIcc_of_le hle] at hr
    exact hasDerivAt_circleMean_dzbar hC (by linarith [hr.1] : r ≠ 0)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  rw [setIntegral_annulus_eq_intervalIntegral hC hepspos hle, ← intervalIntegral.integral_const_mul]
  exact hFTC.symm

end Annulus

section Limit

/-- The punctured ball is the increasing union of annuli. -/
theorem iUnion_annulus {R : ℝ} (hR : 0 < R) :
    (⋃ n : ℕ, deningerAnnulus (R / (n + 2)) R) = Metric.ball (0 : ℂ) R \ {0} := by
  ext w
  simp only [Set.mem_iUnion, deningerAnnulus, Set.mem_setOf_eq, Set.mem_sdiff,
    Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, h1, h2⟩
    refine ⟨h2, ?_⟩
    intro hw
    rw [hw] at h1
    simp only [norm_zero] at h1
    have : 0 < R / ((n : ℝ) + 2) := by positivity
    linarith
  · rintro ⟨h2, h0⟩
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h0
    obtain ⟨n, hn⟩ := exists_nat_gt (R / ‖w‖)
    refine ⟨n, ?_, h2⟩
    have hn2 : R / ‖w‖ < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at hn2
    linarith

/-- The annuli increase. -/
theorem monotone_annulus {R : ℝ} (hR : 0 < R) :
    Monotone fun n : ℕ => deningerAnnulus (R / (n + 2)) R := by
  intro m n hmn w hw
  refine ⟨lt_of_le_of_lt ?_ hw.1, hw.2⟩
  apply div_le_div_of_nonneg_left (le_of_lt hR) (by positivity)
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  linarith

/-- The circle mean at radius zero is `2π` times the value at the origin. -/
theorem circleMean_zero : circleMean h 0 = (2 * π : ℝ) • h 0 := by
  have hcm : ∀ θ : ℝ, circleMap 0 0 θ = 0 := fun θ => by simp [circleMap]
  rw [circleMean]
  simp only [hcm]
  rw [intervalIntegral.integral_const]
  congr 1
  ring

/-- **Cauchy–Pompeiu at the centre of a disc.**  For a continuously real-differentiable `h`,

`h(0) = (1/2π) ∫_{-π}^{π} h(R e^{iθ}) dθ − (1/π) ∬_{|w|<R} ∂̄h(w)/w dA(w)`.

The proof integrates the radial derivative of the circle mean, which sees only `∂̄`, from an inner
radius to `R`, rewrites the result as the annulus integral of the `∂̄` Cauchy kernel, and lets the
inner radius tend to zero. -/
theorem cauchyPompeiu_center (hC : ContDiff ℝ 1 h) {R : ℝ} (hR : 0 < R) :
    circleMean h R - (2 * π : ℝ) • h 0 =
      2 * ∫ w in Metric.ball (0 : ℂ) R, dzbar h w / w := by
  have hdiff : Differentiable ℝ (circleMean h) := fun r => (hasDerivAt_circleMean hC r).differentiableAt
  have hcontMean : Continuous (circleMean h) := hdiff.continuous
  have heps : Filter.Tendsto (fun n : ℕ => R / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
    have := Filter.Tendsto.const_div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) tendsto_natCast_atTop_atTop) R
    simpa using this
  have hmean : Filter.Tendsto (fun n : ℕ => circleMean h (R / ((n : ℝ) + 2)))
      Filter.atTop (nhds (circleMean h 0)) := (hcontMean.tendsto 0).comp heps
  have hsets : ∀ n : ℕ, MeasurableSet (deningerAnnulus (R / ((n : ℝ) + 2)) R) := by
    intro n
    have : deningerAnnulus (R / ((n : ℝ) + 2)) R
        = (fun w : ℂ => ‖w‖) ⁻¹' (Set.Ioo (R / ((n : ℝ) + 2)) R) := by
      ext w; simp [deningerAnnulus, Set.mem_Ioo]
    rw [this]
    exact (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hInt : MeasureTheory.IntegrableOn (fun w : ℂ => dzbar h w / w)
      (⋃ n : ℕ, deningerAnnulus (R / ((n : ℝ) + 2)) R) := by
    rw [iUnion_annulus hR]
    exact (integrableOn_dzbar_div_ball hC R).mono_set Set.sdiff_subset
  have htend := MeasureTheory.tendsto_setIntegral_of_monotone hsets (monotone_annulus hR) hInt
  rw [iUnion_annulus hR] at htend
  have hball : (∫ w in Metric.ball (0 : ℂ) R \ {0}, dzbar h w / w)
      = ∫ w in Metric.ball (0 : ℂ) R, dzbar h w / w := by
    refine MeasureTheory.setIntegral_congr_set ?_
    exact MeasureTheory.sdiff_null_ae_eq_self (measure_singleton 0)
  rw [hball] at htend
  have hkey : ∀ n : ℕ, circleMean h R - circleMean h (R / ((n : ℝ) + 2)) =
      2 * ∫ w in deningerAnnulus (R / ((n : ℝ) + 2)) R, dzbar h w / w := by
    intro n
    refine circleMean_sub_eq_annulus hC (by positivity) ?_
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact div_le_self (le_of_lt hR) h2
  have hlhs : Filter.Tendsto (fun n : ℕ => circleMean h R - circleMean h (R / ((n : ℝ) + 2)))
      Filter.atTop (nhds (circleMean h R - circleMean h 0)) :=
    Filter.Tendsto.const_sub _ hmean
  have hrhs : Filter.Tendsto
      (fun n : ℕ => 2 * ∫ w in deningerAnnulus (R / ((n : ℝ) + 2)) R, dzbar h w / w)
      Filter.atTop (nhds (2 * ∫ w in Metric.ball (0 : ℂ) R, dzbar h w / w)) :=
    htend.const_mul 2
  have := tendsto_nhds_unique (by simpa only [hkey] using hlhs) hrhs
  rw [circleMean_zero] at this
  exact this

end Limit



end HTGeometry
