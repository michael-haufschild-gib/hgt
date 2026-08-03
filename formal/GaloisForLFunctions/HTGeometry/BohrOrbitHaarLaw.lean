import GaloisForLFunctions.HTGeometry.BohrOrbitClosure

/-!
# The limiting time distribution of an asymptotic orbit

A path which is asymptotic to a phase flow sees the same time averages as the flow itself: the
difference tends to zero, and the running average of a function tending to zero tends to zero,
because the early part of the integral is bounded and the late part is uniformly small.

Along a rationally independent phase flow the running averages of a continuous function converge to
its Haar mean.  Hence for every continuous observable the time distribution of the asymptotic path
converges weakly to the push-forward of Haar measure under the parametrisation of the hull.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {ι : Type*}

/-- **A vanishing function has vanishing running average.**  Beyond a fixed time the integrand is
uniformly small, and the bounded contribution of the initial segment is divided by the window
length. -/
theorem tendsto_windowAverage_zero_of_tendsto_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hlim : Tendsto f atTop (nhds 0)) :
    Tendsto (windowAverage f) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero] at hlim ⊢
  intro ε hε
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hlim (ε / 4) (by linarith))
  set t₁ : ℝ := max t₀ 0 with ht₁def
  have ht₁nn : 0 ≤ t₁ := le_max_right _ _
  have ht₁ge : t₀ ≤ t₁ := le_max_left _ _
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t₁)).exists_bound_of_continuousOn
    hf.continuousOn
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, ht₁nn⟩)
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := hf.intervalIntegrable
  filter_upwards [eventually_ge_atTop t₁, eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop (4 * C * t₁ / ε)] with T hT₁ hT0 hTbig
  have hsplit : (∫ t in (0 : ℝ)..t₁, f t) + ∫ t in t₁..T, f t = ∫ t in (0 : ℝ)..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hb1 : ‖∫ t in (0 : ℝ)..t₁, f t‖ ≤ C * t₁ := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
      fun x hx => ?_).trans ?_
    · rw [Set.uIoc_of_le ht₁nn] at hx
      exact hC x ⟨hx.1.le, hx.2⟩
    · rw [sub_zero, abs_of_nonneg ht₁nn]
  have hb2 : ‖∫ t in t₁..T, f t‖ ≤ ε / 4 * T := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 4)
      fun x hx => ?_).trans ?_
    · rw [Set.uIoc_of_le hT₁] at hx
      exact (ht₀ x (le_trans ht₁ge hx.1.le)).le
    · rw [abs_of_nonneg (by linarith)]
      have hle : T - t₁ ≤ T := by linarith
      exact mul_le_mul_of_nonneg_left hle (by linarith)
  have hnorm : ‖windowAverage f T‖ ≤ C * t₁ / T + ε / 4 := by
    rw [windowAverage, ← hsplit, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hT0.le)]
    calc T⁻¹ * ‖(∫ t in (0 : ℝ)..t₁, f t) + ∫ t in t₁..T, f t‖
        ≤ T⁻¹ * (C * t₁ + ε / 4 * T) := by
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hb1 hb2)) ?_
          exact inv_nonneg.mpr hT0.le
      _ = C * t₁ / T + ε / 4 := by
          field_simp
  have hfrac : C * t₁ / T < ε / 4 := by
    rw [div_lt_iff₀ hε] at hTbig
    rw [div_lt_iff₀ hT0]
    nlinarith
  linarith

/-- **Asymptotically equal paths have the same limiting time average.** -/
theorem tendsto_windowAverage_of_tendsto_sub_zero {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hsub : Tendsto (fun t => f t - g t) atTop (nhds 0))
    {L : ℂ} (hL : Tendsto (windowAverage g) atTop (nhds L)) :
    Tendsto (windowAverage f) atTop (nhds L) := by
  have hdiff := tendsto_windowAverage_zero_of_tendsto_zero (hf.sub hg) hsub
  have heq : ∀ T : ℝ, windowAverage (f - g) T = windowAverage f T - windowAverage g T := by
    intro T
    rw [windowAverage, windowAverage, windowAverage, ← smul_sub]
    congr 1
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  have hsum := hdiff.add hL
  rw [zero_add] at hsum
  refine hsum.congr fun T => ?_
  rw [heq T]
  ring

/-- **The Haar limiting law of an asymptotic orbit.**  A path asymptotic to the phase flow of a
rationally independent frequency family has running averages converging to the Haar mean. -/
theorem tendsto_windowAverage_torusHaar_of_asymptotic [Countable ι] [DecidableEq ι]
    {omega : ι → ℝ} (h : RationallyIndependentSequence omega) (F : C(UnitAddTorus ι, ℂ))
    {G : ℝ → ℂ} (hG : Continuous G)
    (hasym : Tendsto (fun t => G t - F (clockPhasePoint omega t)) atTop (nhds 0)) :
    Tendsto (windowAverage G) atTop (nhds (∫ x, F x ∂(torusHaar ι))) := by
  refine tendsto_windowAverage_of_tendsto_sub_zero hG
    (F.continuous.comp (continuous_clockPhasePoint omega)) hasym ?_
  have hbase : Tendsto (fun T => forwardFlowAverage omega T F) atTop
      (nhds (∫ x, F x ∂(torusHaar ι))) := hasHaarForwardAverage_of_continuous h F
  exact hbase.congr fun T => rfl

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions

open Filter MeasureTheory Topology

noncomputable section

/-- **The Haar limiting law in the circle model.**  For an observable of the phase flow read in the
circle group of each coordinate, the running averages of an asymptotic path converge to the integral
of the observable against the push-forward of Haar measure under the parametrisation. -/
theorem tendsto_windowAverage_haar_circlePhaseFlow {ι : Type*} [Countable ι] [DecidableEq ι]
    {omega : ι → ℝ} (h : HTGeometry.RationallyIndependentSequence omega)
    (F : C((ι → Circle), ℂ)) {G : ℝ → ℂ} (hG : Continuous G)
    (hasym : Tendsto (fun t => G t - F (circlePhaseFlow omega t)) atTop (nhds 0)) :
    Tendsto (windowAverage G) atTop
      (nhds (∫ x, F (unitTorusHomeomorphCircles ι x) ∂(HTGeometry.torusHaar ι))) := by
  refine HTGeometry.tendsto_windowAverage_torusHaar_of_asymptotic h
    (F.comp ⟨fun x => unitTorusHomeomorphCircles ι x, (unitTorusHomeomorphCircles ι).continuous⟩)
    hG ?_
  refine hasym.congr fun t => ?_
  rw [circlePhaseFlow_eq]
  rfl

end

end GaloisForLFunctions
