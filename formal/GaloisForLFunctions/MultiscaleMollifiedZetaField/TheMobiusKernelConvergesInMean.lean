import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheSmoothedMobiusKernelTestsDerivatives

/-!
# Mean convergence of the dilated Möbius kernel

The bounded smoothed kernel converges in absolute mean on the unit
interval. Its shrinking boundary layer therefore gives a uniform error
bound for smooth logarithmic tests with bounded second derivative.
-/

open ArithmeticFunction Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Absolute mean error of the first smoothed Möbius kernel under dilation. -/
def smoothedMobiusKernelMeanError (L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, |smoothedMobiusKernel (L * x) - 1|

/-- Continuity of the dilated kernel on its fixed unit interval. -/
theorem continuousOn_dilatedSmoothedMobiusKernel {L : ℝ} (hL : 0 ≤ L) :
    ContinuousOn (fun x => smoothedMobiusKernel (L * x)) (Icc 0 1) := by
  have hm : MapsTo (fun x => L * x) (Icc 0 1) (Icc 0 L) :=
    fun x hx => ⟨mul_nonneg hL hx.1,
      (mul_le_mul_of_nonneg_left hx.2 hL).trans_eq (mul_one L)⟩
  exact (continuousOn_smoothedMobiusKernel hL).comp
    (continuous_const.mul continuous_id).continuousOn hm

/-- The cutoff boundary layer has vanishing absolute mean. -/
theorem tendsto_smoothedMobiusKernelMeanError :
    Tendsto smoothedMobiusKernelMeanError atTop (𝓝 0) := by
  obtain ⟨⟨D, hD, hb⟩, hlim⟩ := smoothedMobiusKernel_bounded_and_tendsto
  have hc {L : ℝ} (hL : 0 ≤ L) :
      ContinuousOn (fun x => |smoothedMobiusKernel (L * x) - 1|) (Icc 0 1) :=
    ((continuousOn_dilatedSmoothedMobiusKernel hL).sub continuous_const.continuousOn).abs
  have hmeas : ∀ᶠ L : ℝ in atTop,
      AEStronglyMeasurable (fun x => |smoothedMobiusKernel (L * x) - 1|)
        (volume.restrict (uIoc 0 1)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    rw [uIoc_of_le zero_le_one]
    exact ((hc hL).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᶠ L : ℝ in atTop, ∀ᵐ x : ℝ,
      x ∈ uIoc (0 : ℝ) 1 → ‖|smoothedMobiusKernel (L * x) - 1|‖ ≤ D + 1 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    filter_upwards with x
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, abs_abs]
    have hh : |smoothedMobiusKernel (L * x)| + |(1 : ℝ)| ≤ D + 1 := by
      simpa only [abs_one] using add_le_add (hb _ (mul_nonneg hL hx.1.le))
        (le_refl (1 : ℝ))
    exact (abs_sub _ _).trans hh
  have hpoint : ∀ᵐ x : ℝ, x ∈ uIoc (0 : ℝ) 1 →
      Tendsto (fun L : ℝ => |smoothedMobiusKernel (L * x) - 1|) atTop (𝓝 0) := by
    filter_upwards with x
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    simpa only [sub_self, abs_zero, Function.comp_def, id_eq] using
      ((hlim.comp (tendsto_id.atTop_mul_const hx.1)).sub_const 1).abs
  have hi : IntervalIntegrable (fun _ : ℝ => D + 1) volume 0 1 := intervalIntegrable_const
  have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => D + 1) hmeas hbound hi hpoint
  change Tendsto (fun L : ℝ => ∫ x in (0 : ℝ)..1,
    |smoothedMobiusKernel (L * x) - 1|) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using hh


/-- The logarithmically normalized Möbius transform of a smooth test. -/
def scaledMobiusLogTest (f : ℝ → ℝ) (L u : ℝ) : ℝ :=
  L * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
    ((moebius n : ℤ) : ℝ) / (n : ℝ) * f (u - Real.log n / L))

/-- A compact second-derivative bound controls every cutoff by one absolute-mean error. -/
theorem exists_scaledMobiusLogTest_error_bound {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) (hf0 : f 0 = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, 0 < L → ∀ u ∈ Icc (0 : ℝ) 1,
      |scaledMobiusLogTest f L u - f₁ u| ≤
        |f₁ 0| * |smoothedMobiusKernel (L * u) - 1| + M * smoothedMobiusKernelMeanError L := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc₂.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (f₂ 0)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨M, hM0, ?_⟩
  intro L hL u hu
  have hK : ContinuousOn (fun x => smoothedMobiusKernel (L * x) - 1) (Icc 0 1) :=
    (continuousOn_dilatedSmoothedMobiusKernel hL.le).sub continuous_const.continuousOn
  have hsub : Icc (0 : ℝ) u ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hu.2
  have hKu : IntervalIntegrable (fun x => smoothedMobiusKernel (L * x) - 1) volume 0 u :=
    (hK.mono hsub).intervalIntegrable_of_Icc hu.1
  have hF : Continuous (fun x => f₂ (u - x)) := hc₂.comp (continuous_const.sub continuous_id)
  have hprod : IntervalIntegrable (fun x => f₂ (u - x) *
      (smoothedMobiusKernel (L * x) - 1)) volume 0 u :=
    (hF.continuousOn.mul (hK.mono hsub)).intervalIntegrable_of_Icc hu.1
  have hprimitive : (∫ x in (0 : ℝ)..u, f₂ (u - x)) = f₁ u - f₁ 0 := by
    have hd (x : ℝ) : HasDerivAt (fun x => -f₁ (u - x)) (f₂ (u - x)) x := by
      apply (((hf₁ (u - x)).comp x ((hasDerivAt_id x).const_sub u)).neg).congr_deriv
      ring
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hF.intervalIntegrable 0 u)
    simpa only [sub_self, sub_zero, neg_sub_neg] using hh
  have heq : scaledMobiusLogTest f L u - f₁ u =
      f₁ 0 * (smoothedMobiusKernel (L * u) - 1) +
        ∫ x in (0 : ℝ)..u, f₂ (u - x) * (smoothedMobiusKernel (L * x) - 1) := by
    rw [scaledMobiusLogTest, mobius_log_test_eq_kernel_integral hf hf₁ hc₂ hf0 hL hu.1]
    have hi : IntervalIntegrable (fun x => f₂ (u - x) * smoothedMobiusKernel (L * x))
        volume 0 u := (hF.continuousOn.mul
      ((continuousOn_dilatedSmoothedMobiusKernel hL.le).mono hsub)).intervalIntegrable_of_Icc hu.1
    simp only [mul_sub, mul_one]
    rw [intervalIntegral.integral_sub hi (hF.intervalIntegrable 0 u), hprimitive]
    ring
  have hpartial : (∫ x in (0 : ℝ)..u, |smoothedMobiusKernel (L * x) - 1|) ≤
      smoothedMobiusKernelMeanError L := by
    have htail : IntervalIntegrable (fun x => |smoothedMobiusKernel (L * x) - 1|) volume u 1 :=
      (hK.abs.mono (Icc_subset_Icc hu.1 le_rfl)).intervalIntegrable_of_Icc hu.2
    have hs := intervalIntegral.integral_add_adjacent_intervals («μ» := volume) hKu.abs htail
    have hn := intervalIntegral.integral_nonneg_of_forall («μ» := volume) hu.2
      (fun x => abs_nonneg (smoothedMobiusKernel (L * x) - 1))
    change _ ≤ ∫ x in (0 : ℝ)..1, |smoothedMobiusKernel (L * x) - 1|
    linarith only [hs, hn]
  have hib : |∫ x in (0 : ℝ)..u, f₂ (u - x) *
      (smoothedMobiusKernel (L * x) - 1)| ≤ M * smoothedMobiusKernelMeanError L := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..u, |f₂ (u - x) * (smoothedMobiusKernel (L * x) - 1)| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm hu.1
            (f := fun x => f₂ (u - x) * (smoothedMobiusKernel (L * x) - 1)))
      _ ≤ ∫ x in (0 : ℝ)..u, M * |smoothedMobiusKernel (L * x) - 1| := by
        apply intervalIntegral.integral_mono_on hu.1 hprod.abs (hKu.abs.const_mul M)
        intro x hx
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        simpa only [Real.norm_eq_abs] using hM (u - x)
          ⟨sub_nonneg.mpr hx.2, (sub_le_self u hx.1).trans hu.2⟩
      _ = M * ∫ x in (0 : ℝ)..u, |smoothedMobiusKernel (L * x) - 1| :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hpartial hM0
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  exact add_le_add le_rfl hib

/-- Smooth logarithmic Möbius tests converge uniformly away from the cutoff endpoint. -/
theorem scaledMobiusLogTest_converges_uniformly {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hc₂ : Continuous f₂) (hf0 : f 0 = 0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc δ 1,
      |scaledMobiusLogTest f L u - f₁ u| < ε := by
  obtain ⟨M, hM, hb⟩ := exists_scaledMobiusLogTest_error_bound hf hf₁ hc₂ hf0
  let η : ℝ := ε / (2 * (|f₁ 0| + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have htail : ∀ᶠ y : ℝ in atTop, |smoothedMobiusKernel y - 1| < η := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      smoothedMobiusKernel_bounded_and_tendsto.2.eventually (Metric.ball_mem_nhds 1 hη)
  obtain ⟨K, hK⟩ := eventually_atTop.mp htail
  have hmean : ∀ᶠ L : ℝ in atTop, M * smoothedMobiusKernelMeanError L < ε / 2 := by
    have hh := (tendsto_smoothedMobiusKernelMeanError.const_mul M).eventually_lt_const
      (show M * 0 < ε / 2 by simpa using half_pos hε)
    exact hh
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (K / δ), hmean] with L hL hLK hLM
  intro u hu
  have hKu : K ≤ L * u := calc
    K ≤ L * δ := (div_le_iff₀ hδ).mp hLK
    _ ≤ L * u := mul_le_mul_of_nonneg_left hu.1 hL.le
  have hfirst : |f₁ 0| * |smoothedMobiusKernel (L * u) - 1| ≤ ε / 2 := by
    have hprod : |f₁ 0| * η ≤ ε / 2 := by
      have hden : 0 < |f₁ 0| + 1 := by positivity
      calc
        _ ≤ (|f₁ 0| + 1) * η := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one) hη.le
        _ = ε / 2 := by dsimp only [η]; field_simp [hden.ne'] <;> ring
    exact (mul_le_mul_of_nonneg_left (hK (L * u) hKu).le (abs_nonneg _)).trans hprod
  have he := hb L hL u ⟨hδ.le.trans hu.1, hu.2⟩
  linarith only [he, hfirst, hLM]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
