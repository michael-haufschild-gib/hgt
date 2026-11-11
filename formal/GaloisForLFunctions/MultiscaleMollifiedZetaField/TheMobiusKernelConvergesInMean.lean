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
    exact (abs_sub _ _).trans (by simpa only [abs_one] using
      add_le_add (hb _ (mul_nonneg hL hx.1.le)) le_rfl)
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
  simpa only [intervalIntegral.integral_zero, smoothedMobiusKernelMeanError] using hh


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
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (f₂ 0)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨M, hM0, ?_⟩
  intro L hL u hu
  have hK := (continuousOn_dilatedSmoothedMobiusKernel hL.le).sub continuous_const.continuousOn
  have hsub : Icc (0 : ℝ) u ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hu.2
  have hKu : IntervalIntegrable (fun x => smoothedMobiusKernel (L * x) - 1) volume 0 u :=
    (hK.mono hsub).intervalIntegrable_of_Icc hu.1
  have hF : Continuous (fun x => f₂ (u - x)) := hc₂.comp (continuous_const.sub continuous_id)
  have hprod : IntervalIntegrable (fun x => f₂ (u - x) *
      (smoothedMobiusKernel (L * x) - 1)) volume 0 u :=
    (hF.continuousOn.mul (hK.mono hsub)).intervalIntegrable_of_Icc hu.1
  have hprimitive : (∫ x in (0 : ℝ)..u, f₂ (u - x)) = f₁ u - f₁ 0 := by
    have hd (x : ℝ) : HasDerivAt (fun x => -f₁ (u - x)) (f₂ (u - x)) x := by
      convert (((hf₁ (u - x)).comp x ((hasDerivAt_id x).const_sub u)).neg) using 1 <;> ring
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
    have hn := intervalIntegral.integral_nonneg_of_forall hu.2
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

end GaloisForLFunctions.MultiscaleMollifiedZetaField
