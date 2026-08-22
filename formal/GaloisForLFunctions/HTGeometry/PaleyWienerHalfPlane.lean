import GaloisForLFunctions.HTGeometry.HardyDatum

/-!
# Paley--Wiener for the Hardy space of a half-plane

Every function holomorphic on `Re w > 0` whose restrictions to the vertical lines have uniformly
bounded `L²` mass is the half-line Laplace transform of a square-integrable datum on `(0, ∞)`.
The datum is the common weighted inverse Fourier transform of the boundary values; the weight
`e^{-σx}` forces it to vanish on the negative half-line as `σ → ∞` and keeps its mass bounded as
`σ → 0`.

## Main results

* `hardyDatum`
* `memLp_two_hardyDatum`
* `isHalfPlaneHardy_eq_laplaceRay`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology FourierTransform

open scoped ContDiff SchwartzMap

noncomputable section

/-- The datum of a Hardy function: its boundary inverse Fourier transform on the line `Re w = 1`,
weighted back by `e^{x}`. -/
def hardyDatum (F : ℂ → ℂ) {M : ℝ} (hF : IsHalfPlaneHardy F M) : ℝ → ℂ :=
  fun x => ((Real.exp (1 * x) : ℝ) : ℂ)
    * (hardyPreimage F 1 (hF.memLp 1 one_pos) : ℝ → ℂ) x

theorem aestronglyMeasurable_hardyDatum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    AEStronglyMeasurable (hardyDatum F hF) volume := by
  refine AEStronglyMeasurable.mul ?_ (Lp.aestronglyMeasurable _)
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop)))
    |>.aestronglyMeasurable

/-- On every line the weighted datum is the boundary inverse Fourier transform. -/
theorem hardyDatum_weight_ae {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ}
    (hσ : 0 < σ) :
    (fun x : ℝ => ((Real.exp (-(σ * x)) : ℝ) : ℂ) * hardyDatum F hF x)
      =ᵐ[volume] (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) := by
  filter_upwards [hardyPreimage_weight_ae_eq hF hσ one_pos] with x hx
  rw [hardyDatum, ← hx]
  have hmul : ((Real.exp (-(σ * x)) : ℝ) : ℂ) * ((Real.exp (σ * x) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  calc ((Real.exp (-(σ * x)) : ℝ) : ℂ)
        * (((Real.exp (σ * x) : ℝ) : ℂ) * (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) x)
      = (((Real.exp (-(σ * x)) : ℝ) : ℂ) * ((Real.exp (σ * x) : ℝ) : ℂ))
        * (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) x := by ring
    _ = (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) x := by rw [hmul, one_mul]

theorem memLp_two_weighted_hardyDatum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ}
    (hσ : 0 < σ) :
    MemLp (fun x : ℝ => ((Real.exp (-(σ * x)) : ℝ) : ℂ) * hardyDatum F hF x) 2 volume :=
  (Lp.memLp _).ae_eq (hardyDatum_weight_ae hF hσ).symm

/-- The mass of the weighted datum is the mass of the boundary values, hence at most `M`. -/
theorem integral_norm_sq_weighted_hardyDatum_le {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) {σ : ℝ} (hσ : 0 < σ) :
    (∫ x : ℝ, Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2) ≤ M := by
  have hmem := memLp_two_weighted_hardyDatum hF hσ
  have hnorm : ‖hmem.toLp _‖ ^ 2
      = ∫ x : ℝ, Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2 := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have hsq : Real.exp (-(σ * x)) ^ 2 = Real.exp (-(2 * σ * x)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
  have heq : hmem.toLp _ = hardyPreimage F σ (hF.memLp σ hσ) := by
    refine Lp.ext ?_
    exact (hmem.coeFn_toLp).trans (hardyDatum_weight_ae hF hσ)
  rw [← hnorm, heq, hardyPreimage]
  have hiso : ‖(𝓕⁻ ((hF.memLp σ hσ).toLp _) : Lp ℂ 2 (volume : Measure ℝ))‖
      = ‖((hF.memLp σ hσ).toLp _ : Lp ℂ 2 (volume : Measure ℝ))‖ :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
  rw [hiso, HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hcongr : (∫ ξ : ℝ, ‖(((hF.memLp σ hσ).toLp _ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2)
      = ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [(hF.memLp σ hσ).coeFn_toLp] with ξ hξ
    rw [hξ]
  rw [hcongr]
  exact hF.bound σ hσ

theorem norm_sq_weighted_hardyDatum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) (σ x : ℝ) :
    ‖((Real.exp (-(σ * x)) : ℝ) : ℂ) * hardyDatum F hF x‖ ^ 2
      = Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  have hsq : Real.exp (-(σ * x)) ^ 2 = Real.exp (-(2 * σ * x)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]

theorem integrable_weighted_norm_sq_hardyDatum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ => Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2) volume := by
  have hmem := memLp_two_weighted_hardyDatum hF hσ
  have h := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact norm_sq_weighted_hardyDatum hF σ x

theorem hardyDatum_bound_nonneg {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) : 0 ≤ M := by
  have h := hF.bound 1 one_pos
  have hnn : (0 : ℝ) ≤ ∫ ξ : ℝ, ‖F (rayLine 1 ξ)‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  linarith

/-- **The datum vanishes on the negative half-line.** -/
theorem hardyDatum_ae_zero_of_neg {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    ∀ᵐ x ∂(volume : Measure ℝ), x < 0 → hardyDatum F hF x = 0 := by
  have hM0 : 0 ≤ M := hardyDatum_bound_nonneg hF
  have hstep : ∀ δ : ℝ, 0 < δ →
      ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Iio (-δ) → hardyDatum F hF x = 0 := by
    intro δ hδ
    -- the mass on `Iio (-δ)` is dominated by `M e^{-2σδ}` for every `σ`
    have hdom : ∀ σ : ℝ, 0 < σ →
        IntegrableOn (fun x : ℝ => ‖hardyDatum F hF x‖ ^ 2) (Iio (-δ)) ∧
          (∫ x in Iio (-δ), ‖hardyDatum F hF x‖ ^ 2) ≤ M * Real.exp (-(2 * σ * δ)) := by
      intro σ hσ
      have hint := (integrable_weighted_norm_sq_hardyDatum hF hσ).integrableOn (s := Iio (-δ))
      have hcmp : ∀ x ∈ Iio (-δ), ‖hardyDatum F hF x‖ ^ 2
          ≤ Real.exp (-(2 * σ * δ)) * (Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2) := by
        intro x hx
        have hxδ : x < -δ := hx
        have hexp : (1 : ℝ) ≤ Real.exp (-(2 * σ * δ)) * Real.exp (-(2 * σ * x)) := by
          rw [← Real.exp_add]
          refine Real.one_le_exp ?_
          nlinarith
        nlinarith [sq_nonneg ‖hardyDatum F hF x‖, norm_nonneg (hardyDatum F hF x),
          Real.exp_pos (-(2 * σ * δ)), Real.exp_pos (-(2 * σ * x))]
      have hmaj : IntegrableOn (fun x : ℝ =>
          Real.exp (-(2 * σ * δ)) * (Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2))
          (Iio (-δ)) := hint.const_mul _
      have hintOn : IntegrableOn (fun x : ℝ => ‖hardyDatum F hF x‖ ^ 2) (Iio (-δ)) := by
        refine Integrable.mono' hmaj ?_ ?_
        · exact ((aestronglyMeasurable_hardyDatum hF).norm.pow 2).restrict
        · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hcmp x hx
      refine ⟨hintOn, ?_⟩
      have hle1 : (∫ x in Iio (-δ), ‖hardyDatum F hF x‖ ^ 2)
          ≤ ∫ x in Iio (-δ), Real.exp (-(2 * σ * δ))
              * (Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2) :=
        setIntegral_mono_on hintOn hmaj measurableSet_Iio hcmp
      have hle2 : (∫ x in Iio (-δ), Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2)
          ≤ ∫ x : ℝ, Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2 := by
        refine setIntegral_le_integral (integrable_weighted_norm_sq_hardyDatum hF hσ) ?_
        filter_upwards with x
        positivity
      rw [MeasureTheory.integral_const_mul] at hle1
      have hle3 := le_trans hle2 (integral_norm_sq_weighted_hardyDatum_le hF hσ)
      have hpos : (0 : ℝ) < Real.exp (-(2 * σ * δ)) := Real.exp_pos _
      nlinarith
    have hzero : (∫ x in Iio (-δ), ‖hardyDatum F hF x‖ ^ 2) = 0 := by
      have hnn : (0 : ℝ) ≤ ∫ x in Iio (-δ), ‖hardyDatum F hF x‖ ^ 2 :=
        integral_nonneg fun x => by positivity
      have hlim : Tendsto (fun σ : ℝ => M * Real.exp (-(2 * σ * δ))) atTop (𝓝 0) := by
        have hd : (0 : ℝ) < 2 * δ := by linarith
        have h4 : Tendsto (fun σ : ℝ => (2 * δ) * σ) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hd tendsto_id
        have h5 : Tendsto (fun σ : ℝ => -((2 * δ) * σ)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp h4
        have h2 : Tendsto (fun σ : ℝ => -(2 * σ * δ)) atTop atBot := by
          refine h5.congr fun σ => ?_
          ring
        have h1 : Tendsto (fun σ : ℝ => Real.exp (-(2 * σ * δ))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp h2
        simpa using h1.const_mul M
      have hle : (∫ x in Iio (-δ), ‖hardyDatum F hF x‖ ^ 2) ≤ 0 := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
        exact (hdom σ hσ).2
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => by positivity)
      ((hdom 1 one_pos).1)).1 hzero
    filter_upwards [(ae_restrict_iff' measurableSet_Iio).1 hae] with x hx hmem
    have h := hx hmem
    have : ‖hardyDatum F hF x‖ ^ 2 = 0 := h
    have hnorm : ‖hardyDatum F hF x‖ = 0 := by nlinarith [norm_nonneg (hardyDatum F hF x)]
    exact norm_eq_zero.1 hnorm
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      x ∈ Iio (-(1 / ((n : ℝ) + 1))) → hardyDatum F hF x = 0 := by
    refine ae_all_iff.2 fun n => hstep _ ?_
    positivity
  filter_upwards [hall] with x hx hx0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -x by linarith)
  refine hx n ?_
  simp only [Set.mem_Iio]
  linarith

/-- **The datum is square-integrable on the positive half-line.** -/
theorem memLp_two_hardyDatum {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) :
    MemLp (hardyDatum F hF) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeasG : AEStronglyMeasurable (hardyDatum F hF) (volume.restrict (Ioi (0 : ℝ))) :=
    (aestronglyMeasurable_hardyDatum hF).restrict
  set g : ℕ → ℝ → ENNReal := fun n x =>
    ENNReal.ofReal (Real.exp (-(2 * (1 / ((n : ℝ) + 1)) * x)) * ‖hardyDatum F hF x‖ ^ 2) with hg
  have hσn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    positivity
  have hgmeas : ∀ n : ℕ, AEMeasurable (g n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).aemeasurable).mul
      (((aestronglyMeasurable_hardyDatum hF).norm.pow 2).aemeasurable.restrict)
  have hlimptwise : ∀ x : ℝ, Tendsto (fun n : ℕ => g n x) atTop
      (𝓝 (ENNReal.ofReal (‖hardyDatum F hF x‖ ^ 2))) := by
    intro x
    have hn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hcont : Continuous fun σ : ℝ => Real.exp (-(2 * σ * x)) := by fun_prop
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(2 * (1 / ((n : ℝ) + 1)) * x))) atTop
        (𝓝 (Real.exp (-(2 * (0 : ℝ) * x)))) := (hcont.tendsto 0).comp hn
    have h0 : Real.exp (-(2 * (0 : ℝ) * x)) = 1 := by norm_num
    rw [h0] at h1
    have h2 : Tendsto (fun n : ℕ =>
        Real.exp (-(2 * (1 / ((n : ℝ) + 1)) * x)) * ‖hardyDatum F hF x‖ ^ 2) atTop
        (𝓝 (‖hardyDatum F hF x‖ ^ 2)) := by
      simpa using h1.mul_const (‖hardyDatum F hF x‖ ^ 2)
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hbound : ∀ n : ℕ, (∫⁻ x in Ioi (0 : ℝ), g n x) ≤ ENNReal.ofReal M := by
    intro n
    have hint := integrable_weighted_norm_sq_hardyDatum hF (hσn n)
    have hle : (∫⁻ x in Ioi (0 : ℝ), g n x)
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal
            (Real.exp (-(2 * (1 / ((n : ℝ) + 1)) * x)) * ‖hardyDatum F hF x‖ ^ 2) :=
      setLIntegral_le_lintegral _ _
    refine le_trans hle ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (integral_norm_sq_weighted_hardyDatum_le hF (hσn n))
  have hfatou := MeasureTheory.lintegral_liminf_le' (u := (atTop : Filter ℕ)) hgmeas
  have hliminf : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖hardyDatum F hF x‖ ^ 2))
      ≤ ENNReal.ofReal M := by
    have hcongr : (∫⁻ x in Ioi (0 : ℝ), Filter.liminf (fun n : ℕ => g n x) atTop)
        = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖hardyDatum F hF x‖ ^ 2) := by
      refine lintegral_congr fun x => ?_
      exact (hlimptwise x).liminf_eq
    rw [hcongr] at hfatou
    refine le_trans hfatou ?_
    exact Filter.liminf_le_of_frequently_le (f := (atTop : Filter ℕ))
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hbound))
  refine (memLp_two_iff_integrable_sq_norm hmeasG).2 ?_
  refine ⟨(hmeasG.norm.pow 2), ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => by positivity)]
  exact lt_of_le_of_lt hliminf ENNReal.ofReal_lt_top

/-- **Paley--Wiener for the Hardy space of a half-plane.**  Every Hardy function is the half-line
Laplace transform of its datum. -/
theorem isHalfPlaneHardy_eq_laplaceRay {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {w : ℂ}
    (hw : 0 < w.re) : F w = laplaceRay (hardyDatum F hF) w := by
  set d : ℝ → ℂ := hardyDatum F hF with hd
  have hdm : MemLp d 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_hardyDatum hF
  set σ : ℝ := w.re with hσdef
  have hσ : 0 < σ := hw
  -- the damped datum is the boundary inverse Fourier transform
  have hdamp : rayDamp d σ =ᵐ[volume] (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
      simpa using hx
    filter_upwards [hardyDatum_weight_ae hF hσ, hardyDatum_ae_zero_of_neg hF, hne]
      with x hx hx0 hxne
    by_cases hpos : x ∈ Ioi (0 : ℝ)
    · rw [rayDamp, Set.indicator_of_mem hpos, ← hx, expRay]
      have hexp : Complex.exp (-(((σ : ℝ) : ℂ) * (x : ℝ)))
          = ((Real.exp (-(σ * x)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    · rw [rayDamp, Set.indicator_of_notMem hpos, ← hx]
      have hxneg : x < 0 := by
        rcases lt_trichotomy x 0 with h | h | h
        · exact h
        · exact absurd h hxne
        · exact absurd (Set.mem_Ioi.2 h) hpos
      rw [hx0 hxneg, mul_zero]
  have hLp : (memLp_two_rayDamp hdm hσ.le).toLp (rayDamp d σ)
      = hardyPreimage F σ (hF.memLp σ hσ) :=
    Lp.ext (((memLp_two_rayDamp hdm hσ.le).coeFn_toLp).trans hdamp)
  have hfour : (fun ξ : ℝ => laplaceRay d (rayLine σ ξ)) =ᵐ[volume]
      fun ξ : ℝ => F (rayLine σ ξ) := by
    have h1 := coeFn_fourierTransform_rayDamp hdm hσ
    rw [hLp, fourier_hardyPreimage] at h1
    filter_upwards [h1.symm, (hF.memLp σ hσ).coeFn_toLp] with ξ hξ hξ'
    exact hξ.trans hξ'
  have hcont1 : Continuous fun ξ : ℝ => laplaceRay d (rayLine σ ξ) := by
    have hmap : Continuous fun ξ : ℝ => rayLine σ ξ := by
      unfold rayLine
      fun_prop
    refine (differentiableOn_laplaceRay hdm).continuousOn.comp_continuous hmap (fun ξ => ?_)
    simpa using hσ
  have hcont2 : Continuous fun ξ : ℝ => F (rayLine σ ξ) := by
    have hmap : Continuous fun ξ : ℝ => rayLine σ ξ := by
      unfold rayLine
      fun_prop
    refine hF.holo.continuousOn.comp_continuous hmap (fun ξ => ?_)
    simpa using hσ
  have heq : (fun ξ : ℝ => laplaceRay d (rayLine σ ξ)) = fun ξ : ℝ => F (rayLine σ ξ) :=
    (Continuous.ae_eq_iff_eq (volume : Measure ℝ) hcont1 hcont2).1 hfour
  have hpt := congrFun heq (w.im / (2 * Real.pi))
  have hline : rayLine σ (w.im / (2 * Real.pi)) = w := by
    rw [rayLine, hσdef]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hval : (2 * Real.pi * (w.im / (2 * Real.pi)) : ℝ) = w.im := by
      field_simp
    rw [hval]
    exact Complex.re_add_im w
  rw [hline] at hpt
  exact hpt.symm

end

end GaloisForLFunctions.HTGeometry
