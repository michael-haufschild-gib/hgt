import GaloisForLFunctions.RHTower.CCM.CCMFirstClockLandauDivisor
import GaloisForLFunctions.RHTower.LandauIntegralTransfer

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Published first-clock sign assertion, with no truncation or auxiliary hypothesis. -/
def CCMFirstClockPublishedSourceNonnegative : Prop :=
  ∀ L : ℝ, Real.pi / 2 ≤ L →
    0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)

theorem ccmFirstClockXiRationalDivisor_re_nonneg_of_publishedSource
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ (ccmFirstClockXiRationalDivisor L).re := by
  have h := hsource L hL
  rw [ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor hL] at h
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  nlinarith [h, (show 0 < 2 / L by positivity)]

/-- Real positive tail density obtained by centering the CCM carrier at Laplace abscissa `r`. -/
def ccmFirstClockLandauDensity (r L : ℝ) : ℝ :=
  Real.exp (-r * L) * (ccmFirstClockXiRationalDivisor L).re

theorem measurable_ccmFirstClockLandauDensity (r : ℝ) :
    Measurable (ccmFirstClockLandauDensity r) := by
  unfold ccmFirstClockLandauDensity
  exact (by fun_prop : Measurable (fun L : ℝ => Real.exp (-r * L))).mul
    measurable_ccmFirstClockXiRationalDivisor.re

theorem integrableOn_ccmFirstClockLandauDensity
    {r : ℝ} (hr : 1 / 2 < r) :
    IntegrableOn (ccmFirstClockLandauDensity r) (Ioi (Real.pi / 2)) := by
  have hcomplex :=
    integrableOn_exp_mul_ccmFirstClockXiRationalDivisor
      (s := (r : ℂ)) (by simpa using hr)
  have hre : IntegrableOn
      (fun L : ℝ =>
        (Complex.exp (-(r : ℂ) * (L : ℂ)) *
          ccmFirstClockXiRationalDivisor L).re) (Ioi 0) :=
    hcomplex.re
  have hre' := hre.mono_set (show Ioi (Real.pi / 2) ⊆ Ioi 0 by
    intro L hL
    exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
  apply hre'.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  unfold ccmFirstClockLandauDensity
  have hQim := ccmFirstClockXiRationalDivisor_im_eq_zero L
  have hQcast :
      ccmFirstClockXiRationalDivisor L =
        ((ccmFirstClockXiRationalDivisor L).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hQim]
  rw [hQcast]
  rw [show -(r : ℂ) * (L : ℂ) = ((-r * L : ℝ) : ℂ) by
    push_cast
    ring]
  simp
  left
  rw [Complex.exp_re]
  simp [mul_re]

/-- Positive measure used by Landau's theorem after deleting the compact unsigned head. -/
def ccmFirstClockLandauMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (Real.pi / 2))).withDensity
    (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))

theorem ccmFirstClockLandauDensity_nonneg_ae
    (hsource : CCMFirstClockPublishedSourceNonnegative) (r : ℝ) :
    ∀ᵐ L ∂volume.restrict (Ioi (Real.pi / 2)),
      0 ≤ ccmFirstClockLandauDensity r L := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  exact mul_nonneg (Real.exp_pos _).le
    (ccmFirstClockXiRationalDivisor_re_nonneg_of_publishedSource
      hsource hL.le)

/-- Compact unsigned head removed from the literal first-clock transform. -/
def ccmFirstClockHeadLaplace (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioc (0 : ℝ) (Real.pi / 2),
    Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L

private theorem integrableOn_ccmFirstClockXiRationalDivisor_head :
    IntegrableOn ccmFirstClockXiRationalDivisor
      (Ioc (0 : ℝ) (Real.pi / 2)) := by
  let M : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let C : ℝ :=
    (ccmFirstClockHeadReciprocalSquareConstant +
      (1 + 2 * Real.pi) * (Real.exp (Real.pi / 4) + 1)) * M
  have hC0 : 0 ≤ C := by
    have hmass : 0 ≤ M := by
      dsimp only [M]
      exact tsum_nonneg fun _ => by positivity
    dsimp only [C]
    apply mul_nonneg
    · exact add_nonneg ccmFirstClockHeadReciprocalSquareConstant_nonneg
        (mul_nonneg (by positivity) (by positivity))
    · exact hmass
  have hconst : IntegrableOn (fun _ : ℝ => C)
      (Ioc (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  refine Integrable.mono' (f := ccmFirstClockXiRationalDivisor)
    hconst
    measurable_ccmFirstClockXiRationalDivisor.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
  have hQ := norm_ccmFirstClockXiRationalDivisor_le hL.1.le
  dsimp only [C, M]
  calc
    ‖ccmFirstClockXiRationalDivisor L‖ ≤
        (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := hQ
    _ ≤ (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (Real.pi / 4) + 1)) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
      have hmass : 0 ≤
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
        tsum_nonneg fun _ => by positivity
      apply mul_le_mul_of_nonneg_right _ hmass
      have hexpLe :
          Real.exp (L / 2) ≤ Real.exp (Real.pi / 4) :=
        Real.exp_le_exp.mpr (by nlinarith [hL.2])
      have hinner :
          Real.exp (L / 2) + 1 ≤ Real.exp (Real.pi / 4) + 1 :=
        add_le_add hexpLe (le_refl 1)
      have hmul :
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1) ≤
            (1 + 2 * Real.pi) * (Real.exp (Real.pi / 4) + 1) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      exact add_le_add
        (le_refl ccmFirstClockHeadReciprocalSquareConstant) hmul

/-- Compact head Laplace correction is entire. -/
theorem differentiable_ccmFirstClockHeadLaplace :
    Differentiable ℂ ccmFirstClockHeadLaplace := by
  intro s₀
  let A : ℝ := Real.pi / 2
  let F : ℂ → ℝ → ℂ := fun s L =>
    Complex.exp (-s * (L : ℂ)) * ccmFirstClockXiRationalDivisor L
  let F' : ℂ → ℝ → ℂ := fun s L =>
    (-(L : ℂ)) * Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L
  let bound : ℝ → ℝ := fun L =>
    A * Real.exp ((|s₀.re| + 1) * A) *
      ‖ccmFirstClockXiRationalDivisor L‖
  have hA : 0 < A := by dsimp only [A]; positivity
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hFmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (F s)
        (volume.restrict (Ioc (0 : ℝ) A)) := by
    filter_upwards with s
    exact ((by fun_prop : Measurable (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)))).aestronglyMeasurable.mul
        measurable_ccmFirstClockXiRationalDivisor.aestronglyMeasurable).restrict
  have hFint : Integrable (F s₀)
      (volume.restrict (Ioc (0 : ℝ) A)) := by
    have hQ : Integrable ccmFirstClockXiRationalDivisor
        (volume.restrict (Ioc (0 : ℝ) A)) := by
      simpa only [MeasureTheory.IntegrableOn, A] using
        integrableOn_ccmFirstClockXiRationalDivisor_head
    have hboundExp : Filter.Eventually
        (fun L : ℝ => ‖Complex.exp (-s₀ * (L : ℂ))‖ ≤
          Real.exp (|s₀.re| * A))
        (ae (volume.restrict (Ioc (0 : ℝ) A))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      rw [Complex.norm_exp]
      have hre : (-s₀ * (L : ℂ)).re = -s₀.re * L := by simp [mul_re]
      rw [hre]
      apply Real.exp_le_exp.mpr
      have hL0 : 0 ≤ L := hL.1.le
      have hLA : L ≤ A := hL.2
      have hs := neg_le_abs s₀.re
      exact (mul_le_mul_of_nonneg_right hs hL0).trans
        (mul_le_mul_of_nonneg_left hLA (abs_nonneg s₀.re))
    apply Integrable.mono' (hQ.norm.const_mul (Real.exp (|s₀.re| * A)))
    · exact ((by fun_prop : Measurable (fun L : ℝ =>
        Complex.exp (-s₀ * (L : ℂ)))).aestronglyMeasurable.mul
          measurable_ccmFirstClockXiRationalDivisor.aestronglyMeasurable).restrict
    · filter_upwards [hboundExp] with L hL
      dsimp only [F]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hL
        (norm_nonneg (ccmFirstClockXiRationalDivisor L))
  have hF'meas : AEStronglyMeasurable (F' s₀)
      (volume.restrict (Ioc (0 : ℝ) A)) := by
    exact ((by fun_prop : Measurable (fun L : ℝ =>
      (-(L : ℂ)) * Complex.exp (-s₀ * (L : ℂ)))).aestronglyMeasurable.mul
        measurable_ccmFirstClockXiRationalDivisor.aestronglyMeasurable).restrict
  have hboundInt : Integrable bound
      (volume.restrict (Ioc (0 : ℝ) A)) := by
    have hQ : Integrable ccmFirstClockXiRationalDivisor
        (volume.restrict (Ioc (0 : ℝ) A)) := by
      simpa only [MeasureTheory.IntegrableOn, A] using
        integrableOn_ccmFirstClockXiRationalDivisor_head
    exact hQ.norm.const_mul _
  have hbound : ∀ᵐ L ∂volume.restrict (Ioc (0 : ℝ) A),
      ∀ s ∈ Metric.ball s₀ 1, ‖F' s L‖ ≤ bound L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    intro s hs
    have hdist : ‖s - s₀‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hreDiff : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
    have hsre : -s.re ≤ |s₀.re| + 1 := by
      linarith [neg_le_abs s₀.re, neg_le_abs (s.re - s₀.re)]
    have hL0 : 0 ≤ L := hL.1.le
    have hLA : L ≤ A := hL.2
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real, Complex.norm_exp,
      Real.norm_eq_abs, abs_of_nonneg hL0]
    have hre : (-s * (L : ℂ)).re = -s.re * L := by simp [mul_re]
    rw [hre]
    gcongr
  have hdiff : ∀ᵐ L ∂volume.restrict (Ioc (0 : ℝ) A),
      ∀ s ∈ Metric.ball s₀ 1,
        HasDerivAt (fun s => F s L) (F' s L) s := by
    filter_upwards with L
    intro s hs
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (L : ℂ)))
        (-(L : ℂ) * Complex.exp (-s * (L : ℂ))) s := by
      simpa [mul_comm] using
        (((hasDerivAt_id s).neg.mul_const (L : ℂ)).cexp)
    simpa only [F, F', mul_assoc] using
      hexp.mul_const (ccmFirstClockXiRationalDivisor L)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) A)) (F := F) (F' := F')
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := bound)
    hball hFmeas hFint hF'meas hbound hboundInt hdiff
  have hdiffAt := hmain.2.differentiableAt
  exact hdiffAt

/-- Holomorphic continuation of the positive physical tail, obtained by deleting the compact
unsigned head from the complete first-clock continuation. -/
def ccmFirstClockTailContinuation (s : ℂ) : ℂ :=
  ccmFirstClockLaplaceContinuation s - ccmFirstClockHeadLaplace s

theorem integral_tail_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    (∫ L : ℝ in Ioi (Real.pi / 2),
      Complex.exp (-s * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L) =
      ccmFirstClockTailContinuation s := by
  let f : ℝ → ℂ := fun L =>
    Complex.exp (-s * (L : ℂ)) * ccmFirstClockXiRationalDivisor L
  have hfull : IntegrableOn f (Ioi 0) :=
    integrableOn_exp_mul_ccmFirstClockXiRationalDivisor hsHalf
  have hA0 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hhead : IntegrableOn f (Ioc 0 (Real.pi / 2)) :=
    hfull.mono_set (by
      intro L hL
      exact hL.1)
  have htail : IntegrableOn f (Ioi (Real.pi / 2)) :=
    hfull.mono_set (by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.pi / 2))
      (Ioi (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro L hheadL htailL
    exact (not_lt_of_ge hheadL.2) htailL
  have hsplit := setIntegral_union₀ hdisj.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hhead htail
  rw [Set.Ioc_union_Ioi_eq_Ioi hA0] at hsplit
  have hfullEq :=
    integral_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation hsHalf
  dsimp only [f] at hsplit
  unfold ccmFirstClockTailContinuation ccmFirstClockHeadLaplace
  rw [← hfullEq, hsplit]
  ring

/-- The complex MGF of the positive first-clock tail measure is exactly the translated
holomorphic tail continuation near its centering point. -/
theorem complexMGF_id_ccmFirstClockLandauMeasure_eq_tailContinuation
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r : ℝ} (hr : 1 / 2 < r) {z : ℂ}
    (hz : 1 / 2 < r - z.re) :
    complexMGF id (ccmFirstClockLandauMeasure r) z =
      ccmFirstClockTailContinuation ((r : ℂ) - z) := by
  have hdensInt := integrableOn_ccmFirstClockLandauDensity hr
  have hmeas : AEMeasurable
      (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))
      (volume.restrict (Ioi (Real.pi / 2))) :=
    (measurable_ccmFirstClockLandauDensity r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg :=
    ccmFirstClockLandauDensity_nonneg_ae hsource r
  rw [complexMGF, ccmFirstClockLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_tail_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation
    (s := (r : ℂ) - z) (by simpa using hz)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with L hL hden
  rw [ENNReal.toReal_ofReal hden]
  have hQim := ccmFirstClockXiRationalDivisor_im_eq_zero L
  have hQcast :
      ccmFirstClockXiRationalDivisor L =
        ((ccmFirstClockXiRationalDivisor L).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hQim]
  unfold ccmFirstClockLandauDensity
  rw [hQcast]
  rw [Complex.real_smul]
  push_cast
  simp only [id_eq, Complex.ofReal_re]
  rw [show
      Complex.exp (-(r : ℂ) * (L : ℂ)) *
          ((ccmFirstClockXiRationalDivisor L).re : ℂ) *
          Complex.exp (z * (L : ℂ)) =
        (Complex.exp (-(r : ℂ) * (L : ℂ)) *
          Complex.exp (z * (L : ℂ))) *
          ((ccmFirstClockXiRationalDivisor L).re : ℂ) by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

end

end RHTower
