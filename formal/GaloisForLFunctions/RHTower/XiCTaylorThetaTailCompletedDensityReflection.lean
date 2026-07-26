import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberGlobalReflection
import GaloisForLFunctions.RHTower.ThetaCuspInversionBoundaryValue
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhasePotentialSeam

/-!
# Holomorphic two-sided reflection of the completed theta density

The positive-half-line density transform has a growing channel when the spectral argument is
reflected.  Keeping both channels jointly and retaining the endpoint in two integrations by parts
produces an exact identity on the full open Fourier--Laplace strip.  This is an infinite-source
reflection relation: it is not a sign assertion and does not use Xi divisor data.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

def thetaCuspTailSecondDensityEvenPhase (z : ℂ) (x : ℝ) : ℂ :=
  spectralTranslationPhase x z + spectralTranslationPhase x (-z)

def thetaCuspTailSecondDensityEvenPhaseDerivative (z : ℂ) (x : ℝ) : ℂ :=
  I * z *
    (spectralTranslationPhase x z - spectralTranslationPhase x (-z))

def thetaCuspTailSecondDensityEvenPhaseSecondDerivative (z : ℂ) (x : ℝ) : ℂ :=
  -(z ^ 2) * thetaCuspTailSecondDensityEvenPhase z x

theorem hasDerivAt_thetaCuspTailSecondDensityEvenPhase (z : ℂ) (x : ℝ) :
    HasDerivAt (thetaCuspTailSecondDensityEvenPhase z) (thetaCuspTailSecondDensityEvenPhaseDerivative z x) x := by
  have hp := hasDerivAt_spectralTranslationPhase_source z x
  have hn := hasDerivAt_spectralTranslationPhase_source (-z) x
  convert hp.add hn using 1 <;>
    simp [thetaCuspTailSecondDensityEvenPhase, thetaCuspTailSecondDensityEvenPhaseDerivative] <;> ring

theorem hasDerivAt_thetaCuspTailSecondDensityEvenPhaseDerivative (z : ℂ) (x : ℝ) :
    HasDerivAt (thetaCuspTailSecondDensityEvenPhaseDerivative z)
      (thetaCuspTailSecondDensityEvenPhaseSecondDerivative z x) x := by
  have hp := hasDerivAt_spectralTranslationPhase_sourceDerivative z x
  have hn := hasDerivAt_spectralTranslationPhase_sourceDerivative (-z) x
  have h := hp.add hn
  convert h using 1
  · funext u
    simp [thetaCuspTailSecondDensityEvenPhaseDerivative]
    ring
  · simp [thetaCuspTailSecondDensityEvenPhase, thetaCuspTailSecondDensityEvenPhaseSecondDerivative]
    ring

theorem integrableOn_evenPhase_mul_thetaCuspTailDerivative
    (m : ℕ) {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspTailSecondDensityEvenPhase z x * (thetaCuspTailDerivative m x : ℂ)) (Ioi 0) := by
  have hplus : IntegrableOn (fun x : ℝ =>
      spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ))
      (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ =>
        (thetaCuspTailDerivative m x : ℂ)) (Ioi 0) :=
      (integrableOn_thetaCuspTailDerivative_Ioi m).ofReal
    apply hbase.bdd_mul (c := 1)
    · exact (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_spectralTranslationPhase_source z x).continuousAt
          ).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_spectralTranslationPhase_le_one hx.le hz0
  have hminus : IntegrableOn (fun x : ℝ =>
      spectralTranslationPhase x (-z) * (thetaCuspTailDerivative m x : ℂ))
      (Ioi 0) := by
    let C := thetaCuspTailDerivativeExpConstant m
    have hrate : -(1 - z.im) < 0 := by linarith
    have hdom : IntegrableOn (fun x : ℝ =>
        C * Real.exp (-(1 - z.im) * x)) (Ioi 0) := by
      exact (integrableOn_exp_mul_Ioi hrate 0).const_mul C
    change Integrable (fun x : ℝ =>
      spectralTranslationPhase x (-z) *
        (thetaCuspTailDerivative m x : ℂ))
      (volume.restrict (Ioi 0))
    change Integrable (fun x : ℝ =>
      C * Real.exp (-(1 - z.im) * x))
      (volume.restrict (Ioi 0)) at hdom
    apply Integrable.mono hdom
    · have hpcont : Continuous (fun x : ℝ =>
          spectralTranslationPhase x (-z)) :=
        continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_spectralTranslationPhase_source (-z) x).continuousAt
      have htcont : Continuous (fun x : ℝ =>
          (thetaCuspTailDerivative m x : ℂ)) :=
        Complex.continuous_ofReal.comp
          (differentiable_thetaCuspTailDerivative m).continuous
      exact (hpcont.mul htcont).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have htail := abs_thetaCuspTailDerivative_le_exp_neg m hx.le
      have hphase : ‖spectralTranslationPhase x (-z)‖ =
          Real.exp (x * z.im) := by
        unfold spectralTranslationPhase
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      rw [norm_mul, hphase, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (thetaCuspTailDerivativeExpConstant_nonneg m) (Real.exp_pos _).le)]
      change Real.exp (x * z.im) * |thetaCuspTailDerivative m x| ≤
        C * Real.exp (-(1 - z.im) * x)
      change |thetaCuspTailDerivative m x| ≤ C * Real.exp (-x) at htail
      calc
        Real.exp (x * z.im) * |thetaCuspTailDerivative m x| ≤
            Real.exp (x * z.im) * (C * Real.exp (-x)) := by gcongr
        _ = C * Real.exp (-(1 - z.im) * x) := by
          rw [show Real.exp (x * z.im) * (C * Real.exp (-x)) =
              C * (Real.exp (x * z.im) * Real.exp (-x)) by ring,
            ← Real.exp_add]
          congr 2
          ring
  rw [show (fun x : ℝ =>
      thetaCuspTailSecondDensityEvenPhase z x * (thetaCuspTailDerivative m x : ℂ)) =
      fun x : ℝ =>
        spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ) +
          spectralTranslationPhase x (-z) *
            (thetaCuspTailDerivative m x : ℂ) by
      funext x
      unfold thetaCuspTailSecondDensityEvenPhase
      ring]
  exact hplus.add hminus

theorem tendsto_evenPhase_mul_thetaCuspTailDerivative
    (m : ℕ) {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    Tendsto (fun x : ℝ =>
      thetaCuspTailSecondDensityEvenPhase z x * (thetaCuspTailDerivative m x : ℂ))
      atTop (nhds 0) := by
  have hplus : Tendsto (fun x : ℝ =>
      spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖spectralTranslationPhase x z *
          (thetaCuspTailDerivative m x : ℂ)‖ ≤
        ‖thetaCuspTailDerivative m x‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_spectralTranslationPhase_le_one hx hz0)
    exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      hle (by simpa using (thetaCuspTailDerivative_tendsto_atTop_zero m).norm)
  have hminus : Tendsto (fun x : ℝ =>
      spectralTranslationPhase x (-z) * (thetaCuspTailDerivative m x : ℂ))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let C := thetaCuspTailDerivativeExpConstant m
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖spectralTranslationPhase x (-z) *
          (thetaCuspTailDerivative m x : ℂ)‖ ≤
        C * Real.exp (-(1 - z.im) * x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have htail := abs_thetaCuspTailDerivative_le_exp_neg m hx
      change |thetaCuspTailDerivative m x| ≤ C * Real.exp (-x) at htail
      have hphase : ‖spectralTranslationPhase x (-z)‖ =
          Real.exp (x * z.im) := by
        unfold spectralTranslationPhase
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      rw [norm_mul, hphase, Complex.norm_real, Real.norm_eq_abs]
      calc
        Real.exp (x * z.im) * |thetaCuspTailDerivative m x| ≤
            Real.exp (x * z.im) * (C * Real.exp (-x)) := by gcongr
        _ = C * Real.exp (-(1 - z.im) * x) := by
          rw [show Real.exp (x * z.im) * (C * Real.exp (-x)) =
              C * (Real.exp (x * z.im) * Real.exp (-x)) by ring,
            ← Real.exp_add]
          congr 2
          ring
    have hmajor : Tendsto (fun x : ℝ =>
        C * Real.exp (-(1 - z.im) * x)) atTop (nhds 0) := by
      have hrate : -(1 - z.im) < 0 := by linarith
      have hexp : Tendsto (fun x : ℝ =>
          Real.exp (-(1 - z.im) * x)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg hrate)
      simpa using hexp.const_mul C
    exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor
  rw [show (fun x : ℝ =>
      thetaCuspTailSecondDensityEvenPhase z x * (thetaCuspTailDerivative m x : ℂ)) =
      fun x : ℝ =>
        spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ) +
          spectralTranslationPhase x (-z) *
            (thetaCuspTailDerivative m x : ℂ) by
      funext x
      unfold thetaCuspTailSecondDensityEvenPhase
      ring]
  simpa using hplus.add hminus

theorem integral_tail_second_mul_evenPhase_eq_boundary_sub_sq_tail
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) =
      1 / 2 - z ^ 2 * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 0 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x := by
  let f : ℝ → ℂ := fun x => (thetaCuspTailDerivative 0 x : ℂ)
  let f' : ℝ → ℂ := fun x => (thetaCuspTailDerivative 1 x : ℂ)
  let f'' : ℝ → ℂ := fun x => (thetaCuspTailDerivative 2 x : ℂ)
  let g : ℝ → ℂ := thetaCuspTailSecondDensityEvenPhase z
  let g' : ℝ → ℂ := thetaCuspTailSecondDensityEvenPhaseDerivative z
  let g'' : ℝ → ℂ := thetaCuspTailSecondDensityEvenPhaseSecondDerivative z
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    exact (hasDerivAt_thetaCuspTailDerivative 0 x).ofReal_comp
  have hf' (x : ℝ) : HasDerivAt f' (f'' x) x := by
    exact (hasDerivAt_thetaCuspTailDerivative 1 x).ofReal_comp
  have hg (x : ℝ) : HasDerivAt g (g' x) x :=
    hasDerivAt_thetaCuspTailSecondDensityEvenPhase z x
  have hg' (x : ℝ) : HasDerivAt g' (g'' x) x :=
    hasDerivAt_thetaCuspTailSecondDensityEvenPhaseDerivative z x
  have hplusInt (m : ℕ) : IntegrableOn (fun x : ℝ =>
      spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ))
      (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ =>
        (thetaCuspTailDerivative m x : ℂ)) (Ioi 0) :=
      (integrableOn_thetaCuspTailDerivative_Ioi m).ofReal
    apply hbase.bdd_mul (c := 1)
    · exact (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_spectralTranslationPhase_source z x).continuousAt
          ).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_spectralTranslationPhase_le_one hx.le hz0
  have hoddInt (m : ℕ) : IntegrableOn (fun x : ℝ =>
      (spectralTranslationPhase x z - spectralTranslationPhase x (-z)) *
        (thetaCuspTailDerivative m x : ℂ)) (Ioi 0) := by
    have htwoPlus := (hplusInt m).const_mul (2 : ℂ)
    have heven := integrableOn_evenPhase_mul_thetaCuspTailDerivative m hz0 hz1
    refine (htwoPlus.sub heven).congr ?_
    filter_upwards with x
    unfold thetaCuspTailSecondDensityEvenPhase
    dsimp
    ring
  have hgf'' : IntegrableOn (g * f'') (Ioi 0) := by
    simpa [g, f''] using integrableOn_evenPhase_mul_thetaCuspTailDerivative 2 hz0 hz1
  have hg'f' : IntegrableOn (g' * f') (Ioi 0) := by
    have h := (hoddInt 1).const_mul (I * z)
    refine h.congr ?_
    filter_upwards with x
    simp [g', f', thetaCuspTailSecondDensityEvenPhaseDerivative]
    ring
  have hg''f : IntegrableOn (g'' * f) (Ioi 0) := by
    have h := (integrableOn_evenPhase_mul_thetaCuspTailDerivative 0 hz0 hz1).const_mul (-(z ^ 2))
    refine h.congr ?_
    filter_upwards with x
    simp [g'', f, thetaCuspTailSecondDensityEvenPhaseSecondDerivative]
    ring
  have hplusTend (m : ℕ) : Tendsto (fun x : ℝ =>
      spectralTranslationPhase x z * (thetaCuspTailDerivative m x : ℂ))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖spectralTranslationPhase x z *
          (thetaCuspTailDerivative m x : ℂ)‖ ≤
        ‖thetaCuspTailDerivative m x‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_spectralTranslationPhase_le_one hx hz0)
    exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      hle (by simpa using (thetaCuspTailDerivative_tendsto_atTop_zero m).norm)
  have hoddTend (m : ℕ) : Tendsto (fun x : ℝ =>
      (spectralTranslationPhase x z - spectralTranslationPhase x (-z)) *
        (thetaCuspTailDerivative m x : ℂ)) atTop (nhds 0) := by
    have h := (hplusTend m).const_mul (2 : ℂ) |>.sub
      (tendsto_evenPhase_mul_thetaCuspTailDerivative m hz0 hz1)
    have h0 : Tendsto (fun x : ℝ =>
        2 * (spectralTranslationPhase x z *
          (thetaCuspTailDerivative m x : ℂ)) -
          thetaCuspTailSecondDensityEvenPhase z x * (thetaCuspTailDerivative m x : ℂ))
        atTop (nhds 0) := by simpa using h
    apply h0.congr'
    filter_upwards with x
    unfold thetaCuspTailSecondDensityEvenPhase
    ring
  have hzero1 : Tendsto (g * f') (nhdsWithin 0 (Ioi 0))
      (nhds (g 0 * f' 0)) := by
    exact ((hg 0).continuousAt.mul (hf' 0).continuousAt).tendsto.mono_left
      inf_le_left
  have hzero2 : Tendsto (g' * f) (nhdsWithin 0 (Ioi 0))
      (nhds (g' 0 * f 0)) := by
    exact ((hg' 0).continuousAt.mul (hf 0).continuousAt).tendsto.mono_left
      inf_le_left
  have hinfty1 : Tendsto (g * f') atTop (nhds 0) := by
    simpa [g, f'] using tendsto_evenPhase_mul_thetaCuspTailDerivative 1 hz0 hz1
  have hinfty2 : Tendsto (g' * f) atTop (nhds 0) := by
    have h := (hoddTend 0).const_mul (I * z)
    have h0 : Tendsto (fun x : ℝ => (I * z) *
        ((spectralTranslationPhase x z - spectralTranslationPhase x (-z)) *
          (thetaCuspTailDerivative 0 x : ℂ))) atTop (nhds 0) := by
      simpa using h
    apply h0.congr'
    filter_upwards with x
    simp [g', f, thetaCuspTailSecondDensityEvenPhaseDerivative]
    ring
  have h := integral_Ioi_secondDerivative_mul_eq_boundary_add
    (a := (0 : ℝ)) (f := f) (f' := f') (f'' := f'')
    (g := g) (g' := g') (g'' := g'')
    (A₁ := g 0 * f' 0) (B₁ := 0) (A₂ := g' 0 * f 0) (B₂ := 0)
    (fun x _ => hf x) (fun x _ => hf' x) (fun x _ => hg x) (fun x _ => hg' x)
    hgf'' hg'f' hg''f hzero1 hinfty1 hzero2 hinfty2
  dsimp [f, f', f'', g, g', g'', thetaCuspTailSecondDensityEvenPhase,
    thetaCuspTailSecondDensityEvenPhaseDerivative, thetaCuspTailSecondDensityEvenPhaseSecondDerivative] at h ⊢
  rw [show (fun x : ℝ =>
      (thetaCuspTailDerivative 0 x : ℂ) *
        (-(z ^ 2) *
          (spectralTranslationPhase x z + spectralTranslationPhase x (-z)))) =
      fun x : ℝ => -(z ^ 2) *
        ((thetaCuspTailDerivative 0 x : ℂ) *
          (spectralTranslationPhase x z + spectralTranslationPhase x (-z))) by
        funext x
        ring,
    integral_const_mul] at h
  have hp0 : spectralTranslationPhase 0 z = 1 := by
    simp [spectralTranslationPhase]
  have hm0 : spectralTranslationPhase 0 (-z) = 1 := by
    simp [spectralTranslationPhase]
  rw [hp0, hm0, thetaCuspTailDerivative_one_zero] at h
  rw [show (fun x : ℝ =>
      (thetaCuspTailDerivative 0 x : ℂ) *
        (spectralTranslationPhase x z + spectralTranslationPhase x (-z))) =
      fun x : ℝ =>
        (thetaCuspTailDerivative 0 x : ℂ) * spectralTranslationPhase x z +
          (thetaCuspTailDerivative 0 x : ℂ) * spectralTranslationPhase x (-z) by
        funext x
        ring] at h
  norm_num at h
  convert h using 1 <;> ring

theorem integral_fullSource_mul_evenPhase_eq_XiC
    {z : ℂ} (hz : |z.im| < 1) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) = XiC z := by
  have hint := integrable_thetaCuspFourierLaplaceIntegrand hz
  have hsplit := integral_eq_integral_Ioi_add_reflect hint
  have hzmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hz
  have hXi := thetaCuspFourierLaplace_eq_XiC_on_strip hzmem
  rw [← thetaCuspFourierLaplace, hXi] at hsplit
  rw [hsplit]
  apply integral_congr_ae
  filter_upwards with x
  unfold thetaCuspFourierLaplaceIntegrand thetaCuspTailSecondDensityEvenPhase spectralTranslationPhase
  rw [thetaCuspFullSource_neg]
  congr 1
  push_cast
  ring

theorem thetaCuspTailSecondDensityPhaseValue_add_neg_eq_four_integral_tail_second
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    thetaCuspTailSecondDensityPhaseValue z +
        thetaCuspTailSecondDensityPhaseValue (-z) =
      4 * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x := by
  have hplus := integrableOn_thetaCuspTailSecondDensity_mul_phase hz0
  have heven : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) (Ioi 0) := by
    have h := (integrableOn_evenPhase_mul_thetaCuspTailDerivative 2 hz0 hz1).const_mul (4 : ℂ)
    refine h.congr ?_
    filter_upwards with x
    unfold thetaCuspTailSecondDensity
    push_cast
    ring
  have hminus : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        spectralTranslationPhase x (-z)) (Ioi 0) := by
    have h := heven.sub hplus
    refine h.congr ?_
    filter_upwards with x
    change (thetaCuspTailSecondDensity x : ℂ) *
          (spectralTranslationPhase x z + spectralTranslationPhase x (-z)) -
        (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z =
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x (-z)
    ring
  unfold thetaCuspTailSecondDensityPhaseValue
  rw [← integral_add hplus hminus]
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z +
        (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x (-z)) =
      fun x : ℝ => 4 *
        ((thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) by
      funext x
      unfold thetaCuspTailSecondDensity thetaCuspTailSecondDensityEvenPhase
      push_cast
      ring,
    integral_const_mul]

theorem XiC_eq_integral_tail_second_sub_quarter_tail
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    XiC z =
      (∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) -
      (1 / 4 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 0 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x := by
  have habs : |z.im| < 1 := by
    rw [abs_of_nonneg hz0]
    exact hz1
  have h := integral_fullSource_mul_evenPhase_eq_XiC habs
  have htwo : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_evenPhase_mul_thetaCuspTailDerivative 2 hz0 hz1
  have hzero : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailDerivative 0 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_evenPhase_mul_thetaCuspTailDerivative 0 hz0 hz1
  rw [show (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) =
      fun x : ℝ =>
        (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x -
          (1 / 4 : ℂ) *
            ((thetaCuspTailDerivative 0 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x) by
      funext x
      rw [thetaCuspFullSource_eq_tail_second_sub]
      push_cast
      ring,
    integral_sub htwo (hzero.const_mul (1 / 4 : ℂ)),
    integral_const_mul] at h
  exact h.symm

/-- Holomorphic two-sided completion relation for the exact canonical density on the upper half of
the theta Fourier--Laplace strip.  Unlike the real-boundary relation, this retains both one-sided
phase values and therefore couples the growing and decaying spectral channels exactly. -/
theorem thetaCuspTailSecondDensityPhaseValue_twoSided_crossed_upper
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im < 1) :
    (z ^ 2 + 1 / 4) *
        (thetaCuspTailSecondDensityPhaseValue z +
          thetaCuspTailSecondDensityPhaseValue (-z)) =
      1 / 2 + 4 * z ^ 2 * XiC z := by
  let A : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailDerivative 0 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x
  let B : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailDerivative 2 x : ℂ) * thetaCuspTailSecondDensityEvenPhase z x
  let R : ℂ := thetaCuspTailSecondDensityPhaseValue z +
    thetaCuspTailSecondDensityPhaseValue (-z)
  let X : ℂ := XiC z
  have hB : B = 1 / 2 - z ^ 2 * A := by
    dsimp only [B, A]
    exact integral_tail_second_mul_evenPhase_eq_boundary_sub_sq_tail hz0 hz1
  have hR : R = 4 * B := by
    dsimp only [R, B]
    exact thetaCuspTailSecondDensityPhaseValue_add_neg_eq_four_integral_tail_second hz0 hz1
  have hX : X = B - (1 / 4 : ℂ) * A := by
    dsimp only [X, B, A]
    exact XiC_eq_integral_tail_second_sub_quarter_tail hz0 hz1
  dsimp only [R, X] at hR hX ⊢
  linear_combination (z ^ 2 + 1 / 4) * hR - 4 * z ^ 2 * hX + hB

/-- The two-sided completion relation throughout the full open theta Fourier--Laplace strip. -/
theorem thetaCuspTailSecondDensityPhaseValue_twoSided_crossed
    {z : ℂ} (hz : |z.im| < 1) :
    (z ^ 2 + 1 / 4) *
        (thetaCuspTailSecondDensityPhaseValue z +
          thetaCuspTailSecondDensityPhaseValue (-z)) =
      1 / 2 + 4 * z ^ 2 * XiC z := by
  by_cases hz0 : 0 ≤ z.im
  · exact thetaCuspTailSecondDensityPhaseValue_twoSided_crossed_upper
      hz0 (by simpa [abs_of_nonneg hz0] using hz)
  · have hneg0 : 0 ≤ (-z).im := by
      simp only [neg_im]
      linarith
    have hneg1 : (-z).im < 1 := by
      have hlower := (abs_lt.mp hz).1
      simp only [neg_im]
      linarith
    have h := thetaCuspTailSecondDensityPhaseValue_twoSided_crossed_upper
      (z := -z) hneg0 hneg1
    simpa only [neg_sq, neg_neg, add_comm, XiC_even] using h

theorem integrableOn_thetaCuspTailSecondDensity_mul_phase_of_neg_one_lt_im
    {z : ℂ} (hz : -1 < z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z) (Ioi 0) := by
  let C := thetaCuspTailSecondDensityExpOneConstant
  let c := (1 : ℝ) + z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor : IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      (integrableOn_pow_mul_exp_neg_real 0 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z)
      (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp hrho).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hx0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      RHTower.norm_spectralTranslationPhase_eq_exp_neg_mul_im]
    dsimp only [C, c]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondDensityExpOneConstant_nonneg (Real.exp_pos _).le)]
    calc
      |thetaCuspTailSecondDensity x| * Real.exp (-x * z.im) ≤
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
            Real.exp (-x * z.im) := by gcongr
      _ = thetaCuspTailSecondDensityExpOneConstant *
          Real.exp (-((1 : ℝ) + z.im) * x) := by
        rw [show (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
              Real.exp (-x * z.im) = thetaCuspTailSecondDensityExpOneConstant *
                (Real.exp (-x) * Real.exp (-x * z.im)) by ring,
          ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_thetaCuspTailSecondDensity_mul_phaseDerivative_of_neg_one_lt_im
    {z : ℂ} (hz : -1 < z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  let C := thetaCuspTailSecondDensityExpOneConstant
  let c := (1 : ℝ) + z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor : IntegrableOn
      (fun x : ℝ => C * (x ^ 1 * Real.exp (-c * x))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensity x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z))
        (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp hrho).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hx0
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, RHTower.norm_spectralTranslationPhase_eq_exp_neg_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, pow_one]
    rw [abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondDensityExpOneConstant_nonneg
        (mul_nonneg hx0 (Real.exp_pos _).le))]
    dsimp only [C, c]
    calc
      |thetaCuspTailSecondDensity x| * (x * Real.exp (-x * z.im)) ≤
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
            (x * Real.exp (-x * z.im)) := by gcongr
      _ = thetaCuspTailSecondDensityExpOneConstant *
          (x * Real.exp (-((1 : ℝ) + z.im) * x)) := by
        rw [show (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
              (x * Real.exp (-x * z.im)) = thetaCuspTailSecondDensityExpOneConstant *
                (x * (Real.exp (-x) * Real.exp (-x * z.im))) by ring,
          ← Real.exp_add]
        congr 3
        ring

theorem hasDerivAt_thetaCuspTailSecondDensityPhaseValue
    {z₀ : ℂ} (hz₀ : -1 < z₀.im) :
    HasDerivAt thetaCuspTailSecondDensityPhaseValue
      (thetaCuspTailSecondDensityPhaseDerivative z₀) z₀ := by
  let ε : ℝ := (1 + z₀.im) / 2
  let c : ℝ := (1 + z₀.im) / 2
  let C : ℝ := thetaCuspTailSecondDensityExpOneConstant
  let bound : ℝ → ℝ := fun x => C * (x ^ 1 * Real.exp (-c * x))
  let F : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hc : 0 < c := by dsimp only [c]; linarith
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    dsimp only [bound]
    exact (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul C
  have hFmeas : ∀ z : ℂ, AEStronglyMeasurable (F z)
      (volume.restrict (Ioi 0)) := by
    intro z
    have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp hrho).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  have hF'meas : AEStronglyMeasurable (F' z₀)
      (volume.restrict (Ioi 0)) := by
    have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp hrho).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  have hdom : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hx0 : 0 ≤ x := hx.le
    have hzim : z₀.im - ε < z.im := by
      have hdist : dist z z₀ < ε := by simpa [Metric.mem_ball] using hz
      have himdist : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa only [sub_im] using Complex.abs_im_le_norm (z - z₀)
      have hnorm : ‖z - z₀‖ < ε := by
        simpa [Complex.dist_eq] using hdist
      have hlower : -‖z - z₀‖ ≤ z.im - z₀.im := (abs_le.mp himdist).1
      linarith
    have hrate : c ≤ 1 + z.im := by
      dsimp only [c, ε] at hzim ⊢
      linarith
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hx0
    have hexp : Real.exp (-(1 + z.im) * x) ≤ Real.exp (-c * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hxnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    rw [show ‖F' z x‖ =
        |thetaCuspTailSecondDensity x| *
          (x * Real.exp (-x * z.im)) by
      dsimp only [F']
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_I, mul_one, RHTower.norm_spectralTranslationPhase_eq_exp_neg_mul_im,
        hxnorm]
      ]
    dsimp only [bound, C]
    simp only [pow_one]
    calc
      |thetaCuspTailSecondDensity x| * (x * Real.exp (-x * z.im)) ≤
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
            (x * Real.exp (-x * z.im)) := by gcongr
      _ = thetaCuspTailSecondDensityExpOneConstant *
          (x * Real.exp (-(1 + z.im) * x)) := by
        rw [show (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
              (x * Real.exp (-x * z.im)) = thetaCuspTailSecondDensityExpOneConstant *
                (x * (Real.exp (-x) * Real.exp (-x * z.im))) by ring,
          ← Real.exp_add]
        congr 3
        ring
      _ ≤ thetaCuspTailSecondDensityExpOneConstant *
          (x * Real.exp (-c * x)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp hx0)
          thetaCuspTailSecondDensityExpOneConstant_nonneg
  have hdiff : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε,
        HasDerivAt (fun z => F z x) (F' z x) z := by
    filter_upwards with x
    intro z _hz
    dsimp only [F, F']
    convert (hasDerivAt_spectralTranslationPhase x z).const_mul
      (thetaCuspTailSecondDensity x : ℂ) using 1 <;> ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ ε) (bound := bound)
    (Metric.ball_mem_nhds z₀ hε)
    (Eventually.of_forall hFmeas)
    (integrableOn_thetaCuspTailSecondDensity_mul_phase_of_neg_one_lt_im hz₀)
    hF'meas hdom hbound hdiff
  simpa only [thetaCuspTailSecondDensityPhaseValue,
    thetaCuspTailSecondDensityPhaseDerivative, F, F'] using hresult.2

theorem thetaCuspTailSecondDensityPhaseValue_twoSided_derivative_crossed
    {z : ℂ} (hz : |z.im| < 1) :
    2 * z *
          (thetaCuspTailSecondDensityPhaseValue z +
            thetaCuspTailSecondDensityPhaseValue (-z)) +
        (z ^ 2 + 1 / 4) *
          (thetaCuspTailSecondDensityPhaseDerivative z -
            thetaCuspTailSecondDensityPhaseDerivative (-z)) =
      8 * z * XiC z + 4 * z ^ 2 * deriv XiC z := by
  have hzstrip := abs_lt.mp hz
  have hFz := hasDerivAt_thetaCuspTailSecondDensityPhaseValue (z₀ := z) hzstrip.1
  have hFneg := hasDerivAt_thetaCuspTailSecondDensityPhaseValue (z₀ := -z) (by
    simp only [neg_im]
    exact neg_lt_neg hzstrip.2)
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    convert (hasDerivAt_id z).neg using 1 <;> ring
  have hFnegComp := hFneg.comp z hneg
  have hsum : HasDerivAt (fun w : ℂ =>
      thetaCuspTailSecondDensityPhaseValue w +
        thetaCuspTailSecondDensityPhaseValue (-w))
      (thetaCuspTailSecondDensityPhaseDerivative z -
        thetaCuspTailSecondDensityPhaseDerivative (-z)) z := by
    convert hFz.add hFnegComp using 1 <;> ring
  have hp : HasDerivAt (fun w : ℂ => w ^ 2 + 1 / 4)
      (2 * z) z := by
    convert ((hasDerivAt_id z).pow 2).add_const (1 / 4 : ℂ) using 1 <;>
      simp only [id_eq] <;> ring
  have hleft := hp.mul hsum
  have hXi : HasDerivAt XiC (deriv XiC z) z :=
    (XiC_analytic z (Set.mem_univ z)).differentiableAt.hasDerivAt
  have hsq : HasDerivAt (fun w : ℂ => 4 * w ^ 2) (8 * z) z := by
    convert ((hasDerivAt_id z).pow 2).const_mul (4 : ℂ) using 1 <;>
      simp only [id_eq] <;> ring
  have hright := (hasDerivAt_const z (1 / 2 : ℂ)).add (hsq.mul hXi)
  have hmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact hzstrip
  have heq : (fun w : ℂ =>
      (w ^ 2 + 1 / 4) *
        (thetaCuspTailSecondDensityPhaseValue w +
          thetaCuspTailSecondDensityPhaseValue (-w))) =ᶠ[nhds z]
      (fun w : ℂ => 1 / 2 + 4 * w ^ 2 * XiC w) := by
    filter_upwards [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hmem] with w hw
    apply thetaCuspTailSecondDensityPhaseValue_twoSided_crossed
    rw [thetaCuspFourierLaplaceStrip] at hw
    exact abs_lt.mpr hw
  have huniq := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  convert huniq using 1 <;> ring


end


end RHTower
