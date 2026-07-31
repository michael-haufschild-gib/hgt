import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityReflection
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityMonotonicity

/-!
# A source-selected de Branges split for the completed theta density

The exact two-sided density reflection admits a canonical one-sided split.  This file proves its
sharp conjugation law, shows that its norm-square gap vanishes at every `XiC` zero in the open
theta strip, and determines the gap orientation strictly on the positive imaginary anchor.

The anchor sign is unconditional and uses the full canonical density: its two Laplace channels
are compared jointly before the completed reflection identity is applied.  No divisor data or
real-rootedness hypothesis enters.  The result is not an off-axis Hermite--Biehler theorem.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The damped one-sided component selected by the completed density reflection. -/
def thetaCuspTailSecondDensityDeBrangesE (z : ℂ) : ℂ :=
  (z ^ 2 + 1 / 4) * thetaCuspTailSecondDensityPhaseValue z - 1 / 4

/-- The reflected, growing one-sided component. -/
def thetaCuspTailSecondDensityDeBrangesESharp (z : ℂ) : ℂ :=
  (z ^ 2 + 1 / 4) * thetaCuspTailSecondDensityPhaseValue (-z) - 1 / 4

/-- The two one-sided components reconstruct the completed critical-line transform exactly. -/
theorem thetaCuspTailSecondDensityDeBrangesE_add_sharp
    {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesE z +
        thetaCuspTailSecondDensityDeBrangesESharp z =
      4 * z ^ 2 * XiC z := by
  have h := thetaCuspTailSecondDensityPhaseValue_twoSided_crossed hz
  unfold thetaCuspTailSecondDensityDeBrangesE
    thetaCuspTailSecondDensityDeBrangesESharp
  linear_combination h

theorem spectralTranslationPhase_conj_conj_eq_neg
    (x : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (spectralTranslationPhase x ((starRingEnd ℂ) z)) =
      spectralTranslationPhase x (-z) := by
  unfold spectralTranslationPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, Complex.conj_conj]
  ring

/-- Conjugating both the spectral point and the transform produces the reflected channel. -/
theorem thetaCuspTailSecondDensityPhaseValue_conj_conj
    {z : ℂ} (hz : |z.im| < 1) :
    (starRingEnd ℂ)
        (thetaCuspTailSecondDensityPhaseValue ((starRingEnd ℂ) z)) =
      thetaCuspTailSecondDensityPhaseValue (-z) := by
  have hzim : -1 < ((starRingEnd ℂ) z).im := by
    rw [conj_im]
    exact neg_lt_neg (abs_lt.mp hz).2
  have hint :=
    integrableOn_thetaCuspTailSecondDensity_mul_phase_of_neg_one_lt_im hzim
  unfold thetaCuspTailSecondDensityPhaseValue
  change (starRingEnd ℂ)
      (∫ x : ℝ,
        (thetaCuspTailSecondDensity x : ℂ) *
          spectralTranslationPhase x ((starRingEnd ℂ) z)
        ∂(volume.restrict (Ioi 0))) =
    ∫ x : ℝ,
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x (-z)
      ∂(volume.restrict (Ioi 0))
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, spectralTranslationPhase_conj_conj_eq_neg]
  simp

/-- The reflected component is the de Branges sharp transform of the damped component. -/
theorem thetaCuspTailSecondDensityDeBrangesE_sharp
    {z : ℂ} (hz : |z.im| < 1) :
    (starRingEnd ℂ)
        (thetaCuspTailSecondDensityDeBrangesE ((starRingEnd ℂ) z)) =
      thetaCuspTailSecondDensityDeBrangesESharp z := by
  unfold thetaCuspTailSecondDensityDeBrangesE
    thetaCuspTailSecondDensityDeBrangesESharp
  rw [map_sub, map_mul, map_add, map_pow,
    thetaCuspTailSecondDensityPhaseValue_conj_conj hz]
  simp only [Complex.conj_conj, map_div₀, map_one, map_ofNat]

/-- Oriented norm-square gap of the source-selected split. -/
def thetaCuspTailSecondDensityDeBrangesGap (z : ℂ) : ℝ :=
  Complex.normSq (thetaCuspTailSecondDensityDeBrangesE z) -
    Complex.normSq (thetaCuspTailSecondDensityDeBrangesESharp z)

/-- Exact division-free polarization of the source-selected gap.  The symmetric channel is the
completed Xi transform, while the antisymmetric channel retains the one-sided source orientation.
Thus any global sign theorem must control their relative phase; positivity of the density alone
does not disappear behind a quotient by `XiC`. -/
theorem thetaCuspTailSecondDensityDeBrangesGap_eq_polarizedCurrent
    {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesGap z =
      ((thetaCuspTailSecondDensityDeBrangesE z -
          thetaCuspTailSecondDensityDeBrangesESharp z) *
        starRingEnd ℂ (4 * z ^ 2 * XiC z)).re := by
  rw [← thetaCuspTailSecondDensityDeBrangesE_add_sharp hz]
  unfold thetaCuspTailSecondDensityDeBrangesGap
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Every `XiC` zero in the open theta strip forces equality of the two component norms. -/
theorem thetaCuspTailSecondDensityDeBrangesGap_eq_zero_of_XiC_eq_zero
    {z : ℂ} (hz : |z.im| < 1) (hzero : XiC z = 0) :
    thetaCuspTailSecondDensityDeBrangesGap z = 0 := by
  have hsum := thetaCuspTailSecondDensityDeBrangesE_add_sharp hz
  rw [hzero, mul_zero] at hsum
  have hsharp : thetaCuspTailSecondDensityDeBrangesESharp z =
      -thetaCuspTailSecondDensityDeBrangesE z := by
    linear_combination hsum
  unfold thetaCuspTailSecondDensityDeBrangesGap
  rw [hsharp]
  simp

/-- Integration by parts exposes the exact positive source behind the odd boundary channel. -/
theorem thetaCuspTailSecondDensity_sine_identity (t : ℝ) :
    t * (∫ x : ℝ in Ioi 0,
      thetaCuspTailSecondDensity x * Real.sin (t * x)) =
      ∫ x : ℝ in Ioi 0,
        (-4 * thetaCuspTailDerivative 3 x) * (1 - Real.cos (t * x)) := by
  let u : ℝ → ℝ := fun x => 1 - Real.cos (t * x)
  let u' : ℝ → ℝ := fun x => t * Real.sin (t * x)
  let v : ℝ → ℝ := thetaCuspTailSecondDensity
  let v' : ℝ → ℝ := fun x => 4 * thetaCuspTailDerivative 3 x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    have h := (hasDerivAt_const x 1).sub
      ((Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t))
    have hval : (0 : ℝ) - -Real.sin (t * x) * (t * 1) = u' x := by
      dsimp [u']
      ring
    rw [hval] at h
    exact h
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa only [v, v'] using hasDerivAt_thetaCuspTailSecondDensity_fromAtoms x
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have hbase := (integrableOn_thetaCuspTailDerivative_Ioi 3).const_mul 4
    have hcos := (integrableOn_cos_mul_thetaCuspTailDerivative 3 t).const_mul 4
    rw [show (u * v') = fun x =>
        4 * thetaCuspTailDerivative 3 x -
          4 * (Real.cos (t * x) * thetaCuspTailDerivative 3 x) by
      funext x
      dsimp [u, v']
      ring]
    exact hbase.sub hcos
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have hsin := (integrableOn_sin_mul_thetaCuspTailDerivative 2 t).const_mul (4 * t)
    rw [show (u' * v) = fun x =>
        (4 * t) * (Real.sin (t * x) * thetaCuspTailDerivative 2 x) by
      funext x
      dsimp [u', v, thetaCuspTailSecondDensity]
      ring]
    exact hsin
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (u * v) :=
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))).mul
          (continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt)
    have h2 : Tendsto (u * v) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0) := by
      simpa [u, v] using
        (hc.continuousAt : Tendsto (u * v) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
    exact h2
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have hv0 : Tendsto v atTop (𝓝 0) := by
      have h2 : Tendsto (fun x : ℝ => 4 * thetaCuspTailDerivative 2 x)
          atTop (𝓝 0) := by
        simpa using (thetaCuspTailDerivative_tendsto_atTop_zero 2).const_mul 4
      exact h2
    have hcos0 : Tendsto
        (fun x : ℝ => Real.cos (t * x) * v x) atTop (𝓝 0) := by
      have h : Tendsto
          (fun x : ℝ => 4 * (Real.cos (t * x) * thetaCuspTailDerivative 2 x))
          atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (cos_mul_thetaCuspTailDerivative_tendsto_atTop_zero 2 t).const_mul 4
      convert h using 1
      funext x
      dsimp [v, thetaCuspTailSecondDensity]
      ring
    simpa only [sub_zero] using hv0.sub hcos0
      |>.congr' (Eventually.of_forall fun x => by
        dsimp [u]
        ring)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v hzero hinfty
  rw [show (fun x : ℝ => u x * v' x) = fun x =>
      -((-4 * thetaCuspTailDerivative 3 x) * (1 - Real.cos (t * x))) by
    funext x
    dsimp [u, v']
    ring,
    integral_neg,
    show (fun x : ℝ => u' x * v x) = fun x =>
      t * (thetaCuspTailSecondDensity x * Real.sin (t * x)) by
      funext x
      dsimp [u', v]
      ring,
    integral_const_mul] at hibp
  linarith

/-- The odd sine channel of the strictly decreasing completed theta density is positive at every
positive frequency.  This is a source theorem, not a zero-location consequence. -/
theorem integral_thetaCuspTailSecondDensity_mul_sin_pos
    {t : ℝ} (ht : 0 < t) :
    0 < ∫ x : ℝ in Ioi 0,
      thetaCuspTailSecondDensity x * Real.sin (t * x) := by
  let h : ℝ → ℝ := fun x =>
    (-4 * thetaCuspTailDerivative 3 x) * (1 - Real.cos (t * x))
  have hhcont : Continuous h := by
    dsimp [h]
    exact (continuous_const.mul (differentiable_thetaCuspTailDerivative 3).continuous).mul
      (continuous_const.sub (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))
  have hhint : IntegrableOn h (Ioi 0) := by
    have hbase := (integrableOn_thetaCuspTailDerivative_Ioi 3).const_mul (-4)
    have hcos := (integrableOn_cos_mul_thetaCuspTailDerivative 3 t).const_mul (-4)
    rw [show h = fun x =>
        -4 * thetaCuspTailDerivative 3 x -
          (-4) * (Real.cos (t * x) * thetaCuspTailDerivative 3 x) by
      funext x
      dsimp [h]
      ring]
    exact hbase.sub hcos
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg
      (le_of_lt (mul_pos_of_neg_of_neg (by norm_num)
        (thetaCuspTailDerivative_three_neg hx.le)))
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hhpos : 0 < ∫ x : ℝ in Ioi 0, h x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhint).2
    have hopen : IsOpen (Function.support h ∩ Ioi (0 : ℝ)) :=
      hhcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨Real.pi / t, ?_, div_pos Real.pi_pos ht⟩
    change h (Real.pi / t) ≠ 0
    have harg : t * (Real.pi / t) = Real.pi := by field_simp
    dsimp [h]
    rw [harg, Real.cos_pi]
    have hderiv := thetaCuspTailDerivative_three_neg
      (show 0 ≤ Real.pi / t from (div_pos Real.pi_pos ht).le)
    exact ne_of_gt (mul_pos (mul_pos_of_neg_of_neg (by norm_num) hderiv) (by norm_num))
  have hid := thetaCuspTailSecondDensity_sine_identity t
  change t * (∫ x : ℝ in Ioi 0,
    thetaCuspTailSecondDensity x * Real.sin (t * x)) = _ at hid
  nlinarith

theorem thetaCuspTailSecondDensityPhaseValue_im_ofReal_eq_sine
    (t : ℝ) :
    (thetaCuspTailSecondDensityPhaseValue (t : ℂ)).im =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTailSecondDensity x * Real.sin (t * x) := by
  have hint := integrableOn_thetaCuspTailSecondDensity_mul_phase
    (z := (t : ℂ)) (by simp)
  unfold thetaCuspTailSecondDensityPhaseValue
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          spectralTranslationPhase x (t : ℂ)).im =
        ∫ x : ℝ in Ioi 0,
          ((thetaCuspTailSecondDensity x : ℂ) *
            spectralTranslationPhase x (t : ℂ)).im :=
      (integral_im hint).symm
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspTailSecondDensity x * Real.sin (t * x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hphaseIm : (spectralTranslationPhase x (t : ℂ)).im =
          Real.sin (x * t) := by
        unfold spectralTranslationPhase
        rw [show (x : ℂ) * I * (t : ℂ) = ((x * t : ℝ) : ℂ) * I by
          push_cast
          ring]
        exact Complex.exp_ofReal_mul_I_im (x * t)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, hphaseIm]
      congr 1
      ring_nf

theorem thetaCuspTailSecondDensityPhaseValue_im_ofReal_pos
    {t : ℝ} (ht : 0 < t) :
    0 < (thetaCuspTailSecondDensityPhaseValue (t : ℂ)).im := by
  rw [thetaCuspTailSecondDensityPhaseValue_im_ofReal_eq_sine]
  exact integral_thetaCuspTailSecondDensity_mul_sin_pos ht

/-- The antisymmetric boundary channel of the source-selected split has one strict orientation on
the whole positive real axis. -/
theorem thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos
    {t : ℝ} (ht : 0 < t) :
    0 < (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im := by
  have hF := thetaCuspTailSecondDensityPhaseValue_im_ofReal_pos ht
  have hq : (t : ℂ) ^ 2 + 1 / 4 = ((t ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold thetaCuspTailSecondDensityDeBrangesE
  rw [hq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rw [show ((1 / 4 : ℂ)).im = 0 by norm_num, sub_zero]
  nlinarith [sq_nonneg t]

/-- Real Laplace transform of the full canonical second density. -/
def thetaCuspTailSecondDensityRealLaplace (v : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspTailSecondDensity x * Real.exp (-v * x)

theorem spectralTranslationPhase_I_mul
    (x v : ℝ) :
    spectralTranslationPhase x (I * (v : ℂ)) =
      (Real.exp (-v * x) : ℂ) := by
  unfold spectralTranslationPhase
  have harg : (x : ℂ) * I * (I * (v : ℂ)) =
      ((-v * x : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [harg, Complex.ofReal_exp]

theorem thetaCuspTailSecondDensityPhaseValue_I_mul
    (v : ℝ) :
    thetaCuspTailSecondDensityPhaseValue (I * (v : ℂ)) =
      (thetaCuspTailSecondDensityRealLaplace v : ℂ) := by
  unfold thetaCuspTailSecondDensityPhaseValue
    thetaCuspTailSecondDensityRealLaplace
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        spectralTranslationPhase x (I * (v : ℂ))) =
      fun x : ℝ =>
        ((thetaCuspTailSecondDensity x * Real.exp (-v * x) : ℝ) : ℂ) by
    funext x
    rw [spectralTranslationPhase_I_mul]
    push_cast
    rfl]
  exact integral_ofReal
    (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)

theorem integrableOn_thetaCuspTailSecondDensity_mul_exp_neg
    {v : ℝ} (hv : -1 < v) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspTailSecondDensity x * Real.exp (-v * x)) (Ioi 0) := by
  have h :=
    integrableOn_thetaCuspTailSecondDensity_mul_phase_of_neg_one_lt_im
      (z := I * (v : ℂ)) (by simpa using hv)
  have hre := h.re
  have h2 : Integrable (fun x : ℝ =>
      RCLike.re ((thetaCuspTailSecondDensity x * Real.exp (-v * x) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
    simpa only [spectralTranslationPhase_I_mul, ← Complex.ofReal_mul] using hre
  exact h2

/-- Strict orientation of the two full-density Laplace channels. -/
theorem thetaCuspTailSecondDensityRealLaplace_lt_neg
    {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    thetaCuspTailSecondDensityRealLaplace v <
      thetaCuspTailSecondDensityRealLaplace (-v) := by
  have hplus := integrableOn_thetaCuspTailSecondDensity_mul_exp_neg
    (show -1 < v by linarith)
  have hminus := integrableOn_thetaCuspTailSecondDensity_mul_exp_neg
    (show -1 < -v by linarith)
  let f : ℝ → ℝ := fun x =>
    thetaCuspTailSecondDensity x *
      (Real.exp (v * x) - Real.exp (-v * x))
  have hfcont : Continuous f := by
    exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspTailSecondDensity x).continuousAt).mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
          (Real.continuous_exp.comp
            (continuous_const.neg.mul continuous_id)))
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := hminus.sub hplus
    refine h.congr ?_
    filter_upwards with x
    dsimp [f]
    ring_nf
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hexp : Real.exp (-v * x) ≤ Real.exp (v * x) := by
      rw [Real.exp_le_exp]
      nlinarith [mul_pos hv0 hx]
    exact mul_nonneg (thetaCuspTailSecondDensity_pos hx).le
      (sub_nonneg.mpr hexp)
  have hpos : 0 < ∫ x : ℝ in Ioi 0, f x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
    have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
      hfcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change f 1 ≠ 0
    have hrho := thetaCuspTailSecondDensity_pos (x := 1) (by norm_num)
    have hexp : Real.exp (-v) < Real.exp v := by
      rw [Real.exp_lt_exp]
      linarith
    dsimp [f]
    simp only [mul_one]
    exact (mul_pos hrho (sub_pos.mpr hexp)).ne'
  have hdiff :
      (∫ x : ℝ in Ioi 0, f x) =
        thetaCuspTailSecondDensityRealLaplace (-v) -
          thetaCuspTailSecondDensityRealLaplace v := by
    unfold thetaCuspTailSecondDensityRealLaplace
    rw [← integral_sub hminus hplus]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [f]
    ring_nf
  rw [hdiff] at hpos
  linarith

theorem XiC_I_mul_eq_xi_real (v : ℝ) :
    XiC (I * (v : ℂ)) = xi ((1 / 2 - v : ℝ) : ℂ) := by
  unfold XiC
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem thetaCuspTailSecondDensityDeBrangesE_I_mul
    (v : ℝ) :
    thetaCuspTailSecondDensityDeBrangesE (I * (v : ℂ)) =
      (((1 / 4 - v ^ 2) * thetaCuspTailSecondDensityRealLaplace v -
        1 / 4 : ℝ) : ℂ) := by
  unfold thetaCuspTailSecondDensityDeBrangesE
  rw [thetaCuspTailSecondDensityPhaseValue_I_mul v]
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem thetaCuspTailSecondDensityDeBrangesESharp_I_mul
    (v : ℝ) :
    thetaCuspTailSecondDensityDeBrangesESharp (I * (v : ℂ)) =
      (((1 / 4 - v ^ 2) * thetaCuspTailSecondDensityRealLaplace (-v) -
        1 / 4 : ℝ) : ℂ) := by
  unfold thetaCuspTailSecondDensityDeBrangesESharp
  rw [show -(I * (v : ℂ)) = I * ((-v : ℝ) : ℂ) by push_cast; ring]
  rw [thetaCuspTailSecondDensityPhaseValue_I_mul (-v)]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The source-selected de Branges gap has the strict favorable orientation on the positive
imaginary anchor inside the critical strip. -/
theorem thetaCuspTailSecondDensityDeBrangesGap_I_mul_pos
    {v : ℝ} (hv0 : 0 < v) (hvhalf : v < 1 / 2) :
    0 < thetaCuspTailSecondDensityDeBrangesGap (I * (v : ℂ)) := by
  let A : ℝ :=
    (1 / 4 - v ^ 2) * thetaCuspTailSecondDensityRealLaplace v - 1 / 4
  let B : ℝ :=
    (1 / 4 - v ^ 2) * thetaCuspTailSecondDensityRealLaplace (-v) - 1 / 4
  have hq : 0 < 1 / 4 - v ^ 2 := by nlinarith
  have hL := thetaCuspTailSecondDensityRealLaplace_lt_neg hv0 (by linarith)
  have hAB : A < B := by
    dsimp [A, B]
    nlinarith
  have hstrip : |(I * (v : ℂ)).im| < 1 := by
    have hvabs : |v| < 1 := by
      rw [abs_of_pos hv0]
      linarith
    simpa only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re,
      zero_add, one_mul] using hvabs
  have hsum := thetaCuspTailSecondDensityDeBrangesE_add_sharp hstrip
  have hxiRe : 0 < (XiC (I * (v : ℂ))).re := by
    rw [XiC_I_mul_eq_xi_real]
    exact xi_pos_on_real_anchor (by linarith) (by linarith)
  have hxiIm : (XiC (I * (v : ℂ))).im = 0 := by
    rw [XiC_I_mul_eq_xi_real]
    exact xi_real_on_real_anchor (by linarith) (by linarith)
  have hzsq : (I * (v : ℂ)) ^ 2 = -((v ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  let X : ℝ := (XiC (I * (v : ℂ))).re
  have hXpos : 0 < X := by
    change 0 < (XiC (I * (v : ℂ))).re
    exact hxiRe
  have hxiEq : XiC (I * (v : ℂ)) = (X : ℂ) := by
    apply Complex.ext <;> simp [X, hxiIm]
  have hsumneg : A + B < 0 := by
    rw [thetaCuspTailSecondDensityDeBrangesE_I_mul v,
      thetaCuspTailSecondDensityDeBrangesESharp_I_mul v] at hsum
    have hsum' : ((A + B : ℝ) : ℂ) =
        ((-4 * v ^ 2 * X : ℝ) : ℂ) := by
      rw [Complex.ofReal_add]
      dsimp [A, B]
      calc
        _ = 4 * (I * (v : ℂ)) ^ 2 * XiC (I * (v : ℂ)) := hsum
        _ = _ := by rw [hzsq, hxiEq]; push_cast; ring
    have hsumRe := congrArg Complex.re hsum'
    have hsumRe' : A + B = -4 * v ^ 2 * X := by
      simpa only [ofReal_re] using hsumRe
    have hrightpos : 0 < 4 * v ^ 2 * X :=
      mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hv0)) hXpos
    have hrightneg : -4 * v ^ 2 * X < 0 := by nlinarith
    linarith
  have hprod : 0 < (A - B) * (A + B) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hAB) hsumneg
  unfold thetaCuspTailSecondDensityDeBrangesGap
  rw [thetaCuspTailSecondDensityDeBrangesE_I_mul v,
    thetaCuspTailSecondDensityDeBrangesESharp_I_mul v]
  rw [Complex.normSq_ofReal, Complex.normSq_ofReal]
  dsimp [A, B] at hprod ⊢
  nlinarith

end

end RHTower
