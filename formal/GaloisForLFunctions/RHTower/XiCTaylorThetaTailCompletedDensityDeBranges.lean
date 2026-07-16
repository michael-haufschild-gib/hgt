import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityReflection

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
  simpa only [spectralTranslationPhase_I_mul, ← Complex.ofReal_mul,
    ofReal_re] using hre

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
