import GaloisForLFunctions.RHTower.ThetaCuspFourierXi
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# The theta-cusp source discharges the first prime--archimedean Hankel level

The completed theta-cusp source is strictly positive on the positive logarithmic half-line.  The
critical completed function is exactly its cosine transform.  Differentiating this transform twice
shows that `Xi''(0) < 0`, while its value at the center is positive.  Consequently the zeroth
Taylor moment of the normalized continued prime--Gamma trace is strictly positive, and every
constant-polynomial source Hankel test is nonnegative.

This is only the first level of the countable source criterion.  Higher normalized trace moments
are logarithmic cumulants of the theta source, not its raw positive moments, so positivity of the
source density alone does not imply the remaining Hankel inequalities.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta Polynomial
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

theorem thetaCuspSourceTerm_nonneg_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ thetaCuspSourceTerm x n := by
  rcases n with _ | n
  · simp [thetaCuspSourceTerm, thetaCuspSeed]
  · apply mul_nonneg (Real.exp_pos _).le
    apply (thetaCuspSeed_pos ?_).le
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have he : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
    have ht : 1 < ((n + 1 : ℕ) : ℝ) * Real.exp x := by
      nlinarith [Real.exp_pos x]
    have ht2 : 1 < (((n + 1 : ℕ) : ℝ) * Real.exp x) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three, Real.pi_pos,
      mul_pos (sub_pos.mpr ht2) (show 0 < 2 * Real.pi by positivity)]

theorem thetaCuspSourceTerm_one_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspSourceTerm x 1 := by
  rw [thetaCuspSourceTerm]
  apply mul_pos (Real.exp_pos _)
  apply thetaCuspSeed_pos
  norm_num
  have he : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
  have he2 : 1 < Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
  nlinarith [Real.pi_gt_three, Real.pi_pos,
    mul_pos (sub_pos.mpr he2) (show 0 < 2 * Real.pi by positivity)]

/-- The full theta-cusp source is pointwise strictly positive on the positive half-line. -/
theorem thetaCuspFullSource_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspFullSource x := by
  rw [thetaCuspFullSource]
  exact (summable_thetaCuspSourceTerm x).tsum_pos
    (thetaCuspSourceTerm_nonneg_of_pos hx) 1
    (thetaCuspSourceTerm_one_pos_of_pos hx)

theorem integrable_thetaCuspSecondMoment :
    Integrable (fun x : ℝ => x ^ 2 * thetaCuspFullSource x) := by
  have hmajor := thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) 2
  apply hmajor.mono
  · exact ((continuous_id.pow 2).mul
      contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    simp [Real.norm_eq_abs]

/-- The positive theta source has a strictly positive second logarithmic moment. -/
theorem integral_Ioi_thetaCuspSecondMoment_pos :
    0 < ∫ x : ℝ in Ioi 0, x ^ 2 * thetaCuspFullSource x := by
  let f : ℝ → ℝ := fun x => x ^ 2 * thetaCuspFullSource x
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_id.pow 2).mul contDiff_thetaCuspFullSource.continuous
  have hfint : IntegrableOn f (Ioi 0) := integrable_thetaCuspSecondMoment.integrableOn
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sq_nonneg x) (thetaCuspFullSource_pos_of_pos hx).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  simpa [f] using (thetaCuspFullSource_pos_of_pos (x := 1) zero_lt_one).ne'

theorem integral_Ioi_thetaCuspFullSource_pos :
    0 < ∫ x : ℝ in Ioi 0, thetaCuspFullSource x := by
  let f : ℝ → ℝ := thetaCuspFullSource
  have hfcont : Continuous f := contDiff_thetaCuspFullSource.continuous
  have hfint : IntegrableOn f (Ioi 0) :=
    (thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))).integrableOn
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (thetaCuspFullSource_pos_of_pos hx).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact (thetaCuspFullSource_pos_of_pos (x := 1) zero_lt_one).ne'

/-- The real one-sided completed Fourier trace is exactly four times the raw tail cosine trace. -/
theorem re_fourier_xiThetaPositiveSource_eq_four_mul_tail_cos (t : ℝ) :
    (𝓕 xiThetaPositiveSource (t / (4 * Real.pi))).re =
      4 * ∫ x : ℝ in Ioi 0,
        thetaCuspTailDerivative 0 x * Real.cos (t * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hf : Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * v * (t / (4 * Real.pi))) * I) •
        xiThetaPositiveSource v) := by
    let phase : ℝ → ℝ := fun v => -2 * Real.pi * v * (t / (4 * Real.pi))
    let phi : ℝ → ℂ := fun v =>
      Complex.exp ((phase v : ℂ) * I)
    have hphi_meas : AEStronglyMeasurable phi (volume : Measure ℝ) := by
      exact (by fun_prop : Continuous phi).aestronglyMeasurable
    have hphi_norm : ∀ᵐ v : ℝ, ‖phi v‖ ≤ 1 := by
      filter_upwards with v
      change ‖Complex.exp ((phase v : ℂ) * I)‖ ≤ 1
      rw [Complex.norm_exp]
      have hre : (((phase v : ℂ) * I).re) = 0 := by simp
      rw [hre]
      norm_num
    have h := xiThetaPositiveSource_integrable.bdd_smul 1
      hphi_meas hphi_norm
    change Integrable (fun v : ℝ => phi v • xiThetaPositiveSource v) at h
    simpa only [phi, phase] using h
  change RCLike.re (∫ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * (t / (4 * Real.pi))) * I) •
        xiThetaPositiveSource v) = _
  rw [← integral_re hf]
  let g : ℝ → ℝ := fun u =>
    2 * thetaCuspTailDerivative 0 (u / 2) * Real.cos (t * (u / 2))
  rw [show (fun u : ℝ => RCLike.re
      (Complex.exp (↑(-2 * Real.pi * u * (t / (4 * Real.pi))) * I) •
        xiThetaPositiveSource u)) = (Ioi (0 : ℝ)).indicator g by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu, xiThetaPositiveSource, indicator_of_mem hu]
      have hu0 : 0 < u := hu
      have hs := xiThetaLogSource_two_mul_eq_tail (x := u / 2) (by linarith)
      have hs' : xiThetaLogSource u =
          (2 * thetaCuspTailDerivative 0 (u / 2) : ℝ) := by
        convert hs using 1
        all_goals ring
      rw [hs']
      change (Complex.exp
          (↑(-2 * Real.pi * u * (t / (4 * Real.pi))) * I) *
            (2 * thetaCuspTailDerivative 0 (u / 2) : ℝ)).re = g u
      have hphase : -2 * Real.pi * u * (t / (4 * Real.pi)) =
          -(t * (u / 2)) := by
        field_simp [Real.pi_ne_zero]
        ring
      have hphaseC :
          (((-2 * Real.pi * u * (t / (4 * Real.pi)) : ℝ) : ℂ) * I) =
            (((-(t * (u / 2)) : ℝ) : ℂ) * I) := by
        exact congrArg (fun r : ℝ => (r : ℂ) * I) hphase
      rw [hphaseC]
      change (Complex.exp (((-(t * (u / 2)) : ℝ) : ℂ) * I) *
        (2 * thetaCuspTailDerivative 0 (u / 2) : ℝ)).re = g u
      rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
      simp [g, Real.cos_neg]
      ring
    · rw [indicator_of_notMem hu, xiThetaPositiveSource, indicator_of_notMem hu]
      simp]
  rw [integral_indicator measurableSet_Ioi]
  have hscale := integral_comp_mul_left_Ioi g 0 (show (0 : ℝ) < 2 by norm_num)
  have hcomp : (fun x : ℝ => g (2 * x)) = fun x =>
      2 * (thetaCuspTailDerivative 0 x * Real.cos (t * x)) := by
    funext x
    simp [g]
    ring
  rw [hcomp, integral_const_mul] at hscale
  norm_num at hscale ⊢
  linarith

/-- Exact positive-source cosine representation of the centered completed function. -/
theorem XiC_ofReal_eq_two_mul_thetaCuspCosine (t : ℝ) :
    XiC (t : ℂ) =
      ((2 * ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (t * x) : ℝ) : ℂ) := by
  rw [XiC_ofReal_eq_completedRiemannZeta₀,
    completedRiemannZeta₀_critical_eq_re_positiveFourier,
    re_fourier_xiThetaPositiveSource_eq_four_mul_tail_cos,
    integral_Ioi_thetaCuspFullSource_mul_cos]
  push_cast
  ring

def thetaCuspCosineRepresentation (t : ℝ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t * x)

theorem Xi_eq_thetaCuspCosineRepresentation (t : ℝ) :
    Xi t = thetaCuspCosineRepresentation t := by
  have h := congrArg Complex.re (XiC_ofReal_eq_two_mul_thetaCuspCosine t)
  simpa [XiC_ofReal, thetaCuspCosineRepresentation] using h

theorem integrableOn_thetaCuspFirstMoment :
    IntegrableOn (fun x : ℝ => x * thetaCuspFullSource x) (Ioi 0) := by
  have hmajor := thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) 1
  apply (hmajor.mono
    ((continuous_id.mul contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable)
    (by
      filter_upwards with x
      simp [Real.norm_eq_abs])).integrableOn

theorem hasDerivAt_thetaCuspCosineRepresentation (t : ℝ) :
    HasDerivAt thetaCuspCosineRepresentation
      (∫ x : ℝ in Ioi 0,
        -2 * x * thetaCuspFullSource x * Real.sin (t * x)) t := by
  let F : ℝ → ℝ → ℝ := fun s x =>
    2 * thetaCuspFullSource x * Real.cos (s * x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    -2 * x * thetaCuspFullSource x * Real.sin (s * x)
  let bound : ℝ → ℝ := fun x =>
    2 * (‖x‖ ^ 1 * ‖thetaCuspSchwartzReal x‖)
  have hFint : Integrable (F t) (volume.restrict (Ioi 0)) := by
    have hbase : Integrable (fun x : ℝ => thetaCuspSchwartzReal x)
        (volume.restrict (Ioi 0)) :=
      (thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))).restrict
    have hmeas : AEStronglyMeasurable (fun x : ℝ => 2 * Real.cos (t * x))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous (fun x : ℝ => 2 * Real.cos (t * x))).aestronglyMeasurable
    have hbd : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
        ‖2 * Real.cos (t * x)‖ ≤ 2 := by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_cos_le_one (t * x)]
    have hmul := hbase.bdd_mul (c := 2) hmeas hbd
    simpa only [F, thetaCuspSchwartzReal_apply, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    exact ((thetaCuspSchwartzReal.integrable_pow_mul
      (volume : Measure ℝ) 1).const_mul 2).restrict
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := t) (s := Set.univ) (bound := bound)
    univ_mem
    (Filter.Eventually.of_forall fun s =>
      (by
        dsimp [F]
        exact ((continuous_const.mul contDiff_thetaCuspFullSource.continuous).mul
          ((Real.continuous_cos.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable))
    hFint
    (by
      dsimp [F']
      exact ((((continuous_const.mul continuous_id).mul
        contDiff_thetaCuspFullSource.continuous).mul
          (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (by
      filter_upwards with x
      intro s hs
      dsimp [F', bound]
      simp only [pow_one]
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
      calc
        2 * |x| * |thetaCuspFullSource x| * |Real.sin (s * x)| ≤
            2 * |x| * |thetaCuspFullSource x| * 1 := by
          gcongr
          exact abs_sin_le_one _
        _ = 2 * (|x| * |thetaCuspFullSource x|) := by ring)
    hbound
    (by
      filter_upwards with x
      intro s hs
      dsimp [F, F']
      have hcos : HasDerivAt
          (fun y : ℝ => Real.cos (y * x))
          (-Real.sin (s * x) * x) s := by
        simpa only [Function.comp_def, id_eq, one_mul] using
          (Real.hasDerivAt_cos (s * x)).comp s
            ((hasDerivAt_id s).mul_const x)
      exact ((hasDerivAt_const s (2 * thetaCuspFullSource x)).mul hcos).congr_deriv
        (by ring))
  change HasDerivAt
    (fun s : ℝ =>
      2 * ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (s * x))
    (∫ x : ℝ in Ioi 0,
      -2 * x * thetaCuspFullSource x * Real.sin (t * x)) t
  simpa only [thetaCuspCosineRepresentation, F, F', integral_const_mul,
    mul_assoc, neg_mul] using hresult.2

theorem hasDerivAt_thetaCuspCosineRepresentation_derivative (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∫ x : ℝ in Ioi 0,
        -2 * x * thetaCuspFullSource x * Real.sin (s * x))
      (∫ x : ℝ in Ioi 0,
        -2 * x ^ 2 * thetaCuspFullSource x * Real.cos (t * x)) t := by
  let F : ℝ → ℝ → ℝ := fun s x =>
    -2 * x * thetaCuspFullSource x * Real.sin (s * x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    -2 * x ^ 2 * thetaCuspFullSource x * Real.cos (s * x)
  let bound : ℝ → ℝ := fun x =>
    2 * (‖x‖ ^ 2 * ‖thetaCuspSchwartzReal x‖)
  have hFint : Integrable (F t) (volume.restrict (Ioi 0)) := by
    have hbase := integrableOn_thetaCuspFirstMoment
    have hmul := hbase.bdd_mul (c := 2)
      ((by fun_prop : Continuous (fun x : ℝ => -2 * Real.sin (t * x))).aestronglyMeasurable)
      (by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_mul]
        norm_num
        nlinarith [abs_sin_le_one (t * x)])
    simpa only [F, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    exact ((thetaCuspSchwartzReal.integrable_pow_mul
      (volume : Measure ℝ) 2).const_mul 2).restrict
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := t) (s := Set.univ) (bound := bound)
    univ_mem
    (Filter.Eventually.of_forall fun s =>
      (by
        dsimp [F]
        exact ((((continuous_const.mul continuous_id).mul
          contDiff_thetaCuspFullSource.continuous).mul
            (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)))
    hFint
    (by
      dsimp [F']
      exact ((((continuous_const.mul (continuous_id.pow 2)).mul
        contDiff_thetaCuspFullSource.continuous).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (by
      filter_upwards with x
      intro s hs
      dsimp [F', bound]
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
      calc
        2 * x ^ 2 * |thetaCuspFullSource x| * |Real.cos (s * x)| ≤
            2 * x ^ 2 * |thetaCuspFullSource x| * 1 := by
          gcongr
          exact abs_cos_le_one _
        _ = 2 * (x ^ 2 * |thetaCuspFullSource x|) := by ring)
    hbound
    (by
      filter_upwards with x
      intro s hs
      dsimp [F, F']
      have hsin : HasDerivAt
          (fun y : ℝ => Real.sin (y * x))
          (Real.cos (s * x) * x) s := by
        simpa only [Function.comp_def, id_eq, one_mul] using
          (Real.hasDerivAt_sin (s * x)).comp s
            ((hasDerivAt_id s).mul_const x)
      exact
        ((hasDerivAt_const s (-2 * x * thetaCuspFullSource x)).mul hsin).congr_deriv
          (by ring))
  have h := hresult.2
  change HasDerivAt
    (fun s => ∫ x : ℝ in Ioi 0, F s x)
    (∫ x : ℝ in Ioi 0, F' t x) t at h
  simpa only [F, F'] using h

theorem deriv_thetaCuspCosineRepresentation (t : ℝ) :
    deriv thetaCuspCosineRepresentation t =
      ∫ x : ℝ in Ioi 0,
        -2 * x * thetaCuspFullSource x * Real.sin (t * x) :=
  (hasDerivAt_thetaCuspCosineRepresentation t).deriv

theorem secondDeriv_thetaCuspCosineRepresentation (t : ℝ) :
    deriv (deriv thetaCuspCosineRepresentation) t =
      ∫ x : ℝ in Ioi 0,
        -2 * x ^ 2 * thetaCuspFullSource x * Real.cos (t * x) := by
  rw [show deriv thetaCuspCosineRepresentation = fun s : ℝ =>
      ∫ x : ℝ in Ioi 0,
        -2 * x * thetaCuspFullSource x * Real.sin (s * x) by
    funext s
    exact deriv_thetaCuspCosineRepresentation s]
  exact (hasDerivAt_thetaCuspCosineRepresentation_derivative t).deriv

theorem Xi_secondDeriv_zero_eq_neg_two_mul_thetaCuspSecondMoment :
    deriv (deriv Xi) 0 =
      -2 * ∫ x : ℝ in Ioi 0, x ^ 2 * thetaCuspFullSource x := by
  rw [show Xi = thetaCuspCosineRepresentation by
    funext t
    exact Xi_eq_thetaCuspCosineRepresentation t,
    secondDeriv_thetaCuspCosineRepresentation]
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [show (fun x : ℝ => -2 * x ^ 2 * thetaCuspFullSource x) =
      fun x => -2 * (x ^ 2 * thetaCuspFullSource x) by
    funext x
    ring,
    integral_const_mul]

/-- The completed critical function is strictly concave at its center, unconditionally. -/
theorem Xi_secondDeriv_zero_neg : deriv (deriv Xi) 0 < 0 := by
  rw [Xi_secondDeriv_zero_eq_neg_two_mul_thetaCuspSecondMoment]
  nlinarith [integral_Ioi_thetaCuspSecondMoment_pos]

theorem Xi_zero_eq_two_mul_integral_thetaCuspFullSource :
    Xi 0 = 2 * ∫ x : ℝ in Ioi 0, thetaCuspFullSource x := by
  rw [Xi_eq_thetaCuspCosineRepresentation]
  simp [thetaCuspCosineRepresentation]

theorem Xi_zero_pos : 0 < Xi 0 := by
  rw [Xi_zero_eq_two_mul_integral_thetaCuspFullSource]
  exact mul_pos (by norm_num) integral_Ioi_thetaCuspFullSource_pos

theorem Xi_deriv_zero : deriv Xi 0 = 0 := by
  rw [show Xi = thetaCuspCosineRepresentation by
    funext t
    exact Xi_eq_thetaCuspCosineRepresentation t,
    deriv_thetaCuspCosineRepresentation]
  simp

theorem analyticTraceMoments_normalizedPrimeArchSource_zero_eq_Xi_ratio :
    analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 =
      -deriv (deriv Xi) 0 / Xi 0 := by
  rw [analyticTraceMoments]
  norm_num
  rw [normalizedTraceMomentGerm, dslope_same]
  have hXi : HasDerivAt XiC (deriv XiC 0) 0 :=
    (XiC_analytic 0 (Set.mem_univ 0)).differentiableAt.hasDerivAt
  have hXi' : HasDerivAt (deriv XiC) (deriv (deriv XiC) 0) 0 :=
    ((XiC_analytic 0 (Set.mem_univ 0)).deriv).differentiableAt.hasDerivAt
  have hquot := hXi'.div hXi XiC_zero_ne
  have hlog : deriv (logDeriv XiC) 0 =
      (deriv (deriv XiC) 0 * XiC 0 - deriv XiC 0 * deriv XiC 0) /
        XiC 0 ^ 2 := by
    rw [show logDeriv XiC = deriv XiC / XiC by rfl]
    exact hquot.deriv
  have h2 : deriv (deriv XiC) 0 = ((deriv (deriv Xi) 0 : ℝ) : ℂ) := by
    simpa using XiC_secondDeriv_ofReal 0
  have h1 : deriv XiC 0 = ((deriv Xi 0 : ℝ) : ℂ) := by
    simpa using XiC_deriv_ofReal 0
  have h0 : XiC 0 = ((Xi 0 : ℝ) : ℂ) := by
    simpa using XiC_ofReal 0
  rw [continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC.deriv_eq,
    hlog, h2, h1, h0, Xi_deriv_zero]
  have hXi0 : Xi 0 ≠ 0 := Xi_zero_pos.ne'
  simp only [Complex.ofReal_zero, mul_zero, sub_zero]
  have hc :
      -(((deriv (deriv Xi) 0 : ℝ) : ℂ) * ((Xi 0 : ℝ) : ℂ) /
          (((Xi 0 : ℝ) : ℂ) ^ 2)) =
        (((-deriv (deriv Xi) 0 / Xi 0 : ℝ)) : ℂ) := by
    push_cast
    field_simp [hXi0]
  rw [hc]
  simp

/-- The zeroth normalized completed prime--Gamma trace moment is strictly positive. -/
theorem analyticTraceMoments_normalizedPrimeArchSource_zero_pos :
    0 < analyticTraceMoments
      (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 := by
  rw [analyticTraceMoments_normalizedPrimeArchSource_zero_eq_Xi_ratio]
  exact div_pos (neg_pos.mpr Xi_secondDeriv_zero_neg) Xi_zero_pos

theorem primeArchSourceTraceHankel_C_re (c : ℝ) :
    (primeArchSourceTraceHankel (Polynomial.C c)).re =
      c ^ 2 * analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 := by
  rw [primeArchSourceTraceHankel]
  have hsq :
      ((Polynomial.C c).map (algebraMap ℝ ℂ)) ^ 2 =
        Polynomial.C (((c ^ 2 : ℝ) : ℂ)) := by
    ext n
    rcases n with _ | n
    · simp [pow_two]
    · simp [pow_two]
  rw [hsq]
  simp only [Polynomial.natDegree_C, zero_add, Finset.range_one,
    Finset.sum_singleton, Polynomial.coeff_C_zero, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Every constant-polynomial test in the prime--archimedean Hankel family is nonnegative. -/
theorem primeArchSourceTraceHankel_C_re_nonneg (c : ℝ) :
    0 ≤ (primeArchSourceTraceHankel (Polynomial.C c)).re := by
  rw [primeArchSourceTraceHankel_C_re]
  exact
    mul_nonneg (sq_nonneg c)
      analyticTraceMoments_normalizedPrimeArchSource_zero_pos.le

/-- Every nonzero constant-polynomial test is strictly positive. -/
theorem primeArchSourceTraceHankel_C_re_pos {c : ℝ} (hc : c ≠ 0) :
    0 < (primeArchSourceTraceHankel (Polynomial.C c)).re := by
  rw [primeArchSourceTraceHankel_C_re]
  exact
    mul_pos (sq_pos_of_ne_zero hc)
      analyticTraceMoments_normalizedPrimeArchSource_zero_pos

end RHTower
