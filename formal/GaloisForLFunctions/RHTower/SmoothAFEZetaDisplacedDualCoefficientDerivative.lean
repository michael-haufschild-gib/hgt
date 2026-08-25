import GaloisForLFunctions.RHTower.ZetaChiLeftEdgeLogDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedHeadDerivativeApproximation
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# Height derivative of the exact general reflected coefficient

The fixed left contour has absolute exponent `-(3/2+d)`.  Differentiating
its chi and Dirichlet-power factors adds only polynomial frequency growth and
one logarithm of the index, both absorbed by the Gaussian and the summable
left-edge power.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Frequency integrand for the height derivative of one reflected AFE
coefficient on a displaced line. -/
def smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
    (d x tau : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  let w : ℂ := (-1 : ℂ) + (v : ℂ) * I
  let z : ℂ := displacedLinePt d tau + w
  (((deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1) +
      zetaChi z *
        ((n + 1 : ℂ) ^ (z - 1) * Complex.log (n + 1 : ℂ) * I)) *
    (x : ℂ) ^ w) * smoothAFEGaussianKernel w

theorem hasDerivAt_smoothAFEZetaReflectedTerm_displaced_left_one
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) (v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
        ((-1 : ℂ) + (v : ℂ) * I))
      (smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
        d x tau n v) tau := by
  let w : ℂ := (-1 : ℂ) + (v : ℂ) * I
  let z : ℂ := displacedLinePt d tau + w
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
  have hGamma : Gammaℝ (1 - z) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    dsimp only [z, w]
    simp [displacedLinePt]
    linarith
  have hchi := ((zetaChi_analyticAt hGamma).differentiableAt.hasDerivAt.comp
    tau ((hasDerivAt_displacedLinePt d tau).add_const w))
  have hpowC := (Complex.hasStrictDerivAt_const_cpow
    (x := (n + 1 : ℂ)) (y := z - 1) (Or.inl hn)).hasDerivAt
  have hpow := hpowC.comp tau
    (((hasDerivAt_displacedLinePt d tau).add_const w).sub_const 1)
  have hmain := (hchi.mul hpow).mul_const ((x : ℂ) ^ w)
  have hfull := hmain.mul_const (smoothAFEGaussianKernel w)
  have heq : (fun u : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d u) x n w) =
      (fun u : ℝ =>
        ((zetaChi (displacedLinePt d u + w) *
          (n + 1 : ℂ) ^ (displacedLinePt d u + w - 1)) *
          (x : ℂ) ^ w) * smoothAFEGaussianKernel w) := by
    funext u
    exact smoothAFEZetaReflectedTerm_eq_cpow
      (displacedLinePt d u) x n w
  rw [heq]
  dsimp only [smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative]
  simpa [Function.comp_apply, z, w, mul_assoc] using hfull

/-- Pointwise Gaussian majorant for the differentiated reflected integrand.
The constant may depend on fixed `d,x`, while height and frequency remain
explicit. -/
theorem exists_norm_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_le
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : ℝ, ∀ n : ℕ, ∀ v : ℝ,
      ‖smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative d x tau n v‖ ≤
        C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) *
          (1 + |tau| + |v|) ^ 3 *
          (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
  let sigma : ℝ := -1 / 2 - d
  have hsigmaLow : -3 / 4 ≤ sigma := by dsimp only [sigma]; linarith
  have hsigmaHigh : sigma ≤ -1 / 2 := by dsimp only [sigma]; linarith
  obtain ⟨K0, hK0, hchi⟩ := exists_bound_norm_zetaChi_vertical
    (show sigma ≠ 0 by dsimp only [sigma]; linarith)
    (by dsimp only [sigma]; linarith)
    (by dsimp only [sigma]; linarith)
  obtain ⟨K1, hK1, hderiv⟩ :=
    exists_norm_deriv_zetaChi_vertical_left_edge_le hsigmaLow hsigmaHigh
  let C : ℝ := K0 + K1
  refine ⟨C, add_nonneg hK0 hK1, fun tau n v => ?_⟩
  let r : ℝ := n + 1
  let t : ℝ := tau + v
  let q : ℝ := 1 + |tau| + |v|
  let w : ℂ := (-1 : ℂ) + (v : ℂ) * I
  let z : ℂ := displacedLinePt d tau + w
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast Nat.succ_pos n
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by
    dsimp only [r]
    exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg tau, abs_nonneg v]
  have htq : 1 + |t| ≤ q := by
    dsimp only [t, q]
    linarith [abs_add_le tau v]
  have htq2 : (1 + |t|) ^ 2 ≤ q ^ 3 := by
    have h2 : (1 + |t|) ^ 2 ≤ q ^ 2 := by gcongr
    exact h2.trans (pow_le_pow_right₀ hq1 (by omega))
  have htq3 : (1 + |t|) ^ 3 ≤ q ^ 3 := by gcongr
  have hzarg : z = (sigma : ℂ) + (t : ℂ) * I := by
    apply Complex.ext
    · simp [z, w, sigma, displacedLinePt]
      ring
    · simp [z, w, t, displacedLinePt]
  have hchi' : ‖zetaChi z‖ ≤ K0 * (1 + |t|) ^ 2 := by
    rw [hzarg]
    exact hchi t
  have hderiv' : ‖deriv zetaChi z‖ ≤ K1 * (1 + |t|) ^ 3 := by
    rw [hzarg]
    exact hderiv t
  have hpow : ‖(n + 1 : ℂ) ^ (z - 1)‖ = r ^ (-(3 / 2 + d)) := by
    rw [show (n + 1 : ℂ) = (r : ℂ) by
        dsimp only [r]
        push_cast
        ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hr]
    have hre : (z - 1).re = -(3 / 2 + d) := by
      dsimp only [z, w]
      simp [displacedLinePt]
      ring
    rw [hre]
  have hlogEq : Complex.log (n + 1 : ℂ) = ((Real.log r : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_log hr.le using 1
    all_goals simp [r]
  have hlog : ‖Complex.log (n + 1 : ℂ)‖ = Real.log r := by
    rw [hlogEq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogr]
  have hxpow : ‖(x : ℂ) ^ w‖ = x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    dsimp only [w]
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero]
    norm_num
    rw [Real.rpow_neg_one]
  have hkernel := norm_smoothAFEGaussianKernel_vertical_le_of_ne
    (σ := -1) (by norm_num) v
  have hkernel' : ‖smoothAFEGaussianKernel w‖ ≤
      Real.exp 1 * Real.exp (-(v ^ 2)) := by
    dsimp only [w]
    convert hkernel using 1 <;> norm_num
  have hcore :
      ‖(deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1) +
          zetaChi z *
            ((n + 1 : ℂ) ^ (z - 1) * Complex.log (n + 1 : ℂ) * I)‖ ≤
        C * r ^ (-(3 / 2 + d)) * (1 + Real.log r) * q ^ 3 := by
    calc
      _ ≤ ‖deriv zetaChi z‖ * ‖(n + 1 : ℂ) ^ (z - 1)‖ +
          ‖zetaChi z‖ *
            (‖(n + 1 : ℂ) ^ (z - 1)‖ *
              ‖Complex.log (n + 1 : ℂ)‖) := by
            simpa only [norm_mul, norm_I, one_mul, mul_one, mul_assoc] using
              norm_add_le
                ((deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1))
                (zetaChi z *
                  ((n + 1 : ℂ) ^ (z - 1) *
                    Complex.log (n + 1 : ℂ) * I))
      _ ≤ (K1 * (1 + |t|) ^ 3) * r ^ (-(3 / 2 + d)) +
          (K0 * (1 + |t|) ^ 2) *
            (r ^ (-(3 / 2 + d)) * Real.log r) := by
            rw [hpow, hlog]
            gcongr
      _ ≤ (K1 * q ^ 3) * r ^ (-(3 / 2 + d)) +
          (K0 * q ^ 3) *
            (r ^ (-(3 / 2 + d)) * Real.log r) := by gcongr
      _ ≤ (K1 + K0) * r ^ (-(3 / 2 + d)) *
          (1 + Real.log r) * q ^ 3 := by
            have hrpow0 : 0 ≤ r ^ (-(3 / 2 + d)) := Real.rpow_nonneg hr.le _
            have hq0 : 0 ≤ q := le_trans (by norm_num) hq1
            have hq3 : 0 ≤ q ^ 3 := by positivity
            have hmissing1 :
                0 ≤ K1 * r ^ (-(3 / 2 + d)) * Real.log r * q ^ 3 := by
              positivity
            have hmissing0 :
                0 ≤ K0 * r ^ (-(3 / 2 + d)) * q ^ 3 := by
              positivity
            nlinarith
      _ = C * r ^ (-(3 / 2 + d)) *
          (1 + Real.log r) * q ^ 3 := by
            dsimp only [C]
            ring
  unfold smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
  dsimp only [z, w]
  have hcore' :
      ‖(deriv zetaChi (displacedLinePt d tau + (-1 + ↑v * I)) * I) *
            (↑n + 1) ^ (displacedLinePt d tau + (-1 + ↑v * I) - 1) +
          zetaChi (displacedLinePt d tau + (-1 + ↑v * I)) *
            ((↑n + 1) ^ (displacedLinePt d tau + (-1 + ↑v * I) - 1) *
              log (↑n + 1) * I)‖ ≤
        C * r ^ (-(3 / 2 + d)) * (1 + Real.log r) * q ^ 3 := by
    simpa only [z, w] using hcore
  have hxpow' : ‖(x : ℂ) ^ (-1 + ↑v * I)‖ = x⁻¹ := by
    simpa only [w] using hxpow
  have hkernel'' : ‖smoothAFEGaussianKernel (-1 + ↑v * I)‖ ≤
      Real.exp 1 * Real.exp (-(v ^ 2)) := by
    simpa only [w] using hkernel'
  rw [norm_mul, norm_mul]
  calc
    ‖(deriv zetaChi (displacedLinePt d tau + (-1 + ↑v * I)) * I) *
          (↑n + 1) ^ (displacedLinePt d tau + (-1 + ↑v * I) - 1) +
        zetaChi (displacedLinePt d tau + (-1 + ↑v * I)) *
          ((↑n + 1) ^ (displacedLinePt d tau + (-1 + ↑v * I) - 1) *
            log (↑n + 1) * I)‖ *
        ‖(x : ℂ) ^ (-1 + ↑v * I)‖ *
        ‖smoothAFEGaussianKernel (-1 + ↑v * I)‖
      ≤ (C * r ^ (-(3 / 2 + d)) * (1 + Real.log r) * q ^ 3) *
          x⁻¹ * (Real.exp 1 * Real.exp (-(v ^ 2))) := by
            rw [hxpow']
            gcongr
    _ = C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) *
          (1 + |tau| + |v|) ^ 3 *
          (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
            dsimp only [r, q]
            ring

theorem continuous_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    Continuous
      (smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
        d x tau n) := by
  haveI : NeZero (x : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
  let w : ℝ → ℂ := fun v => (-1 : ℂ) + (v : ℂ) * I
  let z : ℝ → ℂ := fun v => displacedLinePt d tau + w v
  have hw : Continuous w := by
    dsimp only [w]
    fun_prop
  have hz : Continuous z := continuous_const.add hw
  have hGamma : ∀ v : ℝ, Gammaℝ (1 - z v) ≠ 0 := by
    intro v
    apply Gammaℝ_ne_zero_of_re_pos
    dsimp only [z, w]
    simp [displacedLinePt]
    linarith
  have hchi : Continuous (fun v : ℝ => zetaChi (z v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact ContinuousAt.comp (x := v)
      (zetaChi_analyticAt (hGamma v)).continuousAt hz.continuousAt
  have hchi' : Continuous (fun v : ℝ => deriv zetaChi (z v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact ContinuousAt.comp (x := v)
      ((zetaChi_analyticAt (hGamma v)).deriv.continuousAt) hz.continuousAt
  have hpowN : Continuous (fun v : ℝ =>
      (n + 1 : ℂ) ^ (z v - 1)) :=
    (continuous_const_cpow (n + 1 : ℂ)).comp (hz.sub continuous_const)
  have hpowX : Continuous (fun v : ℝ => (x : ℂ) ^ (w v)) :=
    (continuous_const_cpow (x : ℂ)).comp hw
  have hwne : ∀ v : ℝ, w v ≠ 0 := by
    intro v hzero
    have hre := congrArg Complex.re hzero
    dsimp only [w] at hre
    norm_num at hre
  have hkernel : Continuous (fun v : ℝ => smoothAFEGaussianKernel (w v)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hw.pow 2)).div hw hwne
  unfold smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
  change Continuous (fun v : ℝ =>
    (((deriv zetaChi (z v) * I) * (n + 1 : ℂ) ^ (z v - 1) +
        zetaChi (z v) *
          ((n + 1 : ℂ) ^ (z v - 1) * Complex.log (n + 1 : ℂ) * I)) *
      (x : ℂ) ^ (w v)) * smoothAFEGaussianKernel (w v))
  exact ((((hchi'.mul continuous_const).mul hpowN).add
    (hchi.mul ((hpowN.mul continuous_const).mul continuous_const))).mul
      hpowX).mul hkernel

theorem smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_integrable
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    Integrable (smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
      d x tau n) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_le
      hd hdquarter hx
  let A : ℝ := C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
    (1 + Real.log (n + 1 : ℝ)) * (x⁻¹ * Real.exp 1)
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) 3).const_mul A)
  · exact (continuous_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
      hd hdquarter hx tau n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      calc
        ‖smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
            d x tau n v‖
          ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
              (1 + Real.log (n + 1 : ℝ)) *
              (1 + |tau| + |v|) ^ 3 *
              (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) :=
            hpoint tau n v
        _ = A * ((1 + |tau| + |v|) ^ 3 *
              Real.exp (-(v ^ 2))) := by
            dsimp only [A]
            ring

/-- Exact height derivative of one general reflected coefficient on a
displaced line. -/
def smoothAFEZetaDisplacedDualCoefficientHeightDerivative
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ v : ℝ,
      smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
        d x tau n v

theorem hasDerivAt_smoothAFEZetaDualCoefficientGeneral_displaced
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDualCoefficientGeneral
        (displacedLinePt d u) x n)
      (smoothAFEZetaDisplacedDualCoefficientHeightDerivative
        d x tau n) tau := by
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
      ((-1 : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative d x u n v
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_le
      hd hdquarter hx
  let A : ℝ := C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
    (1 + Real.log (n + 1 : ℝ)) * (x⁻¹ * Real.exp 1)
  let bound : ℝ → ℝ := fun v =>
    A * ((2 + |tau| + |v|) ^ 3 * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u => by
      have h0 : 0 < (displacedLinePt d u).re := by
        rw [displacedLinePt_re]
        linarith
      have h1 : (displacedLinePt d u).re < 1 := by
        rw [displacedLinePt_re]
        linarith
      exact (smoothAFEZetaReflectedTerm_general_left_one_integrable
        hx h0 h1 n).aestronglyMeasurable)
    (by
      have h0 : 0 < (displacedLinePt d tau).re := by
        rw [displacedLinePt_re]
        linarith
      have h1 : (displacedLinePt d tau).re < 1 := by
        rw [displacedLinePt_re]
        linarith
      exact smoothAFEZetaReflectedTerm_general_left_one_integrable
        hx h0 h1 n)
    (smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_integrable
      hd hdquarter hx tau n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hudist : |u - tau| < 1 := by
        have hdist := Metric.mem_ball.mp hu
        simpa only [Real.dist_eq, abs_sub_comm] using hdist
      have huabs : |u| < |tau| + 1 := by
        calc
          |u| = |(u - tau) + tau| := by ring_nf
          _ ≤ |u - tau| + |tau| := abs_add_le _ _
          _ < 1 + |tau| := by linarith
          _ = |tau| + 1 := by ring
      have hheight : 1 + |u| + |v| ≤ 2 + |tau| + |v| := by
        linarith
      have hlogn : 0 ≤ Real.log (n + 1 : ℝ) :=
        Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ n + 1 by omega))
      have hpref :
          0 ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
            (1 + Real.log (n + 1 : ℝ)) := by
        positivity
      dsimp only [F']
      calc
        ‖smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
            d x u n v‖
          ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
              (1 + Real.log (n + 1 : ℝ)) *
              (1 + |u| + |v|) ^ 3 *
              (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) :=
            hpoint u n v
        _ ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
              (1 + Real.log (n + 1 : ℝ)) *
              (2 + |tau| + |v|) ^ 3 *
              (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
            gcongr
        _ = bound v := by
            dsimp only [bound, A]
            ring)
    ((integrable_shifted_pow_mul_exp_neg_sq (2 + |tau|) 3).const_mul A)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact hasDerivAt_smoothAFEZetaReflectedTerm_displaced_left_one
        hd hdquarter u n v)
  have hcoeffEq : (fun u : ℝ =>
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d u) x n) =
      fun u : ℝ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
    funext u
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul]
    calc
      (zetaChi (displacedLinePt d u) *
            (n + 1 : ℂ) ^ (displacedLinePt d u - 1)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand (displacedLinePt d u)
              (1 / ((n + 1 : ℝ) * x))
              (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ((zetaChi (displacedLinePt d u) *
              (n + 1 : ℂ) ^ (displacedLinePt d u - 1)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand (displacedLinePt d u)
              (1 / ((n + 1 : ℝ) * x))
              (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ, smoothAFEZetaReflectedTerm
            (displacedLinePt d u) x n
              ((-1 : ℂ) + (v : ℂ) * I) := by
        rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx]
        · norm_num
        · rw [displacedLinePt_re]
          linarith
        · rw [displacedLinePt_re]
          linarith
  rw [hcoeffEq]
  unfold smoothAFEZetaDisplacedDualCoefficientHeightDerivative
  exact hparam.2.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

/-- Uniform summable envelope for the differentiated reflected
coefficients. Height dependence is only cubic. -/
theorem exists_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative_le
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n‖ ≤
        K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) * (1 + |tau|) ^ 3 := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative_le
      hd hdquarter hx
  let G : ℝ := ∫ v : ℝ,
    (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))
  let K : ℝ := (1 / (2 * Real.pi)) * C *
    (x⁻¹ * Real.exp 1) * G
  have hgauss : Integrable (fun v : ℝ =>
      (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
    integrable_shifted_pow_mul_exp_neg_sq 1 3
  have hG : 0 ≤ G := integral_nonneg fun _ => by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun tau n => ?_⟩
  let D : ℝ := C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
    (1 + Real.log (n + 1 : ℝ)) * (1 + |tau|) ^ 3 *
    (x⁻¹ * Real.exp 1)
  have hlogn : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hdom : Integrable (fun v : ℝ =>
      D * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2)))) :=
    hgauss.const_mul D
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
            d x tau n v‖ ≤ D * G := by
    have hint0 := norm_integral_le_of_norm_le hdom
      (Filter.Eventually.of_forall fun v => by
        have hprod :
            1 + |tau| + |v| ≤ (1 + |tau|) * (1 + |v|) := by
          nlinarith [abs_nonneg tau, abs_nonneg v,
            mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
        have hpow :
            (1 + |tau| + |v|) ^ 3 ≤
              (1 + |tau|) ^ 3 * (1 + |v|) ^ 3 := by
          rw [← mul_pow]
          gcongr
        calc
          ‖smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
              d x tau n v‖
            ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
                (1 + Real.log (n + 1 : ℝ)) *
                (1 + |tau| + |v|) ^ 3 *
                (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) :=
              hpoint tau n v
          _ ≤ C * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
                (1 + Real.log (n + 1 : ℝ)) *
                ((1 + |tau|) ^ 3 * (1 + |v|) ^ 3) *
                (x⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
              gcongr
          _ = D * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
              dsimp only [D]
              ring)
    calc
      ‖∫ v : ℝ,
          smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
            d x tau n v‖
        ≤ ∫ v : ℝ, D *
            ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := hint0
      _ = D * G := by
        rw [integral_const_mul]
  unfold smoothAFEZetaDisplacedDualCoefficientHeightDerivative
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ v : ℝ,
          smoothAFEZetaDisplacedReflectedIntegrandHeightDerivative
            d x tau n v‖
      ≤ (1 / (2 * Real.pi)) * (D * G) := by gcongr
    _ = K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) * (1 + |tau|) ^ 3 := by
      dsimp only [D, K]
      ring

private theorem summable_displaced_left_edge_log_majorant
    {d : ℝ} (hd : 0 < d) :
    Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
        (1 + Real.log (n + 1 : ℝ))) := by
  have hp : 1 < 3 / 2 + d := by linarith
  have hzero := summable_log_natCast_pow_mul_rpow_neg 0 hp
  have hone := summable_log_natCast_pow_mul_rpow_neg 1 hp
  have hzeroShift := (summable_nat_add_iff 1).2 hzero
  have honeShift := (summable_nat_add_iff 1).2 hone
  refine (hzeroShift.add honeShift).congr fun n => ?_
  norm_num [Nat.cast_add]
  ring

theorem summable_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative
        d x tau n‖) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative_le
      hd hdquarter hx
  let A : ℝ := K * (1 + |tau|) ^ 3
  have hmajor : Summable (fun n : ℕ =>
      A * ((n + 1 : ℝ) ^ (-(3 / 2 + d)) *
        (1 + Real.log (n + 1 : ℝ)))) :=
    (summable_displaced_left_edge_log_majorant hd).mul_left A
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmajor
  calc
    ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n‖
      ≤ K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) * (1 + |tau|) ^ 3 :=
        hbound tau n
    _ = A * ((n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ))) := by
      dsimp only [A]
      ring

theorem hasDerivAt_tsum_smoothAFEZetaDualCoefficientGeneral_displaced
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral (displacedLinePt d u) x n)
      (∑' n : ℕ,
        smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n) tau := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualCoefficientHeightDerivative_le
      hd hdquarter hx
  let M : ℕ → ℝ := fun n =>
    K * ((n + 1 : ℝ) ^ (-(3 / 2 + d)) *
      (1 + Real.log (n + 1 : ℝ))) * (2 + |tau|) ^ 3
  have hMs : Summable M := by
    have h := (summable_displaced_left_edge_log_majorant hd).mul_left
      (K * (2 + |tau|) ^ 3)
    refine h.congr fun n => ?_
    dsimp only [M]
    ring
  have hg : ∀ n : ℕ, ∀ u ∈ Set.Ioo (tau - 1) (tau + 1),
      HasDerivAt
        (fun y : ℝ => smoothAFEZetaDualCoefficientGeneral
          (displacedLinePt d y) x n)
        (smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x u n) u := by
    intro n u hu
    exact hasDerivAt_smoothAFEZetaDualCoefficientGeneral_displaced
      hd hdquarter hx u n
  have hg' : ∀ n : ℕ, ∀ u ∈ Set.Ioo (tau - 1) (tau + 1),
      ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x u n‖ ≤
        M n := by
    intro n u hu
    have hudist : |u - tau| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    have huabs : |u| < |tau| + 1 := by
      calc
        |u| = |(u - tau) + tau| := by ring_nf
        _ ≤ |u - tau| + |tau| := abs_add_le _ _
        _ < 1 + |tau| := by linarith
        _ = |tau| + 1 := by ring
    have hheight : 1 + |u| ≤ 2 + |tau| := by linarith
    have hlogn : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ n + 1 by omega))
    have hpref :
        0 ≤ K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
          (1 + Real.log (n + 1 : ℝ)) := by
      positivity
    calc
      ‖smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x u n‖
        ≤ K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
            (1 + Real.log (n + 1 : ℝ)) * (1 + |u|) ^ 3 :=
          hbound u n
      _ ≤ K * (n + 1 : ℝ) ^ (-(3 / 2 + d)) *
            (1 + Real.log (n + 1 : ℝ)) * (2 + |tau|) ^ 3 := by
          gcongr
      _ = M n := by
          dsimp only [M]
          ring
  have hy : tau ∈ Set.Ioo (tau - 1) (tau + 1) := by constructor <;> linarith
  have hsum0 : Summable (fun n : ℕ =>
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d tau) x n) := by
    have h0 : 0 < (displacedLinePt d tau).re := by
      rw [displacedLinePt_re]
      linarith
    have h1 : (displacedLinePt d tau).re < 1 := by
      rw [displacedLinePt_re]
      linarith
    obtain ⟨C, hC, hcoeff⟩ :=
      exists_norm_smoothAFEZetaDualCoefficientGeneral_le hx h0 h1
    have hbase := summable_smoothAFEZetaMajorant
      (p := 2 - (displacedLinePt d tau).re) (by linarith)
    exact Summable.of_norm_bounded (hbase.mul_left C) hcoeff
  exact hasDerivAt_tsum_of_isPreconnected hMs isOpen_Ioo
    Set.ordConnected_Ioo.isPreconnected hg hg' hy hsum0 hy

/-- The complete reflected Mellin edge differentiates to the absolutely
summable coefficient derivative series. -/
theorem hasDerivAt_smoothAFEZetaDualMellinGeneral_displaced
    {d x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDualMellinGeneral
        (displacedLinePt d u) x)
      (∑' n : ℕ,
        smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n) tau := by
  have hseries :=
    hasDerivAt_tsum_smoothAFEZetaDualCoefficientGeneral_displaced
      hd hdquarter hx tau
  have heq : (fun u : ℝ => smoothAFEZetaDualMellinGeneral
      (displacedLinePt d u) x) =
      fun u : ℝ => ∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral (displacedLinePt d u) x n := by
    funext u
    exact smoothAFEZetaDualMellinGeneral_eq_tsum hx
      (by rw [displacedLinePt_re]; linarith)
      (by rw [displacedLinePt_re]; linarith)
  rw [heq]
  exact hseries

end RHTower
