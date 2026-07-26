import GaloisForLFunctions.RHTower.DeningerArithmeticArchimedean
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomEdge

open Complex Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A complex positive-real-part resolvent is a bounded multiplier on Deninger's Euler line. -/
theorem integrable_deningerTimeTestLaplace_mul_complexVerticalResolvent
    (φ : DeningerTimeTestFunction) (c : ℝ)
    {a : ℂ} (ha : 0 < a.re) :
    Integrable
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            ((c : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          (a -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I)⁻¹) := by
  let F : ℝ → ℂ :=
    fun ξ =>
      deningerTimeTestLaplace φ
        ((c : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I)
  let d : ℝ → ℂ :=
    fun ξ =>
      (a -
        ((2 * Real.pi * ξ : ℝ) : ℂ) *
          Complex.I)⁻¹
  have hF : Integrable F := by
    rw [show F =
        𝓕 (deningerExponentiallyTiltedTimeTest φ c) by
      funext ξ
      exact
        (fourier_deningerExponentiallyTiltedTimeTest
          φ c ξ).symm]
    exact
      integrable_fourier_deningerExponentiallyTiltedTimeTest
        φ c
  have hdenne : ∀ ξ : ℝ,
      a -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I ≠ 0 := by
    intro ξ h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    linarith
  have hdcont : Continuous d := by
    dsimp only [d]
    exact
      (by fun_prop :
        Continuous
          (fun ξ : ℝ =>
            a -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)).inv₀ hdenne
  have hdbound : ∀ ξ : ℝ, ‖d ξ‖ ≤ 1 / a.re := by
    intro ξ
    have hre :
        a.re ≤
          ‖a -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I‖ := by
      have h :=
        Complex.re_le_norm
          (a -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I)
      simpa [Complex.mul_re] using h
    dsimp only [d]
    rw [norm_inv]
    simpa only [one_div] using
      one_div_le_one_div_of_le ha hre
  simpa only [F, d] using
    hF.mul_bdd hdcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdbound)

/--
Complex Bromwich identity:
`∫ Φ(c-2πiξ)/(a-2πiξ) dξ = Φ(c-a)` whenever `Re a > 0`.
-/
theorem integral_deningerTimeTestLaplace_mul_complexVerticalResolvent
    (φ : DeningerTimeTestFunction) (c : ℝ)
    {a : ℂ} (ha : 0 < a.re) :
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            ((c : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          (a -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I)⁻¹) =
      deningerTimeTestLaplace φ ((c : ℂ) - a) := by
  let F : ℝ → ℂ :=
    fun ξ =>
      deningerTimeTestLaplace φ
        ((c : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I)
  let e : ℝ → ℂ :=
    (Ioi (0 : ℝ)).indicator
      (fun t : ℝ =>
        Complex.exp (-a * (t : ℂ)))
  let K : ℝ × ℝ → ℂ :=
    fun p =>
      Complex.exp
          (((2 * Real.pi * p.2 * p.1 : ℝ) : ℂ) *
            Complex.I) *
        (e p.1 * F p.2)
  have he : Integrable e := by
    dsimp only [e]
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_mul_complex_Ioi
      (a := -a)
      (by
        simp only [Complex.neg_re]
        linarith)
      0
  have hF : Integrable F := by
    rw [show F =
        𝓕 (deningerExponentiallyTiltedTimeTest φ c) by
      funext ξ
      exact
        (fourier_deningerExponentiallyTiltedTimeTest
          φ c ξ).symm]
    exact
      integrable_fourier_deningerExponentiallyTiltedTimeTest
        φ c
  have hbase :
      Integrable
        (fun p : ℝ × ℝ => e p.1 * F p.2) :=
    he.mul_prod hF
  have hK : Integrable K := by
    dsimp only [K]
    refine hbase.norm.mono' ?_ ?_
    · exact
        (Complex.continuous_exp.comp
          (by fun_prop)).aestronglyMeasurable.mul
            hbase.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, Complex.norm_exp]
      have hre :
          ((((2 * Real.pi * p.2 * p.1 : ℝ) : ℂ) *
            Complex.I)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero, one_mul]
  have hresolvent : ∀ ξ : ℝ,
      (a -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I)⁻¹ =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-a * (t : ℂ)) *
            Complex.exp
              (((2 * Real.pi * ξ * t : ℝ) : ℂ) *
                Complex.I) := by
    intro ξ
    let q : ℂ :=
      -(a -
        ((2 * Real.pi * ξ : ℝ) : ℂ) *
          Complex.I)
    have hq : q.re < 0 := by
      dsimp only [q]
      simp [Complex.mul_re]
      exact ha
    have hfun :
        (fun t : ℝ =>
          Complex.exp (-a * (t : ℂ)) *
            Complex.exp
              (((2 * Real.pi * ξ * t : ℝ) : ℂ) *
                Complex.I)) =
          fun t : ℝ =>
            Complex.exp (q * (t : ℂ)) := by
      funext t
      rw [← Complex.exp_add]
      congr 1
      dsimp only [q]
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex_Ioi hq 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [q]
    rw [show
        -(a -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I) =
          -1 *
            (a -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) by
      ring]
    field_simp
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            ((c : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          (a -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I)⁻¹) =
        fun ξ : ℝ =>
          F ξ *
            ∫ t : ℝ in Ioi 0,
              Complex.exp (-a * (t : ℂ)) *
                Complex.exp
                  (((2 * Real.pi * ξ * t : ℝ) : ℂ) *
                    Complex.I) by
    funext ξ
    rw [hresolvent ξ]]
  calc
    (∫ ξ : ℝ,
        F ξ *
          ∫ t : ℝ in Ioi 0,
            Complex.exp (-a * (t : ℂ)) *
              Complex.exp
                (((2 * Real.pi * ξ * t : ℝ) : ℂ) *
                  Complex.I)) =
        ∫ ξ : ℝ, ∫ t : ℝ, K (t, ξ) := by
      congr with ξ
      rw [← integral_indicator measurableSet_Ioi]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [K, e, Set.indicator_of_mem ht]
        ring
      · simp [K, e, ht]
    _ = ∫ t : ℝ, ∫ ξ : ℝ, K (t, ξ) := by
      apply integral_integral_swap
      simpa only [Function.comp_apply] using hK.swap
    _ = ∫ t : ℝ,
        Complex.exp (-a * (t : ℂ)) *
          deningerExponentiallyTiltedTimeTest φ c t := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [show
          (fun ξ : ℝ => K (t, ξ)) =
            fun ξ : ℝ =>
              Complex.exp (-a * (t : ℂ)) *
                (Complex.exp
                    (((2 * Real.pi * ξ * t : ℝ) : ℂ) *
                      Complex.I) *
                  F ξ) by
          funext ξ
          dsimp only [K]
          rw [show
              e t =
                Complex.exp
                  (-a * (t : ℂ)) by
            simp [e, ht]]
          ring]
        rw [integral_const_mul,
          integral_fourierKernel_mul_deningerTimeTestLaplace]
      · have ht0 : t ≤ 0 := le_of_not_gt ht
        have hφ :
            φ t = 0 :=
          deningerTimeTest_eq_zero_of_nonpos φ ht0
        have he0 : e t = 0 :=
          Set.indicator_of_notMem ht _
        simp [K, he0,
          deningerExponentiallyTiltedTimeTest, hφ]
    _ = deningerTimeTestLaplace φ
        ((c : ℂ) - a) := by
      rw [deningerTimeTestLaplace]
      apply integral_congr_ae
      filter_upwards with t
      rw [deningerExponentiallyTiltedTimeTest]
      calc
        Complex.exp (-a * (t : ℂ)) *
            ((φ t : ℂ) *
              Complex.exp ((c * t : ℝ) : ℂ)) =
          (φ t : ℂ) *
            (Complex.exp (-a * (t : ℂ)) *
              Complex.exp ((c * t : ℝ) : ℂ)) := by
          ring
        _ = (φ t : ℂ) *
            Complex.exp
              (-a * (t : ℂ) +
                ((c * t : ℝ) : ℂ)) := by
          rw [Complex.exp_add]
        _ = (φ t : ℂ) *
            Complex.exp
              ((t : ℂ) * ((c : ℂ) - a)) := by
          congr 1
          push_cast
          ring

noncomputable def deningerXiRightEulerLineSchwartz
    (φ : DeningerTimeTestFunction) : SchwartzMap ℝ ℂ :=
  𝓕 (deningerExponentiallyTiltedTimeSchwartz φ (3 / 2))

@[simp]
theorem deningerXiRightEulerLineSchwartz_apply
    (φ : DeningerTimeTestFunction) (ξ : ℝ) :
    deningerXiRightEulerLineSchwartz φ ξ =
      deningerTimeTestLaplace φ
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  change
    (𝓕 (deningerExponentiallyTiltedTimeSchwartz φ (3 / 2)) :
      SchwartzMap ℝ ℂ) ξ = _
  rw [SchwartzMap.fourier_coe]
  change
    𝓕 (deningerExponentiallyTiltedTimeTest φ (3 / 2)) ξ = _
  rw [fourier_deningerExponentiallyTiltedTimeTest]

def deningerXiRightEulerPoint (ξ : ℝ) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) -
    ((2 * Real.pi * ξ : ℝ) : ℂ) * I

def deningerXiRightCenteredLine (ξ : ℝ) : ℂ :=
  (deningerXiRightEulerPoint ξ - 1 / 2) * (-I)

@[simp]
theorem deningerXiRightEulerPoint_re (ξ : ℝ) :
    (deningerXiRightEulerPoint ξ).re = 3 / 2 := by
  simp [deningerXiRightEulerPoint, Complex.mul_re]

theorem deningerXiRightCenteredLine_affine (ξ : ℝ) :
    deningerXiRightCenteredLine ξ =
      -((2 * Real.pi * ξ : ℝ) : ℂ) - I := by
  apply Complex.ext
  · simp [deningerXiRightCenteredLine,
      deningerXiRightEulerPoint,
      Complex.mul_re]
  · simp [deningerXiRightCenteredLine,
      deningerXiRightEulerPoint,
      Complex.mul_im]
    ring

theorem deningerXiRightCenteredLine_inverse (ξ : ℝ) :
    1 / 2 +
        deningerXiRightCenteredLine ξ * I =
      deningerXiRightEulerPoint ξ := by
  unfold deningerXiRightCenteredLine
  have hI : (-I) * I = 1 := by
    calc
      (-I) * I = -(I * I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; ring
  rw [mul_assoc, hI]
  ring

theorem XiC_deningerXiRightCenteredLine_ne_zero
    (ξ : ℝ) :
    XiC (deningerXiRightCenteredLine ξ) ≠ 0 := by
  have hxi :
      xi (deningerXiRightEulerPoint ξ) ≠ 0 :=
    xi_ne_zero_of_one_lt_re (by
      rw [deningerXiRightEulerPoint_re]
      norm_num)
  simpa only [XiC,
    deningerXiRightCenteredLine_inverse] using hxi

theorem half_le_norm_xiSpectralPoint_sub_deningerXiRightCenteredLine
    (q : XiZeroCopy) (ξ : ℝ) :
    (1 / 2 : ℝ) ≤
      ‖xiSpectralPoint q -
        deningerXiRightCenteredLine ξ‖ := by
  let ρ : ℂ := deningerRawThetaEigen q
  let s : ℂ := deningerXiRightEulerPoint ξ
  have hdiff :
      xiSpectralPoint q -
          deningerXiRightCenteredLine ξ =
        (ρ - s) * (-I) := by
    dsimp only [ρ, s, deningerRawThetaEigen,
      deningerXiRightCenteredLine,
      deningerXiRightEulerPoint, xiSpectralPoint]
    ring
  have hρ := deningerRawThetaEigen_re_mem_open_unit q
  have hsre : s.re = 3 / 2 :=
    deningerXiRightEulerPoint_re ξ
  rw [hdiff, norm_mul, norm_neg, Complex.norm_I, mul_one]
  calc
    (1 / 2 : ℝ) ≤ |(ρ - s).re| := by
      have hneg : (ρ - s).re ≤ 0 := by
        simp only [sub_re, hsre]
        linarith
      rw [abs_of_nonpos hneg]
      simp only [sub_re, hsre]
      linarith
    _ ≤ ‖ρ - s‖ := Complex.abs_re_le_norm _

theorem xiRelativeResolventTerm_deningerXiRightCenteredLine_eq
    (q : XiZeroCopy) (ξ : ℝ) :
    xiRelativeResolventTerm
        (deningerXiRightCenteredLine ξ) q =
      -deningerXiRightCenteredLine ξ /
        (xiSpectralPoint q *
          (xiSpectralPoint q -
            deningerXiRightCenteredLine ξ)) := by
  have ha : xiSpectralPoint q ≠ 0 :=
    xiSpectralPoint_ne_zero q
  have haz :
      xiSpectralPoint q -
          deningerXiRightCenteredLine ξ ≠ 0 := by
    intro h
    have hn :=
      half_le_norm_xiSpectralPoint_sub_deningerXiRightCenteredLine
        q ξ
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [xiRelativeResolventTerm, inv_eq_one_div]
  field_simp [ha, haz]
  ring

theorem norm_xiRelativeResolventTerm_deningerXiRightCenteredLine_le
    (q : XiZeroCopy) (ξ : ℝ) :
    ‖xiRelativeResolventTerm
        (deningerXiRightCenteredLine ξ) q‖ ≤
      (‖deningerXiRightCenteredLine ξ‖ +
          2 * ‖deningerXiRightCenteredLine ξ‖ ^ 2) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let x : ℝ := ‖deningerXiRightCenteredLine ξ‖
  let A : ℝ := ‖xiSpectralPoint q‖
  let d : ℝ :=
    ‖xiSpectralPoint q -
      deningerXiRightCenteredLine ξ‖
  have hx : 0 ≤ x := norm_nonneg _
  have hA : 0 < A :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hd :
      0 < d :=
    lt_of_lt_of_le (by norm_num)
      (half_le_norm_xiSpectralPoint_sub_deningerXiRightCenteredLine
        q ξ)
  have hdhalf : 1 / 2 ≤ d :=
    half_le_norm_xiSpectralPoint_sub_deningerXiRightCenteredLine
      q ξ
  have htri : A ≤ d + x := by
    dsimp only [A, d, x]
    calc
      ‖xiSpectralPoint q‖ =
          ‖(xiSpectralPoint q -
              deningerXiRightCenteredLine ξ) +
            deningerXiRightCenteredLine ξ‖ := by
        congr 1
        ring
      _ ≤
          ‖xiSpectralPoint q -
              deningerXiRightCenteredLine ξ‖ +
            ‖deningerXiRightCenteredLine ξ‖ :=
        norm_add_le _ _
  have hcore :
      x * A ≤ (x + 2 * x ^ 2) * d := by
    have hxtri :
        x * A ≤ x * (d + x) :=
      mul_le_mul_of_nonneg_left htri hx
    have hxd :
        x ^ 2 ≤ 2 * x ^ 2 * d := by
      nlinarith [sq_nonneg x]
    nlinarith
  rw [
    xiRelativeResolventTerm_deningerXiRightCenteredLine_eq,
    norm_div, norm_neg, norm_mul]
  change x / (A * d) ≤
    (x + 2 * x ^ 2) * (1 / A ^ 2)
  rw [one_div, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (mul_pos hA hd) (pow_pos hA 2)]
  have hmul :=
    mul_le_mul_of_nonneg_left hcore hA.le
  nlinarith

def deningerXiRightRelativeMajorant
    (φ : DeningerTimeTestFunction) (ξ : ℝ) : ℝ :=
  ‖deningerXiRightEulerLineSchwartz φ ξ‖ *
    (‖deningerXiRightCenteredLine ξ‖ +
      2 * ‖deningerXiRightCenteredLine ξ‖ ^ 2)

theorem integrable_deningerXiRightRelativeMajorant
    (φ : DeningerTimeTestFunction) :
    Integrable (deningerXiRightRelativeMajorant φ) := by
  let F : SchwartzMap ℝ ℂ :=
    deningerXiRightEulerLineSchwartz φ
  let z : ℝ → ℂ := deningerXiRightCenteredLine
  have hz : z.HasTemperateGrowth := by
    rw [show z =
        fun ξ : ℝ =>
          -((2 * Real.pi * ξ : ℝ) : ℂ) - I by
      funext ξ
      exact deningerXiRightCenteredLine_affine ξ]
    fun_prop
  let G₁ : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ z F
  let z₂ : ℝ → ℂ := fun ξ => z ξ ^ 2
  have hz₂ : z₂.HasTemperateGrowth := by
    dsimp only [z₂]
    fun_prop
  let G₂ : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ z₂ F
  have hG₁ :
      Integrable
        (fun ξ : ℝ => ‖z ξ * F ξ‖) := by
    have h : Integrable (fun ξ : ℝ => ‖G₁ ξ‖) :=
      G₁.integrable.norm
    rw [show
        (fun ξ : ℝ => ‖G₁ ξ‖) =
          fun ξ : ℝ => ‖z ξ * F ξ‖ by
      funext ξ
      dsimp only [G₁]
      rw [SchwartzMap.smulLeftCLM_apply_apply hz]
      rfl] at h
    exact h
  have hG₂ :
      Integrable
        (fun ξ : ℝ => ‖z ξ ^ 2 * F ξ‖) := by
    have h : Integrable (fun ξ : ℝ => ‖G₂ ξ‖) :=
      G₂.integrable.norm
    rw [show
        (fun ξ : ℝ => ‖G₂ ξ‖) =
          fun ξ : ℝ => ‖z ξ ^ 2 * F ξ‖ by
      funext ξ
      dsimp only [G₂]
      rw [SchwartzMap.smulLeftCLM_apply_apply hz₂]
      rfl] at h
    exact h
  have hsum :=
    hG₁.add (hG₂.const_mul 2)
  rw [show
      deningerXiRightRelativeMajorant φ =
        fun ξ : ℝ =>
          ‖z ξ * F ξ‖ +
            2 * ‖z ξ ^ 2 * F ξ‖ by
    funext ξ
    rw [deningerXiRightRelativeMajorant,
      norm_mul, norm_mul, norm_pow]
    dsimp only [F, z]
    ring]
  exact hsum

def deningerXiRightSpectralRawIntegrand
    (φ : DeningerTimeTestFunction)
    (q : XiZeroCopy) (ξ : ℝ) : ℂ :=
  deningerXiRightEulerLineSchwartz φ ξ *
    (-I *
      xiRelativeResolventTerm
        (deningerXiRightCenteredLine ξ) q)

theorem neg_I_mul_xiRelativeResolventTerm_deningerXiRight_eq
    (q : XiZeroCopy) (ξ : ℝ) :
    -I *
        xiRelativeResolventTerm
          (deningerXiRightCenteredLine ξ) q =
      (deningerRawThetaEigen q - 1 / 2)⁻¹ +
        (deningerXiRightEulerPoint ξ -
          deningerRawThetaEigen q)⁻¹ := by
  have hhalf :
      deningerRawThetaEigen q - 1 / 2 ≠ 0 := by
    dsimp only [deningerRawThetaEigen]
    exact sub_ne_zero.mpr
      (xi_divisor_support_ne_half q.1)
  have hline :
      deningerXiRightEulerPoint ξ -
          deningerRawThetaEigen q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [sub_re, deningerXiRightEulerPoint_re] at hre
    norm_num at hre
    have hρ := deningerRawThetaEigen_re_mem_open_unit q
    linarith
  have haeq :
      xiSpectralPoint q =
        (deningerRawThetaEigen q - 1 / 2) * (-I) := by
    rfl
  have hdiffeq :
      xiSpectralPoint q -
          deningerXiRightCenteredLine ξ =
        (deningerXiRightEulerPoint ξ -
          deningerRawThetaEigen q) * I := by
    rw [haeq]
    unfold deningerXiRightCenteredLine
    ring
  rw [xiRelativeResolventTerm, hdiffeq, haeq]
  field_simp [hhalf, hline, Complex.I_ne_zero]
  ring

theorem integrable_deningerXiRightSpectralRawIntegrand
    (φ : DeningerTimeTestFunction)
    (q : XiZeroCopy) :
    Integrable
      (deningerXiRightSpectralRawIntegrand φ q) := by
  let F : ℝ → ℂ :=
    fun ξ => deningerXiRightEulerLineSchwartz φ ξ
  let C : ℂ :=
    (deningerRawThetaEigen q - 1 / 2)⁻¹
  have hF : Integrable F := by
    exact
      (deningerXiRightEulerLineSchwartz φ).integrable
  have ha :
      0 <
        (((((3 / 2 : ℝ) : ℂ)) -
          deningerRawThetaEigen q).re) := by
    have hρ := deningerRawThetaEigen_re_mem_open_unit q
    norm_num [Complex.sub_re]
    linarith
  have hres :
      Integrable
        (fun ξ : ℝ =>
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) := by
    have h :=
      integrable_deningerTimeTestLaplace_mul_complexVerticalResolvent
        φ (3 / 2) ha
    rw [show
        (fun ξ : ℝ =>
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) =
          fun ξ : ℝ =>
            deningerTimeTestLaplace φ
                (((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
              ((((3 / 2 : ℝ) : ℂ) -
                  deningerRawThetaEigen q) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ by
      funext ξ
      dsimp only [F]
      rw [deningerXiRightEulerLineSchwartz_apply]
      dsimp only [deningerXiRightEulerPoint]
      congr 1
      ring]
    exact h
  rw [show
      deningerXiRightSpectralRawIntegrand φ q =
        fun ξ : ℝ =>
          F ξ * C +
            F ξ *
              (deningerXiRightEulerPoint ξ -
                deningerRawThetaEigen q)⁻¹ by
    funext ξ
    rw [deningerXiRightSpectralRawIntegrand,
      neg_I_mul_xiRelativeResolventTerm_deningerXiRight_eq]
    dsimp only [F, C]
    ring]
  exact (hF.mul_const C).add hres

theorem integral_deningerXiRightSpectralRawIntegrand
    (φ : DeningerTimeTestFunction)
    (q : XiZeroCopy) :
    (∫ ξ : ℝ,
        deningerXiRightSpectralRawIntegrand φ q ξ) =
      deningerTimeTestLaplace φ
        (deningerRawThetaEigen q) := by
  let F : ℝ → ℂ :=
    fun ξ => deningerXiRightEulerLineSchwartz φ ξ
  let C : ℂ :=
    (deningerRawThetaEigen q - 1 / 2)⁻¹
  have hF : Integrable F := by
    exact
      (deningerXiRightEulerLineSchwartz φ).integrable
  have ha :
      0 <
        (((((3 / 2 : ℝ) : ℂ)) -
          deningerRawThetaEigen q).re) := by
    have hρ := deningerRawThetaEigen_re_mem_open_unit q
    norm_num [Complex.sub_re]
    linarith
  have hres :
      Integrable
        (fun ξ : ℝ =>
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) := by
    have h :=
      integrable_deningerTimeTestLaplace_mul_complexVerticalResolvent
        φ (3 / 2) ha
    rw [show
        (fun ξ : ℝ =>
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) =
          fun ξ : ℝ =>
            deningerTimeTestLaplace φ
                (((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
              ((((3 / 2 : ℝ) : ℂ) -
                  deningerRawThetaEigen q) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ by
      funext ξ
      dsimp only [F]
      rw [deningerXiRightEulerLineSchwartz_apply]
      dsimp only [deningerXiRightEulerPoint]
      congr 1
      ring]
    exact h
  have hzero :
      (∫ ξ : ℝ, F ξ) = 0 := by
    simpa only [F,
      deningerXiRightEulerLineSchwartz_apply] using
      integral_deningerTimeTestLaplace_fourierLine_eq_zero
        φ (3 / 2)
  have hresValue :
      (∫ ξ : ℝ,
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) =
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q) := by
    have h :=
      integral_deningerTimeTestLaplace_mul_complexVerticalResolvent
        φ (3 / 2) ha
    rw [show
        (fun ξ : ℝ =>
          F ξ *
            (deningerXiRightEulerPoint ξ -
              deningerRawThetaEigen q)⁻¹) =
          fun ξ : ℝ =>
            deningerTimeTestLaplace φ
                (((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
              ((((3 / 2 : ℝ) : ℂ) -
                  deningerRawThetaEigen q) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ by
      funext ξ
      dsimp only [F]
      rw [deningerXiRightEulerLineSchwartz_apply]
      dsimp only [deningerXiRightEulerPoint]
      congr 1
      ring]
    simpa only [show
        (((3 / 2 : ℝ) : ℂ) -
          (((3 / 2 : ℝ) : ℂ) -
            deningerRawThetaEigen q)) =
            deningerRawThetaEigen q by ring] using h
  rw [show
      deningerXiRightSpectralRawIntegrand φ q =
        fun ξ : ℝ =>
          F ξ * C +
            F ξ *
              (deningerXiRightEulerPoint ξ -
                deningerRawThetaEigen q)⁻¹ by
    funext ξ
    rw [deningerXiRightSpectralRawIntegrand,
      neg_I_mul_xiRelativeResolventTerm_deningerXiRight_eq]
    dsimp only [F, C]
    ring,
    integral_add (hF.mul_const C) hres,
    integral_mul_const,
    hzero,
    zero_mul,
    zero_add,
    hresValue]

theorem norm_deningerXiRightSpectralRawIntegrand_le
    (φ : DeningerTimeTestFunction)
    (q : XiZeroCopy) (ξ : ℝ) :
    ‖deningerXiRightSpectralRawIntegrand φ q ξ‖ ≤
      deningerXiRightRelativeMajorant φ ξ *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  rw [deningerXiRightSpectralRawIntegrand,
    norm_mul, norm_mul, norm_neg, Complex.norm_I,
    one_mul, deningerXiRightRelativeMajorant]
  have h :=
    mul_le_mul_of_nonneg_left
      (norm_xiRelativeResolventTerm_deningerXiRightCenteredLine_le
        q ξ)
      (norm_nonneg
        (deningerXiRightEulerLineSchwartz φ ξ))
  calc
    ‖deningerXiRightEulerLineSchwartz φ ξ‖ *
        ‖xiRelativeResolventTerm
          (deningerXiRightCenteredLine ξ) q‖ ≤
      ‖deningerXiRightEulerLineSchwartz φ ξ‖ *
        ((‖deningerXiRightCenteredLine ξ‖ +
            2 * ‖deningerXiRightCenteredLine ξ‖ ^ 2) *
          (1 / ‖xiSpectralPoint q‖ ^ 2)) := h
    _ =
      ‖deningerXiRightEulerLineSchwartz φ ξ‖ *
          (‖deningerXiRightCenteredLine ξ‖ +
            2 * ‖deningerXiRightCenteredLine ξ‖ ^ 2) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem integral_norm_deningerXiRightSpectralRawIntegrand_le
    (φ : DeningerTimeTestFunction)
    (q : XiZeroCopy) :
    (∫ ξ : ℝ,
        ‖deningerXiRightSpectralRawIntegrand φ q ξ‖) ≤
      (∫ ξ : ℝ,
        deningerXiRightRelativeMajorant φ ξ) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have hraw :=
    integrable_deningerXiRightSpectralRawIntegrand
      φ q
  have hmajor :=
    integrable_deningerXiRightRelativeMajorant φ
  calc
    (∫ ξ : ℝ,
        ‖deningerXiRightSpectralRawIntegrand φ q ξ‖) ≤
      ∫ ξ : ℝ,
        deningerXiRightRelativeMajorant φ ξ *
          (1 / ‖xiSpectralPoint q‖ ^ 2) :=
      integral_mono hraw.norm
        (hmajor.mul_const _) fun ξ =>
          norm_deningerXiRightSpectralRawIntegrand_le
            φ q ξ
    _ =
      (∫ ξ : ℝ,
        deningerXiRightRelativeMajorant φ ξ) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      rw [integral_mul_const]

theorem summable_integral_norm_deningerXiRightSpectralRawIntegrand
    (φ : DeningerTimeTestFunction) :
    Summable
      (fun q : XiZeroCopy =>
        ∫ ξ : ℝ,
          ‖deningerXiRightSpectralRawIntegrand
            φ q ξ‖) := by
  let J : ℝ :=
    ∫ ξ : ℝ,
      deningerXiRightRelativeMajorant φ ξ
  have hbase :
      Summable
        (fun q : XiZeroCopy =>
          J * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left J
  exact hbase.of_nonneg_of_le
    (fun q => integral_nonneg fun _ => norm_nonneg _)
    (fun q => by
      simpa only [J] using
        integral_norm_deningerXiRightSpectralRawIntegrand_le
          φ q)

theorem tsum_deningerXiRightSpectralRawIntegrand
    (φ : DeningerTimeTestFunction) (ξ : ℝ) :
    (∑' q : XiZeroCopy,
        deningerXiRightSpectralRawIntegrand φ q ξ) =
      deningerTimeTestLaplace φ
          (deningerXiRightEulerPoint ξ) *
        logDeriv xi
          (deningerXiRightEulerPoint ξ) := by
  let F : ℂ :=
    deningerXiRightEulerLineSchwartz φ ξ
  let z : ℂ :=
    deningerXiRightCenteredLine ξ
  have hXi : XiC z ≠ 0 := by
    exact XiC_deningerXiRightCenteredLine_ne_zero ξ
  rw [show
      (fun q : XiZeroCopy =>
        deningerXiRightSpectralRawIntegrand φ q ξ) =
        fun q : XiZeroCopy =>
          (F * (-I)) *
            xiRelativeResolventTerm z q by
    funext q
    unfold deningerXiRightSpectralRawIntegrand
    dsimp only [F, z]
    ring,
    tsum_mul_left]
  change
    (F * (-I)) * xiRelativeResolventTrace z =
      deningerTimeTestLaplace φ
          (deningerXiRightEulerPoint ξ) *
        logDeriv xi
          (deningerXiRightEulerPoint ξ)
  rw [← logDeriv_XiC_eq_relativeResolventTrace hXi,
    logDeriv_XiC_eq_mul_I_logDeriv_xi,
    deningerXiRightCenteredLine_inverse]
  dsimp only [F]
  rw [deningerXiRightEulerLineSchwartz_apply]
  dsimp only [deningerXiRightEulerPoint]
  have hI : (-I) * I = 1 := by
    calc
      (-I) * I = -(I * I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; ring
  calc
    deningerTimeTestLaplace φ
          (((3 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
        (-I) *
          (I *
            logDeriv xi
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      deningerTimeTestLaplace φ
          (((3 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
        ((-I) * I) *
          logDeriv xi
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
        ring
    _ =
      deningerTimeTestLaplace φ
          (((3 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
        logDeriv xi
          (((3 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
      rw [hI, mul_one]

/--
Exact multiplicity-sensitive right-line spectral identity for every Deninger test.
-/
theorem integral_deningerTimeTestLaplace_mul_logDeriv_xi
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          logDeriv xi
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      ∑' q : XiZeroCopy,
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q) := by
  have hinterchange :
      (∑' q : XiZeroCopy,
        ∫ ξ : ℝ,
          deningerXiRightSpectralRawIntegrand φ q ξ) =
        ∫ ξ : ℝ,
          ∑' q : XiZeroCopy,
            deningerXiRightSpectralRawIntegrand φ q ξ :=
    integral_tsum_of_summable_integral_norm
      (integrable_deningerXiRightSpectralRawIntegrand φ)
      (summable_integral_norm_deningerXiRightSpectralRawIntegrand
        φ)
  calc
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          logDeriv xi
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
      ∫ ξ : ℝ,
        ∑' q : XiZeroCopy,
          deningerXiRightSpectralRawIntegrand φ q ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [tsum_deningerXiRightSpectralRawIntegrand]
      rfl
    _ =
      ∑' q : XiZeroCopy,
        ∫ ξ : ℝ,
          deningerXiRightSpectralRawIntegrand φ q ξ :=
      hinterchange.symm
    _ =
      ∑' q : XiZeroCopy,
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q) := by
      apply tsum_congr
      intro q
      exact integral_deningerXiRightSpectralRawIntegrand φ q

theorem integrable_deningerTimeTestLaplace_mul_vonMangoldtLSeries
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          LSeries
            (fun n =>
              (ArithmeticFunction.vonMangoldt n : ℂ))
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) := by
  let F : ℝ → ℂ :=
    fun ξ =>
      deningerXiRightEulerLineSchwartz φ ξ
  let L : ℝ → ℂ :=
    fun ξ =>
      LSeries
        (fun n =>
          (ArithmeticFunction.vonMangoldt n : ℂ))
        (rectangularEulerArchPoint ξ)
  have hF : Integrable F :=
    (deningerXiRightEulerLineSchwartz φ).integrable
  have hL : Continuous L := by
    exact continuous_rectangularEulerVonMangoldtLSeries
  have hbound :
      ∀ ξ : ℝ,
        ‖L ξ‖ ≤ rectangularEulerVonMangoldtBound := by
    intro ξ
    exact norm_rectangularEulerVonMangoldtLSeries_le ξ
  have hprod :=
    hF.mul_bdd hL.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
          LSeries
            (fun n =>
              (ArithmeticFunction.vonMangoldt n : ℂ))
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) =
        fun ξ : ℝ => F ξ * L ξ by
    funext ξ
    dsimp only [F, L]
    rw [deningerXiRightEulerLineSchwartz_apply]
    unfold rectangularEulerArchPoint
    congr 1
    push_cast
    ring]
  exact hprod

theorem logDeriv_xi_deningerXiRightEulerPoint_eq
    (ξ : ℝ) :
    logDeriv xi (deningerXiRightEulerPoint ξ) =
      logDeriv archFactor
          (deningerXiRightEulerPoint ξ) -
        LSeries
          (fun n =>
            (ArithmeticFunction.vonMangoldt n : ℂ))
          (deningerXiRightEulerPoint ξ) := by
  have hs :
      1 < (deningerXiRightEulerPoint ξ).re := by
    rw [deningerXiRightEulerPoint_re]
    norm_num
  have hsplit :=
    seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re
      (s := deningerXiRightEulerPoint ξ) hs
  rw [seamFluxCochain,
    infinitePrimeFlux_eq_vonMangoldtLSeries hs] at hsplit
  linear_combination -hsplit

end RHTower
