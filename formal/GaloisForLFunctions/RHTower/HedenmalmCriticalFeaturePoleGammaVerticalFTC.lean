import GaloisForLFunctions.RHTower.HedenmalmCriticalFeaturePositiveShiftCellAverage
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalHeightWindow
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound

/-!
# Vertical FTC for the HCF pole--Gamma jet

After height-cell averaging, the only derivative term in the pole--Gamma source budget is an exact
endpoint increment.  Thus the possible `N(T)`-scale contribution is confined to first-order
archimedean winding against the thin-strip source contour; the second jet cannot carry an
independent leading budget.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

private theorem hasDerivAt_im_of_complexPath
    {f : ℝ → ℂ} {f' : ℂ} {y : ℝ} (h : HasDerivAt f f' y) :
    HasDerivAt (fun t => (f t).im) f'.im y := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

private theorem hasDerivAt_criticalFeatureEulerVMArchPoint (t : ℝ) :
    HasDerivAt criticalFeatureEulerVMArchPoint I t := by
  have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hc : HasDerivAt (fun _u : ℝ => (3 / 2 : ℂ)) 0 t :=
    hasDerivAt_const t _
  have hadd := hc.add (h.mul_const I)
  have heq : criticalFeatureEulerVMArchPoint =ᶠ[nhds t]
      ((fun _u : ℝ => (3 / 2 : ℂ)) + fun u : ℝ => (u : ℂ) * I) :=
    Filter.Eventually.of_forall fun u => by
      simp only [Pi.add_apply, criticalFeatureEulerVMArchPoint]
  have htarget := hadd.congr_of_eventuallyEq heq
  simpa using htarget

/-- The imaginary part of the archimedean logarithmic derivative differentiates vertically to
the real part of its complex derivative. -/
theorem hasDerivAt_im_logDeriv_archFactor_eulerVMArchPoint (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint u)).im)
      (deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re t := by
  let s := criticalFeatureEulerVMArchPoint t
  have hsre : s.re = 3 / 2 := by
    simpa [s] using criticalFeatureEulerVMArchPoint_re t
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [zero_re, hsre] at hre
    norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re, hsre] at hre
    norm_num at hre
  have harch : AnalyticAt ℂ archFactor s := analyticAt_archFactor_of_re_pos hspos
  have harchNe : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hlog : AnalyticAt ℂ (logDeriv archFactor) s := by
    simpa only [logDeriv] using harch.deriv.div harch harchNe
  let d : ℂ := deriv (logDeriv archFactor) s
  have houtC : HasDerivAt (logDeriv archFactor) d s := by
    simpa [d] using hlog.differentiableAt.hasDerivAt
  have houtR : HasFDerivAt (logDeriv archFactor)
      ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ) s :=
    houtC.hasFDerivAt.restrictScalars ℝ
  have hpath : HasDerivAt criticalFeatureEulerVMArchPoint I t :=
    hasDerivAt_criticalFeatureEulerVMArchPoint t
  have hcomp := houtR.comp_hasDerivAt t hpath
  have him := hasDerivAt_im_of_complexPath hcomp
  simpa [Function.comp_def, s, d] using him

theorem continuous_re_logDeriv_archFactor_eulerVMArchPoint :
    Continuous (fun t : ℝ =>
      (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s := criticalFeatureEulerVMArchPoint t
  have hsre : s.re = 3 / 2 := by
    simpa [s] using criticalFeatureEulerVMArchPoint_re t
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [zero_re, hsre] at hre
    norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re, hsre] at hre
    norm_num at hre
  have harch : AnalyticAt ℂ archFactor s := analyticAt_archFactor_of_re_pos hspos
  have harchNe : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hlog : AnalyticAt ℂ (logDeriv archFactor) s := by
    simpa only [logDeriv] using harch.deriv.div harch harchNe
  have hpoint : ContinuousAt criticalFeatureEulerVMArchPoint t := by
    unfold criticalFeatureEulerVMArchPoint
    fun_prop
  exact Complex.continuous_re.continuousAt.comp
    (hlog.continuousAt.comp_of_eq hpoint rfl)

theorem continuous_re_deriv_logDeriv_archFactor_eulerVMArchPoint :
    Continuous (fun t : ℝ =>
      (deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s := criticalFeatureEulerVMArchPoint t
  have hsre : s.re = 3 / 2 := by
    simpa [s] using criticalFeatureEulerVMArchPoint_re t
  have hspos : 0 < s.re := by rw [hsre]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [zero_re, hsre] at hre
    norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re, hsre] at hre
    norm_num at hre
  have harch : AnalyticAt ℂ archFactor s := analyticAt_archFactor_of_re_pos hspos
  have harchNe : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hlog : AnalyticAt ℂ (logDeriv archFactor) s := by
    simpa only [logDeriv] using harch.deriv.div harch harchNe
  have hpoint : ContinuousAt criticalFeatureEulerVMArchPoint t := by
    unfold criticalFeatureEulerVMArchPoint
    fun_prop
  exact Complex.continuous_re.continuousAt.comp
    (hlog.deriv.continuousAt.comp_of_eq hpoint rfl)

/-- Exact endpoint evaluation of the vertical second-logarithmic-derivative channel. -/
theorem integral_re_deriv_logDeriv_archFactor_eulerVMArchPoint_eq_sub (a b : ℝ) :
    (∫ t : ℝ in a..b,
      (deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) =
      (logDeriv archFactor (criticalFeatureEulerVMArchPoint b)).im -
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint a)).im := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_im_logDeriv_archFactor_eulerVMArchPoint t
  · exact continuous_re_deriv_logDeriv_archFactor_eulerVMArchPoint.intervalIntegrable _ _

/-- Exact vertical-FTC reduction of the pole--Gamma jet.  The second jet is purely an endpoint
increment; only first-order archimedean winding can remain at leading height scale. -/
theorem integral_criticalFeaturePoleGammaArchJet_eq_firstOrder_sub_endpoints (a b : ℝ) :
    (∫ t : ℝ in a..b,
      2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
        deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) =
      2 * (∫ t : ℝ in a..b,
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) -
      2 * ((logDeriv archFactor (criticalFeatureEulerVMArchPoint b)).im -
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint a)).im) := by
  simp_rw [sub_re, mul_sub]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_re_deriv_logDeriv_archFactor_eulerVMArchPoint_eq_sub]
    ring
  · exact continuous_re_logDeriv_archFactor_eulerVMArchPoint.const_mul 2
      |>.intervalIntegrable _ _
  · exact continuous_re_deriv_logDeriv_archFactor_eulerVMArchPoint.const_mul 2
      |>.intervalIntegrable _ _

/-- The HCF safe Euler line is the depth-one side of the centered archimedean rectangle. -/
theorem criticalFeatureEulerVMArchPoint_eq_xiMassArchVerticalEulerPoint (t : ℝ) :
    criticalFeatureEulerVMArchPoint t = xiMassArchVerticalEulerPoint t (-1) := by
  rw [xiMassArchVerticalEulerPoint_eq]
  unfold criticalFeatureEulerVMArchPoint
  norm_num

/-- Zero-independent linear growth of the first archimedean logarithmic derivative on the HCF
safe line. -/
theorem norm_logDeriv_archFactor_criticalFeatureEulerVMArchPoint_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖logDeriv archFactor (criticalFeatureEulerVMArchPoint t)‖ ≤
      xiMassArchVerticalGrowthConstant + |t| / 2 := by
  rw [criticalFeatureEulerVMArchPoint_eq_xiMassArchVerticalEulerPoint]
  exact norm_logDeriv_archFactor_xiMassArchVertical_le
    (c := 1) (R := t) (y := -1) (by constructor <;> norm_num)
      (max_le ht (by norm_num; linarith))

/-- Endpoint increment left by telescoping the vertical second jet over the canonical height
window. -/
def criticalFeatureCanonicalPoleGammaEndpointIncrement (n : ℕ) : ℝ :=
  (logDeriv archFactor
      (criticalFeatureEulerVMArchPoint ((n : ℝ) + 1))).im -
    (logDeriv archFactor
      (criticalFeatureEulerVMArchPoint (-((n : ℝ) + 2)))).im

/-- Reciprocal canonical zero count tends to zero.  This is extracted from the already-proved
fact that the nonempty canonical lattice has cardinality `o(N)`. -/
theorem tendsto_one_div_criticalFeatureCanonicalZeroCount :
    Tendsto (fun n : ℕ => 1 / criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (eventually_criticalFeatureCanonicalZeroCount_pos.mono fun n hn => by positivity)
    ?_ tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hn
  rw [div_le_div_iff_of_pos_right hn]
  have hc : 1 ≤ (criticalFeatureCanonicalLatticeWindow n).card := by
    rw [card_criticalFeatureCanonicalLatticeWindow]
    omega
  exact_mod_cast hc

/-- Every fixed scalar is negligible against the canonical zero count. -/
theorem tendsto_const_div_criticalFeatureCanonicalZeroCount (C : ℝ) :
    Tendsto (fun n : ℕ => C / criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have h : Tendsto
      (fun n : ℕ => C * (1 / criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_criticalFeatureCanonicalZeroCount
  simpa [div_eq_mul_inv] using h

/-- The canonical endpoint increment is bounded by a constant plus half the lattice size. -/
theorem abs_criticalFeatureCanonicalPoleGammaEndpointIncrement_le
    (n : ℕ) (hn : 1 ≤ n) :
    |criticalFeatureCanonicalPoleGammaEndpointIncrement n| ≤
      2 * xiMassArchVerticalGrowthConstant +
        ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) / 2 := by
  let Lp := logDeriv archFactor
      (criticalFeatureEulerVMArchPoint ((n : ℝ) + 1))
  let Lm := logDeriv archFactor
      (criticalFeatureEulerVMArchPoint (-((n : ℝ) + 2)))
  have hpHeight : 2 ≤ |(n : ℝ) + 1| := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hmHeight : 2 ≤ |-((n : ℝ) + 2)| := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hp := norm_logDeriv_archFactor_criticalFeatureEulerVMArchPoint_le hpHeight
  have hm := norm_logDeriv_archFactor_criticalFeatureEulerVMArchPoint_le hmHeight
  have hpIm : |Lp.im| ≤ xiMassArchVerticalGrowthConstant + |(n : ℝ) + 1| / 2 :=
    (Complex.abs_im_le_norm Lp).trans hp
  have hmIm : |Lm.im| ≤ xiMassArchVerticalGrowthConstant + |-((n : ℝ) + 2)| / 2 :=
    (Complex.abs_im_le_norm Lm).trans hm
  rw [card_criticalFeatureCanonicalLatticeWindow]
  push_cast
  dsimp only [criticalFeatureCanonicalPoleGammaEndpointIncrement, Lp, Lm]
  calc
    |(logDeriv archFactor (criticalFeatureEulerVMArchPoint ((n : ℝ) + 1))).im -
        (logDeriv archFactor
          (criticalFeatureEulerVMArchPoint (-((n : ℝ) + 2)))).im|
        ≤ |Lp.im| + |Lm.im| := abs_sub _ _
    _ ≤ (xiMassArchVerticalGrowthConstant + |(n : ℝ) + 1| / 2) +
        (xiMassArchVerticalGrowthConstant + |-((n : ℝ) + 2)| / 2) :=
      add_le_add hpIm hmIm
    _ = 2 * xiMassArchVerticalGrowthConstant + (2 * (n : ℝ) + 3) / 2 := by
      rw [abs_of_nonneg, abs_neg, abs_of_nonneg] <;> try positivity
      ring

/-- The entire second-logarithmic-derivative channel is `o(N)` on canonical height windows. -/
theorem tendsto_criticalFeatureCanonicalPoleGammaEndpointIncrement_div :
    Tendsto
      (fun n : ℕ =>
        criticalFeatureCanonicalPoleGammaEndpointIncrement n /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun n : ℕ =>
        (2 * xiMassArchVerticalGrowthConstant) /
            criticalFeatureCanonicalZeroCount n +
          (((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
            criticalFeatureCanonicalZeroCount n) / 2)
      atTop (𝓝 0) := by
    convert
      (tendsto_const_div_criticalFeatureCanonicalZeroCount
          (2 * xiMassArchVerticalGrowthConstant)).add
        (tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount.div_const 2)
        using 1 <;> norm_num
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 1,
      eventually_criticalFeatureCanonicalZeroCount_pos] with n hn hcount
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hcount]
    have hne : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hcount
    field_simp [hne]
    nlinarith [abs_criticalFeatureCanonicalPoleGammaEndpointIncrement_le n hn]

end

end RHTower
