import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.CriticalTraceMomentGerm
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.XiTraceHankelCountableCriterion
import Mathlib.Analysis.Analytic.OfScalars

/-!
# The prime--archimedean central moment germ

The centered completed prime source is an odd relative trace.  Dividing by the centered
coordinate produces an even germ.  This file identifies that source-built germ with the analytic
generating series of the centered reciprocal-square Xi moments.

The point of the construction is source transport: downstream trace--Hankel tests may read their
moments from Taylor coefficients of the fixed prime--Gamma source, rather than assuming a separate
equality with zero-divisor moments.
-/

open Complex Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The centered reciprocal moments interleaved with zero odd coefficients. -/
def xiCentralMomentCoefficient (k : ℕ) : ℂ :=
  if k % 2 = 0 then xiCentralReciprocalMoment (k / 2) else 0

@[simp] theorem xiCentralMomentCoefficient_two_mul (n : ℕ) :
    xiCentralMomentCoefficient (2 * n) = xiCentralReciprocalMoment n := by
  simp [xiCentralMomentCoefficient]

@[simp] theorem xiCentralMomentCoefficient_two_mul_add_one (n : ℕ) :
    xiCentralMomentCoefficient (2 * n + 1) = 0 := by
  simp [xiCentralMomentCoefficient]

/-- The formal even moment series attached to the actual centered Xi divisor. -/
def xiCentralMomentPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ xiCentralMomentCoefficient

/-- Its analytic sum; positivity of its convergence radius is proved below. -/
def xiCentralMomentGerm : ℂ → ℂ :=
  xiCentralMomentPowerSeries.sum

/-- The multiplicity-copy reciprocal-square coordinates admit one common norm bound. -/
theorem exists_xiZeroCopyReciprocalSquare_norm_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_xi_central_reciprocal_square_norm_bound
  refine ⟨M, hM, fun q => ?_⟩
  rw [xiZeroCopyReciprocalSquare_eq]
  exact hbound q.1

/-- A geometric bound for every centered reciprocal moment. -/
theorem norm_xiCentralReciprocalMoment_le
    {M : ℝ} (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (n : ℕ) :
    ‖xiCentralReciprocalMoment n‖ ≤
      M ^ n * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
  rw [← tsum_xiZeroCopyReciprocalSquare_pow n]
  calc
    ‖∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (n + 1)‖ ≤
        ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q ^ (n + 1)‖ :=
      norm_tsum_le_tsum_norm (summable_xiZeroCopyReciprocalSquare_pow n).norm
    _ ≤ ∑' q : XiZeroCopy,
        M ^ n * ‖xiZeroCopyReciprocalSquare q‖ := by
      apply Summable.tsum_mono
        (summable_xiZeroCopyReciprocalSquare_pow n).norm
        (summable_xiZeroCopyReciprocalSquare.norm.mul_left (M ^ n))
      intro q
      simpa only [pow_succ, norm_mul, norm_pow] using
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg (xiZeroCopyReciprocalSquare q)) (hbound q) n)
          (norm_nonneg (xiZeroCopyReciprocalSquare q)))
    _ = M ^ n * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
      rw [tsum_mul_left]

/-- The interleaved moment coefficients have a positive common convergence radius. -/
theorem xiCentralMomentPowerSeries_radius_pos :
    0 < xiCentralMomentPowerSeries.radius := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let r : ℝ≥0 := ⟨1 / (2 * M), by positivity⟩
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖
  have hrad : (r : ℝ≥0∞) ≤ xiCentralMomentPowerSeries.radius := by
    apply FormalMultilinearSeries.le_radius_of_bound (p := xiCentralMomentPowerSeries) S
    intro k
    rw [xiCentralMomentPowerSeries, FormalMultilinearSeries.ofScalars_norm]
    by_cases hk : k % 2 = 0
    · rw [xiCentralMomentCoefficient, if_pos hk]
      have hmoment := norm_xiCentralReciprocalMoment_le hbound (k / 2)
      have hpow : M ^ (k / 2) ≤ M ^ k := by
        exact pow_le_pow_right₀ hM (Nat.div_le_self k 2)
      have hcoef : ‖xiCentralReciprocalMoment (k / 2)‖ ≤ M ^ k * S :=
        hmoment.trans (mul_le_mul_of_nonneg_right hpow (tsum_nonneg fun _ => norm_nonneg _))
      change ‖xiCentralReciprocalMoment (k / 2)‖ * (1 / (2 * M)) ^ k ≤ S
      calc
        ‖xiCentralReciprocalMoment (k / 2)‖ * (1 / (2 * M)) ^ k ≤
            (M ^ k * S) * (1 / (2 * M)) ^ k :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by positivity) _)
        _ = S * (M * (1 / (2 * M))) ^ k := by
          rw [mul_pow]
          ring
        _ = S * (1 / 2) ^ k := by
          rw [show M * (1 / (2 * M)) = (1 / 2 : ℝ) by field_simp]
        _ ≤ S := by
          exact mul_le_of_le_one_right (tsum_nonneg fun _ => norm_nonneg _)
            (pow_le_one₀ (by norm_num) (by norm_num))
    · rw [xiCentralMomentCoefficient, if_neg hk, norm_zero, zero_mul]
      exact tsum_nonneg fun _ => norm_nonneg _
  have hrpos : 0 < r := by
    apply NNReal.coe_pos.mp
    change 0 < 1 / (2 * M)
    positivity
  exact (ENNReal.coe_pos.mpr hrpos).trans_le hrad

/-- The moment-series sum is analytic at the centered origin. -/
theorem analyticAt_xiCentralMomentGerm : AnalyticAt ℂ xiCentralMomentGerm 0 := by
  exact ⟨xiCentralMomentPowerSeries,
    xiCentralMomentPowerSeries.hasFPowerSeriesOnBall
      xiCentralMomentPowerSeries_radius_pos |>.hasFPowerSeriesAt⟩

/-- The analytic moment germ is the ordinary even generating series of the centered moments. -/
theorem xiCentralMomentGerm_eq_tsum_even (z : ℂ) :
    xiCentralMomentGerm z =
      ∑' n : ℕ, xiCentralReciprocalMoment n * z ^ (2 * n) := by
  rw [xiCentralMomentGerm, xiCentralMomentPowerSeries]
  change FormalMultilinearSeries.ofScalarsSum xiCentralMomentCoefficient z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    dsimp at hab
    omega
  have hsupp : Function.support
      (fun k : ℕ => xiCentralMomentCoefficient k * z ^ k) ⊆
        Set.range (fun n : ℕ => 2 * n) := by
    intro k hk
    by_cases heven : k % 2 = 0
    · refine ⟨k / 2, ?_⟩
      have hdiv := Nat.mod_add_div k 2
      dsimp
      omega
    · rw [Function.mem_support] at hk
      exact (hk (by simp [xiCentralMomentCoefficient, heven])).elim
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro n
  simp

/-- On its natural disk, the moment germ is the reciprocal-square resolvent sum.  This is the
countable Tonelli/geometric-series step linking analytic Taylor coefficients to the Xi divisor. -/
theorem xiCentralMomentGerm_eq_reciprocalSquareResolvent
    {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ^ 2 * M < 1) :
    xiCentralMomentGerm z =
      ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let lam : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  have hlam : Summable (fun q => ‖lam q‖) := by
    simpa only [lam] using summable_xiZeroCopyReciprocalSquare.norm
  let ratio : ℝ := ‖z‖ ^ 2 * M
  have hratio0 : 0 ≤ ratio := mul_nonneg (sq_nonneg _) hM0
  have hratio1 : ratio < 1 := by simpa only [ratio] using hz
  have hgeom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hboundTerm : ∀ (n : ℕ) (q : XiZeroCopy),
      ‖z ^ (2 * n) * lam q ^ (n + 1)‖ ≤ ratio ^ n * ‖lam q‖ := by
    intro n q
    rw [norm_mul, norm_pow, norm_pow, pow_succ, pow_mul]
    have hlamPow : ‖lam q‖ ^ n ≤ M ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound q) n
    calc
      (‖z‖ ^ 2) ^ n * (‖lam q‖ ^ n * ‖lam q‖) ≤
          (‖z‖ ^ 2) ^ n * (M ^ n * ‖lam q‖) := by
        gcongr
      _ = ratio ^ n * ‖lam q‖ := by
        rw [mul_pow]
        ring
  have hnorm : Summable (fun p : ℕ × XiZeroCopy =>
      ratio ^ p.1 * ‖lam p.2‖) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))]
    constructor
    · intro n
      exact hlam.mul_left (ratio ^ n)
    · apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg fun _ => mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))
        (fun n => le_rfl)
      exact (hgeom.mul_right (∑' q : XiZeroCopy, ‖lam q‖)).congr
        (fun n => by rw [← tsum_mul_left])
  have huncurry : Summable (Function.uncurry
      (fun (n : ℕ) (q : XiZeroCopy) => z ^ (2 * n) * lam q ^ (n + 1))) := by
    apply Summable.of_norm_bounded hnorm
    intro p
    exact hboundTerm p.1 p.2
  rw [xiCentralMomentGerm_eq_tsum_even]
  have hstep : ∀ n : ℕ,
      xiCentralReciprocalMoment n * z ^ (2 * n) =
        ∑' q : XiZeroCopy, z ^ (2 * n) * lam q ^ (n + 1) := by
    intro n
    rw [← tsum_xiZeroCopyReciprocalSquare_pow n, ← tsum_mul_right]
    apply tsum_congr
    intro q
    dsimp [lam]
    ring
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr
  intro q
  have hzlam : ‖z ^ 2 * lam q‖ < 1 := by
    rw [norm_mul, norm_pow]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hbound q) (sq_nonneg ‖z‖)) hz
  rw [xiReciprocalSquareResolventTerm]
  change (∑' n : ℕ, z ^ (2 * n) * lam q ^ (n + 1)) =
    lam q / (1 - z ^ 2 * lam q)
  calc
    (∑' n : ℕ, z ^ (2 * n) * lam q ^ (n + 1)) =
        lam q * ∑' n : ℕ, (z ^ 2 * lam q) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow, pow_succ]
      ring
    _ = lam q / (1 - z ^ 2 * lam q) := by
      rw [tsum_geometric_of_norm_lt_one hzlam, div_eq_mul_inv]

/-- Taylor coefficient extraction for the analytic central moment germ. -/
theorem analyticTraceMoments_xiCentralMomentGerm (n : ℕ) :
    analyticTraceMoments xiCentralMomentGerm n =
      (xiCentralReciprocalMoment n).re := by
  have hp := xiCentralMomentPowerSeries.hasFPowerSeriesOnBall
    xiCentralMomentPowerSeries_radius_pos
  have hfac := hp.factorial_smul (1 : ℂ) (2 * n)
  have hderiv : iteratedDeriv (2 * n) xiCentralMomentGerm 0 =
      (((2 * n).factorial : ℕ) : ℂ) * xiCentralReciprocalMoment n := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const_one, one_smul] at hfac
    rw [xiCentralMomentPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, xiCentralMomentCoefficient_two_mul] at hfac
    rw [xiCentralMomentGerm, xiCentralMomentPowerSeries]
    simpa only [nsmul_eq_mul] using hfac.symm
  rw [analyticTraceMoments, hderiv]
  have hfacne : (((2 * n).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  rw [mul_div_cancel_left₀ _ hfacne]

/-- The continued completed prime source vanishes at the centered origin. -/
@[simp] theorem continuedPrimeArchSourceRelativeTrace_zero :
    continuedPrimeArchSourceRelativeTrace 0 = 0 := by
  have hzetaReal :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
  have hzeta : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
    simpa using hzetaReal
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (z := 0) (by norm_num) (by norm_num) (by simpa using hzeta)]
  simp [xiRelativeResolventTrace, xiRelativeResolventTerm]

/-- Away from the center, normalized division of the fixed prime--Gamma source is exactly the
reciprocal-square resolvent. -/
theorem normalizedTraceMomentGerm_continuedPrimeArchSource_eq_resolvent
    {z : ℂ} (hz0 : z ≠ 0)
    (hspos : 0 < (1 / 2 + z * Complex.I).re)
    (hs1 : 1 / 2 + z * Complex.I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace z =
      ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  let s : ℂ := 1 / 2 + z * Complex.I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith
  have hG := Gammaℝ_ne_zero_of_re_pos hspos
  have hXi : XiC z ≠ 0 := by
    change xi s ≠ 0
    rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG]
    exact mul_ne_zero (archFactor_ne_zero hs0 hs1 hG) hzeta
  rw [normalizedTraceMomentGerm, dslope_of_ne _ hz0, slope_def_module,
    continuedPrimeArchSourceRelativeTrace_zero,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hspos hs1 hzeta,
    xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hz0]

/-- Near the center, the continued prime--Gamma source is the analytic logarithmic derivative of
`XiC`.  In particular, its local analyticity is source-side and does not require RH. -/
theorem continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC :
    continuedPrimeArchSourceRelativeTrace =ᶠ[𝓝 0] logDeriv XiC := by
  let s : ℂ → ℂ := fun z => 1 / 2 + z * Complex.I
  have hscont : ContinuousAt s 0 := by
    dsimp [s]
    fun_prop
  have hsrecont : ContinuousAt (fun z => (s z).re) 0 :=
    Complex.continuous_re.continuousAt.comp hscont
  have hspos : ∀ᶠ z in 𝓝 0, 0 < (s z).re := by
    change ∀ᶠ z in 𝓝 0, (s z).re ∈ Set.Ioi 0
    exact hsrecont (Ioi_mem_nhds (by simp [s]))
  have hs1 : ∀ᶠ z in 𝓝 0, s z ≠ 1 :=
    hscont.eventually_ne (by simp [s])
  have hzetaReal :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
  have hzeta0 : riemannZeta (s 0) ≠ 0 := by
    simpa [s] using hzetaReal
  have hzetaCont : ContinuousAt (fun z => riemannZeta (s z)) 0 := by
    have hzetaAt : ContinuousAt riemannZeta (s 0) := by
      exact (differentiableAt_riemannZeta (by simp [s])).continuousAt
    exact hzetaAt.comp hscont
  have hzeta : ∀ᶠ z in 𝓝 0, riemannZeta (s z) ≠ 0 :=
    hzetaCont.eventually_ne hzeta0
  have hXi : ∀ᶠ z in 𝓝 0, XiC z ≠ 0 :=
    (XiC_analytic 0 (Set.mem_univ 0)).continuousAt.eventually_ne XiC_zero_ne
  filter_upwards [hspos, hs1, hzeta, hXi] with z hzpos hz1 hzzeta hXiz
  calc
    continuedPrimeArchSourceRelativeTrace z = xiRelativeResolventTrace z :=
      continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
        (by simpa only [s] using hzpos) (by simpa only [s] using hz1)
        (by simpa only [s] using hzzeta)
    _ = logDeriv XiC z := (logDeriv_XiC_eq_relativeResolventTrace hXiz).symm

/-- The fixed continued prime--Gamma relative trace is analytic at the centered origin. -/
theorem analyticAt_continuedPrimeArchSourceRelativeTrace :
    AnalyticAt ℂ continuedPrimeArchSourceRelativeTrace 0 := by
  have hXi : AnalyticAt ℂ XiC 0 := XiC_analytic 0 (Set.mem_univ 0)
  have hlog : AnalyticAt ℂ (logDeriv XiC) 0 := by
    rw [show logDeriv XiC = fun z => deriv XiC z / XiC z by rfl]
    exact hXi.deriv.div hXi XiC_zero_ne
  exact hlog.congr continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC.symm

/-- Normalized division turns the odd prime--Gamma relative trace into an analytic even source
germ at the center. -/
theorem analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource :
    AnalyticAt ℂ
      (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 :=
  analyticAt_normalizedTraceMomentGerm analyticAt_continuedPrimeArchSourceRelativeTrace

/-- **Prime--Gamma source germ identity.**  The normalized continued source and the analytic
centered-moment generating series are the same germ at the functional-equation center. -/
theorem normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm :
    normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace =ᶠ[𝓝 0]
      xiCentralMomentGerm := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hratioCont : ContinuousAt (fun z : ℂ => ‖z‖ ^ 2 * M) 0 := by fun_prop
  have hratioTendsto : Tendsto (fun z : ℂ => ‖z‖ ^ 2 * M) (𝓝 0) (𝓝 0) := by
    have ht := hratioCont
    change Tendsto (fun z : ℂ => ‖z‖ ^ 2 * M) (𝓝 0)
      (𝓝 (‖(0 : ℂ)‖ ^ 2 * M)) at ht
    norm_num at ht
    exact ht
  have hratio : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ^ 2 * M < 1 :=
    hratioTendsto.eventually_lt_const zero_lt_one
  have hXi : ∀ᶠ z in 𝓝 0, XiC z ≠ 0 :=
    (XiC_analytic 0 (Set.mem_univ 0)).continuousAt.eventually_ne XiC_zero_ne
  have hsource := continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC
  have hnear : ∀ᶠ z in 𝓝[≠] 0,
      normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace z =
        xiCentralMomentGerm z := by
    filter_upwards [hsource.filter_mono nhdsWithin_le_nhds,
      hXi.filter_mono nhdsWithin_le_nhds,
      hratio.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hzsource hXiz hzratio hzmem
    have hz0 : z ≠ 0 := by simpa using hzmem
    rw [normalizedTraceMomentGerm, dslope_of_ne _ hz0, slope_def_module,
      continuedPrimeArchSourceRelativeTrace_zero, hzsource,
      logDeriv_XiC_eq_relativeResolventTrace hXiz,
      xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXiz,
      ← xiCentralMomentGerm_eq_reciprocalSquareResolvent hM hbound hzratio]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hz0]
  exact (analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
    |>.frequently_eq_iff_eventually_eq analyticAt_xiCentralMomentGerm).mp hnear.frequently

/-- Every centered reciprocal moment is therefore a Taylor coefficient of the fixed prime--Gamma
source germ. -/
theorem analyticTraceMoments_normalizedPrimeArchSource (n : ℕ) :
    analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) n =
      (xiCentralReciprocalMoment n).re := by
  have heq := normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm
  have hder := heq.iteratedDeriv_eq (2 * n)
  rw [analyticTraceMoments, hder]
  simpa only [analyticTraceMoments] using analyticTraceMoments_xiCentralMomentGerm n

/-- Complex form of the coefficient identity, using unconditional Schwarz reality of the Xi
moments.  This is the exact interface consumed by the trace--Hankel criterion. -/
theorem primeArchSourceMoment_eq_xiCentralReciprocalMoment (n : ℕ) :
    ((analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) n : ℝ) : ℂ) =
      xiCentralReciprocalMoment n := by
  rw [analyticTraceMoments_normalizedPrimeArchSource]
  apply Complex.ext
  · simp
  · simp [xiCentralReciprocalMoment_im_eq_zero]

/-- The finite quadratic Hankel value formed entirely from Taylor coefficients of the normalized
prime--Gamma source. -/
def primeArchSourceTraceHankel (p : Polynomial ℝ) : ℂ :=
  ∑ k ∈ Finset.range (((p.map (algebraMap ℝ ℂ)) ^ 2).natDegree + 1),
    ((p.map (algebraMap ℝ ℂ)) ^ 2).coeff k *
      ((analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) k : ℝ) : ℂ)

/-- **Zero-data elimination for the Hankel value.**  Every Xi trace--Hankel test is exactly the
finite coefficient pairing read from the fixed prime--Gamma source germ. -/
theorem xiCentralTraceHankel_eq_primeArchSourceTraceHankel (p : Polynomial ℝ) :
    xiCentralTraceHankel p = primeArchSourceTraceHankel p := by
  rw [xiCentralTraceHankel_eq_moment_sum, primeArchSourceTraceHankel]
  apply Finset.sum_congr rfl
  intro k hk
  rw [primeArchSourceMoment_eq_xiCentralReciprocalMoment]

/-- Countable source positivity: every integer polynomial has nonnegative quadratic value when
read from the normalized continued prime--Gamma germ.  The definition contains no Xi zero data. -/
def PrimeArchSourceTraceHankelIntNonnegative : Prop :=
  ∀ p : Polynomial ℤ,
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- **Top-down source chain.**  Countable integer-polynomial positivity of the fixed prime--Gamma
Taylor germ implies RH.  The moment-identification and real-to-integer reductions are unconditional;
the sole remaining mathematical input is source positivity. -/
theorem riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (hsource : PrimeArchSourceTraceHankelIntNonnegative) :
    RiemannHypothesis := by
  apply xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis.mp
  intro p
  rw [xiCentralTraceHankel_eq_primeArchSourceTraceHankel]
  exact hsource p

end

end RHTower
