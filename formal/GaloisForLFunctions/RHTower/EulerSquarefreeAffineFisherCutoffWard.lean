import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffLimits

/-!
# Affine Euler clock from the squarefree clock

The unique decomposition `n = d m²` adds to the critical squarefree clock the residual clock
`2 (σ - 1) log m`.  The residual index has the normalized zeta law of inverse temperature `2σ`.
Its critical clock converges weakly to zero.  Consequently the independent affine sum of the
squarefree clock and the residual clock has the same unit-rate exponential limit as the
squarefree clock.

This is the probability-law core of the CCM affine-cutoff transport.  It is unconditional and
contains no Xi divisor or RH hypothesis.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

/-- Positive residual square-channel mass at inverse temperature `σ`. -/
def eulerSquareResidualMass (sigma : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-2 * sigma)

theorem eulerSquareResidualMass_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ eulerSquareResidualMass sigma n := by
  rw [eulerSquareResidualMass]
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem summable_eulerSquareResidualMass
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerSquareResidualMass sigma) := by
  apply Summable.of_nonneg_of_le (eulerSquareResidualMass_nonneg sigma)
    (fun n => ?_) (Real.summable_nat_rpow.mpr (by linarith : -2 * sigma < -1))
  rw [eulerSquareResidualMass]
  split_ifs
  · positivity
  · exact le_rfl

/-- Partition function of the residual square channel. -/
def eulerSquareResidualTotal (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, eulerSquareResidualMass sigma n

theorem eulerSquareResidualTotal_pos
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < eulerSquareResidualTotal sigma := by
  apply (summable_eulerSquareResidualMass hsigma).tsum_pos
    (eulerSquareResidualMass_nonneg sigma) 1
  simp [eulerSquareResidualMass]

/-- Normalized residual square-channel probability. -/
def eulerSquareResidualProbability (sigma : ℝ) (n : ℕ) : ℝ :=
  eulerSquareResidualMass sigma n / eulerSquareResidualTotal sigma

theorem eulerSquareResidualProbability_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ eulerSquareResidualProbability sigma n := by
  exact div_nonneg (eulerSquareResidualMass_nonneg sigma n)
    (eulerSquareResidualTotal_pos hsigma).le

theorem summable_eulerSquareResidualProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerSquareResidualProbability sigma) :=
  (summable_eulerSquareResidualMass hsigma).div_const _

theorem tsum_eulerSquareResidualProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ∑' n : ℕ, eulerSquareResidualProbability sigma n = 1 := by
  rw [show (∑' n : ℕ, eulerSquareResidualProbability sigma n) =
      (∑' n : ℕ, eulerSquareResidualMass sigma n) /
        eulerSquareResidualTotal sigma by
    exact tsum_div_const]
  rw [show (∑' n : ℕ, eulerSquareResidualMass sigma n) =
      eulerSquareResidualTotal sigma by rfl]
  exact div_self (eulerSquareResidualTotal_pos hsigma).ne'

private def eulerSquareResidualPMFOf
    (sigma : ℝ) (hsigma : 1 < sigma) : PMF ℕ := by
  refine ⟨fun n => ENNReal.ofReal (eulerSquareResidualProbability sigma n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← ENNReal.toNNReal_one]
  have hsum : HasSum (eulerSquareResidualProbability sigma) 1 := by
    rw [← tsum_eulerSquareResidualProbability hsigma]
    exact (summable_eulerSquareResidualProbability hsigma).hasSum
  simpa using hsum.toNNReal (eulerSquareResidualProbability_nonneg hsigma)

/-- Residual square-channel PMF, extended away from `σ>1` by a harmless point mass. -/
def eulerSquareResidualPMF (sigma : ℝ) : PMF ℕ :=
  if hsigma : 1 < sigma then eulerSquareResidualPMFOf sigma hsigma else PMF.pure 1

theorem eulerSquareResidualPMF_toReal
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    (eulerSquareResidualPMF sigma n).toReal =
      eulerSquareResidualProbability sigma n := by
  rw [eulerSquareResidualPMF, dif_pos hsigma]
  change (ENNReal.ofReal (eulerSquareResidualProbability sigma n)).toReal = _
  rw [ENNReal.toReal_ofReal (eulerSquareResidualProbability_nonneg hsigma n)]

/-- Residual square-channel probability measure on its discrete index. -/
def eulerSquareResidualIndexProbabilityMeasure (sigma : ℝ) : ProbabilityMeasure ℕ :=
  ⟨(eulerSquareResidualPMF sigma).toMeasure, inferInstance⟩

/-- Critical residual logarithmic clock contributed by the square coordinate. -/
def eulerSquareResidualCriticalClock (sigma : ℝ) (n : ℕ) : ℝ :=
  2 * (sigma - 1) * Real.log n

/-- Residual critical clock as a Borel probability measure. -/
def eulerSquareResidualCriticalClockProbabilityMeasure
    (sigma : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (eulerSquareResidualIndexProbabilityMeasure sigma)
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (eulerSquareResidualCriticalClock sigma)
        (eulerSquareResidualPMF sigma).toMeasure)

theorem integrable_eulerSquareResidualCriticalClock_char
    (sigma t : ℝ) :
    Integrable
      (fun n : ℕ =>
        Complex.exp (((t * eulerSquareResidualCriticalClock sigma n : ℝ) : ℂ) *
          Complex.I))
      (eulerSquareResidualPMF sigma).toMeasure := by
  refine (integrable_const (1 : ℝ)).mono'
    Measurable.of_discrete.aestronglyMeasurable ?_
  filter_upwards with n
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem charFun_eulerSquareResidualCriticalClockProbabilityMeasure_eq_tsum
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    charFun
        (eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ) t =
      ∑' n : ℕ,
        (eulerSquareResidualProbability sigma n : ℂ) *
          Complex.exp
            (((t * eulerSquareResidualCriticalClock sigma n : ℝ) : ℂ) *
              Complex.I) := by
  rw [charFun_apply_real]
  unfold eulerSquareResidualCriticalClockProbabilityMeasure
    eulerSquareResidualIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hint : Integrable
      (fun n : ℕ =>
        Complex.exp ((t : ℂ) *
          (eulerSquareResidualCriticalClock sigma n : ℂ) * Complex.I))
      (eulerSquareResidualPMF sigma).toMeasure := by
    convert integrable_eulerSquareResidualCriticalClock_char sigma t using 1
    funext n
    push_cast
    rfl
  rw [PMF.integral_eq_tsum _ _ hint]
  apply tsum_congr
  intro n
  rw [eulerSquareResidualPMF_toReal hsigma]
  change (eulerSquareResidualProbability sigma n : ℂ) * _ = _
  congr 2
  push_cast
  rfl

/-- Dirichlet parameter generated by the residual critical characteristic phase. -/
def eulerSquareResidualCriticalClockParameter (sigma t : ℝ) : ℂ :=
  (2 * sigma : ℝ) -
    ((2 * t * (sigma - 1) : ℝ) : ℂ) * Complex.I

theorem eulerSquareResidualCriticalClockParameter_re (sigma t : ℝ) :
    (eulerSquareResidualCriticalClockParameter sigma t).re = 2 * sigma := by
  simp [eulerSquareResidualCriticalClockParameter]

theorem ofReal_eulerSquareResidualMass_eq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    (eulerSquareResidualMass sigma n : ℂ) =
      1 / (n : ℂ) ^ ((2 * sigma : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    have htwo : (2 * (sigma : ℂ)) ≠ 0 := by
      exact_mod_cast (by linarith : (2 * sigma : ℝ) ≠ 0)
    rw [eulerSquareResidualMass, if_pos rfl]
    norm_num
    rw [Complex.zero_cpow htwo]
  · rw [eulerSquareResidualMass, if_neg hn,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [show ((-2 * sigma : ℝ) : ℂ) = -((2 * sigma : ℝ) : ℂ) by
      push_cast
      ring]
    rw [Complex.cpow_neg, one_div]
    norm_cast

theorem ofReal_eulerSquareResidualTotal_eq_zeta
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerSquareResidualTotal sigma : ℂ) =
      riemannZeta ((2 * sigma : ℝ) : ℂ) := by
  have hmap :=
    Complex.ofRealCLM.map_tsum (summable_eulerSquareResidualMass hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  calc
    (eulerSquareResidualTotal sigma : ℂ) =
        ∑' n : ℕ, (eulerSquareResidualMass sigma n : ℂ) := by
      rw [eulerSquareResidualTotal]
      exact hmap
    _ = ∑' n : ℕ, 1 / (n : ℂ) ^ ((2 * sigma : ℝ) : ℂ) := by
      exact tsum_congr (ofReal_eulerSquareResidualMass_eq hsigma)
    _ = riemannZeta ((2 * sigma : ℝ) : ℂ) := by
      exact (zeta_eq_tsum_one_div_nat_cpow (by
        simp
        linarith : 1 < (((2 * sigma : ℝ) : ℂ)).re)).symm

/-- Exact zeta-ratio characteristic function of the residual square clock. -/
theorem charFun_eulerSquareResidualCriticalClockProbabilityMeasure_eq_zetaRatio
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    charFun
        (eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ) t =
      riemannZeta (eulerSquareResidualCriticalClockParameter sigma t) /
        riemannZeta ((2 * sigma : ℝ) : ℂ) := by
  rw [charFun_eulerSquareResidualCriticalClockProbabilityMeasure_eq_tsum
    hsigma]
  have hterm : ∀ n : ℕ,
      (eulerSquareResidualProbability sigma n : ℂ) *
          Complex.exp
            (((t * eulerSquareResidualCriticalClock sigma n : ℝ) : ℂ) *
              Complex.I) =
        (1 / (n : ℂ) ^
            eulerSquareResidualCriticalClockParameter sigma t) /
          (eulerSquareResidualTotal sigma : ℂ) := by
    intro n
    rw [eulerSquareResidualProbability, Complex.ofReal_div,
      ofReal_eulerSquareResidualMass_eq hsigma]
    by_cases hn : n = 0
    · subst n
      have hparam :
          eulerSquareResidualCriticalClockParameter sigma t ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        rw [eulerSquareResidualCriticalClockParameter_re] at hre
        simp only [Complex.zero_re] at hre
        linarith
      have htwo : (((2 * sigma : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (by linarith : (2 * sigma : ℝ) ≠ 0)
      simp only [eulerSquareResidualCriticalClock, Nat.cast_zero,
        Real.log_zero, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, mul_one]
      rw [Complex.zero_cpow htwo, Complex.zero_cpow hparam]
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
      have hcpow : ∀ w : ℂ,
          (n : ℂ) ^ w = Complex.exp (((Real.log n : ℝ) : ℂ) * w) := by
        intro w
        rw [Complex.cpow_def_of_ne_zero hnC, hlog]
      rw [div_mul_eq_mul_div]
      congr 1
      rw [hcpow, hcpow, div_eq_mul_inv, div_eq_mul_inv,
        ← Complex.exp_neg, ← Complex.exp_neg]
      simp only [one_mul]
      rw [← Complex.exp_add]
      congr 1
      unfold eulerSquareResidualCriticalClockParameter
        eulerSquareResidualCriticalClock
      push_cast
      ring
  rw [show (∑' n : ℕ,
      (eulerSquareResidualProbability sigma n : ℂ) *
        Complex.exp
          (((t * eulerSquareResidualCriticalClock sigma n : ℝ) : ℂ) *
            Complex.I)) =
      ∑' n : ℕ,
        (1 / (n : ℂ) ^
            eulerSquareResidualCriticalClockParameter sigma t) /
          (eulerSquareResidualTotal sigma : ℂ) by
    exact tsum_congr hterm]
  rw [tsum_div_const,
    zeta_eq_tsum_one_div_nat_cpow (by
      rw [eulerSquareResidualCriticalClockParameter_re]
      linarith)]
  rw [ofReal_eulerSquareResidualTotal_eq_zeta hsigma]

/-- Pointwise characteristic-function limit of the residual square clock. -/
theorem tendsto_charFun_eulerSquareResidualCriticalClockProbabilityMeasure
    (t : ℝ) :
    Tendsto
      (fun sigma : ℝ =>
        charFun
          (eulerSquareResidualCriticalClockProbabilityMeasure sigma :
            Measure ℝ) t)
      (nhdsWithin 1 (Ioi 1))
      (nhds 1) := by
  have hparam : Tendsto
      (fun sigma : ℝ =>
        eulerSquareResidualCriticalClockParameter sigma t)
      (nhdsWithin 1 (Ioi 1)) (nhds (2 : ℂ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          eulerSquareResidualCriticalClockParameter sigma t) 1 := by
      unfold eulerSquareResidualCriticalClockParameter
      fun_prop
    simpa [eulerSquareResidualCriticalClockParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hdenParam : Tendsto
      (fun sigma : ℝ => ((2 * sigma : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (2 : ℂ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ => ((2 * sigma : ℝ) : ℂ)) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hznum : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (eulerSquareResidualCriticalClockParameter sigma t))
      (nhdsWithin 1 (Ioi 1)) (nhds (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt
      |>.tendsto.comp hparam
  have hzden : Tendsto
      (fun sigma : ℝ => riemannZeta ((2 * sigma : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt
      |>.tendsto.comp hdenParam
  have hzetaTwo : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hratio := hznum.div hzden hzetaTwo
  have hvalue : riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ) = 1 :=
    div_self hzetaTwo
  rw [hvalue] at hratio
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact
    (charFun_eulerSquareResidualCriticalClockProbabilityMeasure_eq_zetaRatio
      hsigma t).symm

/-- Point mass at the zero clock. -/
def eulerSquareResidualZeroProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac 0, inferInstance⟩

/-- Residual square clock collapses weakly to the zero clock at criticality. -/
theorem tendsto_eulerSquareResidualCriticalClockProbabilityMeasure :
    Tendsto eulerSquareResidualCriticalClockProbabilityMeasure
      (nhdsWithin 1 (Ioi 1))
      (nhds eulerSquareResidualZeroProbabilityMeasure) := by
  rw [tendsto_iff_seq_tendsto]
  intro sigma hsigma
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hchar :=
    (tendsto_charFun_eulerSquareResidualCriticalClockProbabilityMeasure t).comp
      hsigma
  have hzero :
      charFun
          (eulerSquareResidualZeroProbabilityMeasure : Measure ℝ) t = 1 := by
    change charFun (Measure.dirac 0) t = 1
    rw [charFun_dirac]
    simp
  rw [hzero]
  exact hchar

/-- Independent squarefree and residual square clocks before affine addition. -/
def eulerSquarefreeAffineCriticalClockPairProbabilityMeasure
    (sigma : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  (squarefreeMobiusCriticalClockProbabilityMeasure sigma).prod
    (eulerSquareResidualCriticalClockProbabilityMeasure sigma)

/-- Physical affine critical clock obtained by adding squarefree and square residual clocks. -/
def eulerSquarefreeAffineCriticalClockProbabilityMeasure
    (sigma : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (eulerSquarefreeAffineCriticalClockPairProbabilityMeasure sigma)
    ((continuous_fst.add continuous_snd).measurable.aemeasurable)

private theorem map_exponential_prod_residual_zero_add :
    ProbabilityMeasure.map
        (mobiusCriticalExponentialProbabilityMeasure.prod
          eulerSquareResidualZeroProbabilityMeasure)
        ((continuous_fst.add continuous_snd).measurable.aemeasurable) =
      mobiusCriticalExponentialProbabilityMeasure := by
  apply Subtype.ext
  change Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      ((mobiusCriticalExponentialProbabilityMeasure : Measure ℝ).prod
        (Measure.dirac 0)) =
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ)
  rw [Measure.prod_dirac]
  rw [Measure.map_map]
  · have hfun :
        ((fun p : ℝ × ℝ => p.1 + p.2) ∘ fun x : ℝ => (x, 0)) = id := by
      funext x
      simp
    rw [hfun, Measure.map_id]
  · fun_prop
  · fun_prop

/-- **Affine residual invisibility law.**  The physical affine Euler clock has exactly the same
critical weak limit as the squarefree clock. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockProbabilityMeasure :
    Tendsto eulerSquarefreeAffineCriticalClockProbabilityMeasure
      (nhdsWithin 1 (Ioi 1))
      (nhds mobiusCriticalExponentialProbabilityMeasure) := by
  have hpair : Tendsto
      (fun sigma : ℝ =>
        (squarefreeMobiusCriticalClockProbabilityMeasure sigma,
          eulerSquareResidualCriticalClockProbabilityMeasure sigma))
      (nhdsWithin 1 (Ioi 1))
      (nhds
        (mobiusCriticalExponentialProbabilityMeasure,
          eulerSquareResidualZeroProbabilityMeasure)) :=
    tendsto_squarefreeMobiusCriticalClockProbabilityMeasure.prodMk_nhds
      tendsto_eulerSquareResidualCriticalClockProbabilityMeasure
  have hprod : Tendsto
      (fun sigma : ℝ =>
        (squarefreeMobiusCriticalClockProbabilityMeasure sigma).prod
          (eulerSquareResidualCriticalClockProbabilityMeasure sigma))
      (nhdsWithin 1 (Ioi 1))
      (nhds
        (mobiusCriticalExponentialProbabilityMeasure.prod
          eulerSquareResidualZeroProbabilityMeasure)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  have hadd :=
    (ProbabilityMeasure.continuous_map (continuous_fst.add continuous_snd))
      |>.continuousAt.tendsto.comp hprod
  rw [map_exponential_prod_residual_zero_add] at hadd
  simpa [eulerSquarefreeAffineCriticalClockProbabilityMeasure,
    eulerSquarefreeAffineCriticalClockPairProbabilityMeasure] using! hadd

/-- Normalized logarithmic moment of the residual square coordinate. -/
def eulerSquareResidualLogMoment (k : ℕ) (sigma : ℝ) : ℝ :=
  ∑' n : ℕ,
    eulerSquareResidualProbability sigma n * Real.log n ^ k

theorem summable_eulerSquareResidualLogMoment
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      eulerSquareResidualProbability sigma n * Real.log n ^ k) := by
  have htotal : 0 < eulerSquareResidualTotal sigma :=
    eulerSquareResidualTotal_pos hsigma
  have hmajor :=
    (summable_abs_log_natCast_pow_mul_rpow_neg k (2 * sigma)
      (by linarith)).div_const (eulerSquareResidualTotal sigma)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    exact mul_nonneg (eulerSquareResidualProbability_nonneg hsigma n)
      (pow_nonneg (Real.log_natCast_nonneg n) k)
  · intro n
    rw [eulerSquareResidualProbability]
    by_cases hn : n = 0
    · subst n
      rw [eulerSquareResidualMass, if_pos rfl]
      simp only [zero_div, zero_mul, Nat.cast_zero, Real.log_zero]
      rw [Real.zero_rpow (by linarith : -(2 * sigma) ≠ 0)]
      positivity
    · rw [eulerSquareResidualMass, if_neg hn]
      rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
      ring_nf
      exact le_rfl

theorem eulerSquareResidualTotal_one_le
    {sigma : ℝ} (hsigma : 1 < sigma) :
    1 ≤ eulerSquareResidualTotal sigma := by
  have h :=
    (summable_eulerSquareResidualMass hsigma).le_tsum 1
      (fun n _ => eulerSquareResidualMass_nonneg sigma n)
  simpa [eulerSquareResidualTotal, eulerSquareResidualMass] using h

theorem eulerSquareResidualProbability_le_mass
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    eulerSquareResidualProbability sigma n ≤
      eulerSquareResidualMass sigma n := by
  rw [eulerSquareResidualProbability]
  exact div_le_self (eulerSquareResidualMass_nonneg sigma n)
    (eulerSquareResidualTotal_one_le hsigma)

private def eulerSquareResidualLogMomentMajorant (k : ℕ) : ℝ :=
  ∑' n : ℕ, |Real.log n| ^ k * (n : ℝ) ^ (-2 : ℝ)

private theorem summable_eulerSquareResidualLogMomentMajorant (k : ℕ) :
    Summable (fun n : ℕ =>
      |Real.log n| ^ k * (n : ℝ) ^ (-2 : ℝ)) :=
  summable_abs_log_natCast_pow_mul_rpow_neg k 2 (by norm_num)

private theorem eulerSquareResidualLogMomentMajorant_nonneg (k : ℕ) :
    0 ≤ eulerSquareResidualLogMomentMajorant k :=
  tsum_nonneg fun n => mul_nonneg (pow_nonneg (abs_nonneg _) k) (by positivity)

private theorem eulerSquareResidualLogMoment_le_majorant
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerSquareResidualLogMoment k sigma ≤
      eulerSquareResidualLogMomentMajorant k := by
  unfold eulerSquareResidualLogMoment eulerSquareResidualLogMomentMajorant
  apply Summable.tsum_le_tsum
  · intro n
    have hprob :=
      eulerSquareResidualProbability_le_mass hsigma n
    have hlog : 0 ≤ Real.log n ^ k :=
      pow_nonneg (Real.log_natCast_nonneg n) k
    have hmass :
        eulerSquareResidualMass sigma n ≤ (n : ℝ) ^ (-2 : ℝ) := by
      rw [eulerSquareResidualMass]
      by_cases hn : n = 0
      · subst n
        rw [if_pos rfl]
        exact Real.rpow_nonneg (by positivity) _
      · rw [if_neg hn]
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))
          (by linarith)
    calc
      eulerSquareResidualProbability sigma n * Real.log n ^ k ≤
          eulerSquareResidualMass sigma n * Real.log n ^ k :=
        mul_le_mul_of_nonneg_right hprob hlog
      _ ≤ (n : ℝ) ^ (-2 : ℝ) * Real.log n ^ k :=
        mul_le_mul_of_nonneg_right hmass hlog
      _ = |Real.log n| ^ k * (n : ℝ) ^ (-2 : ℝ) := by
        rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
        ring
  · exact summable_eulerSquareResidualLogMoment k hsigma
  · exact summable_eulerSquareResidualLogMomentMajorant k

theorem eulerSquareResidualLogMoment_nonneg
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    0 ≤ eulerSquareResidualLogMoment k sigma :=
  tsum_nonneg fun n =>
    mul_nonneg (eulerSquareResidualProbability_nonneg hsigma n)
      (pow_nonneg (Real.log_natCast_nonneg n) k)

/-- Raw moment of the residual critical clock. -/
def eulerSquareResidualCriticalClockMoment (k : ℕ) (sigma : ℝ) : ℝ :=
  ∑' n : ℕ,
    eulerSquareResidualProbability sigma n *
      eulerSquareResidualCriticalClock sigma n ^ k

theorem eulerSquareResidualCriticalClockMoment_eq
    (k : ℕ) (sigma : ℝ) :
    eulerSquareResidualCriticalClockMoment k sigma =
      (2 * (sigma - 1)) ^ k *
        eulerSquareResidualLogMoment k sigma := by
  unfold eulerSquareResidualCriticalClockMoment
    eulerSquareResidualLogMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold eulerSquareResidualCriticalClock
  rw [mul_pow]
  ring

/-- The residual square clock vanishes in first moment at the critical boundary. -/
theorem tendsto_eulerSquareResidualCriticalClockMoment_one :
    Tendsto (eulerSquareResidualCriticalClockMoment 1)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let C := eulerSquareResidualLogMomentMajorant 1
  have hmajor :
      Tendsto (fun sigma : ℝ => (2 * (sigma - 1)) * C)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hbase :
        Tendsto (fun sigma : ℝ => 2 * (sigma - 1))
          (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      have hcont : ContinuousAt (fun sigma : ℝ => 2 * (sigma - 1)) 1 := by
        fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hbase.mul_const C
  refine squeeze_zero'
    (g := fun sigma : ℝ => (2 * (sigma - 1)) * C) ?_ ?_ hmajor
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    rw [eulerSquareResidualCriticalClockMoment_eq 1 sigma, pow_one]
    exact mul_nonneg (by linarith)
      (eulerSquareResidualLogMoment_nonneg 1 hsigma)
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    rw [eulerSquareResidualCriticalClockMoment_eq 1 sigma, pow_one]
    exact mul_le_mul_of_nonneg_left
      (eulerSquareResidualLogMoment_le_majorant 1 hsigma) (by linarith)

/-- **Residual Fisher invisibility.**  The residual square clock vanishes in `L²` at the critical
boundary. -/
theorem tendsto_eulerSquareResidualCriticalClockMoment_two :
    Tendsto (eulerSquareResidualCriticalClockMoment 2)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let C := eulerSquareResidualLogMomentMajorant 2
  have hmajor :
      Tendsto (fun sigma : ℝ => (2 * (sigma - 1)) ^ 2 * C)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hbase :
        Tendsto (fun sigma : ℝ => 2 * (sigma - 1))
          (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      have hcont : ContinuousAt (fun sigma : ℝ => 2 * (sigma - 1)) 1 := by
        fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using (hbase.pow 2).mul_const C
  refine squeeze_zero'
    (g := fun sigma : ℝ => (2 * (sigma - 1)) ^ 2 * C) ?_ ?_ hmajor
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    rw [eulerSquareResidualCriticalClockMoment_eq 2 sigma]
    exact mul_nonneg (sq_nonneg _)
      (eulerSquareResidualLogMoment_nonneg 2 hsigma)
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    rw [eulerSquareResidualCriticalClockMoment_eq 2 sigma]
    exact mul_le_mul_of_nonneg_left
      (eulerSquareResidualLogMoment_le_majorant 2 hsigma) (sq_nonneg _)

/-- The residual clock is supported on the nonnegative half-line in the physical half-plane. -/
theorem eulerSquareResidualCriticalClockProbabilityMeasure_Iio_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ)
        (Iio 0) = 0 := by
  unfold eulerSquareResidualCriticalClockProbabilityMeasure
    eulerSquareResidualIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iio]
  have hpre :
      eulerSquareResidualCriticalClock sigma ⁻¹' Iio 0 = ∅ := by
    ext n
    constructor
    · intro hn
      exact (not_lt_of_ge
        (mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (sub_nonneg.mpr hsigma.le))
          (Real.log_natCast_nonneg n))) hn
    · intro hn
      exact hn.elim
  rw [hpre, measure_empty]

private theorem ae_eulerSquareResidualCriticalClock_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ∀ᵐ y ∂(eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ),
      0 ≤ y := by
  rw [ae_iff]
  simpa only [not_le] using!
    eulerSquareResidualCriticalClockProbabilityMeasure_Iio_zero hsigma

/-- The squarefree clock is supported on the nonnegative half-line in the physical half-plane. -/
theorem squarefreeMobiusCriticalClockProbabilityMeasure_Iio_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
        (Iio 0) = 0 := by
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iio]
  have hpre : squarefreeMobiusCriticalClock sigma ⁻¹' Iio 0 = ∅ := by
    ext n
    constructor
    · intro hn
      exact (not_lt_of_ge
        (mul_nonneg (sub_nonneg.mpr hsigma.le)
          (Real.log_natCast_nonneg n))) hn
    · intro hn
      exact hn.elim
  rw [hpre, measure_empty]

/-- The physical affine Euler clock is supported on the nonnegative half-line. -/
theorem eulerSquarefreeAffineCriticalClockProbabilityMeasure_Iio_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma : Measure ℝ)
        (Iio 0) = 0 := by
  let μ :=
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
  let ν :=
    (eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ)
  have hx : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le] using!
      squarefreeMobiusCriticalClockProbabilityMeasure_Iio_zero hsigma
  have hy : ∀ᵐ y ∂ν, 0 ≤ y := by
    exact ae_eulerSquareResidualCriticalClock_nonneg hsigma
  have hpair : ∀ᵐ p ∂μ.prod ν, 0 ≤ p.1 + p.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hx] with x hx'
    filter_upwards [hy] with y hy'
    linarith
  unfold eulerSquarefreeAffineCriticalClockProbabilityMeasure
    eulerSquarefreeAffineCriticalClockPairProbabilityMeasure
    ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  change μ.prod ν {p : ℝ × ℝ | p.1 + p.2 < 0} = 0
  simpa only [not_le] using (ae_iff.mp hpair)

/-- Universal cap--cut decomposition for a nonnegative probability clock. -/
theorem positiveClockCapMoment_eq_cutMoment_add_tail
    (mu : ProbabilityMeasure ℝ)
    (hmu : (mu : Measure ℝ) (Iio 0) = 0)
    (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ x : ℝ, positiveClockCap u x ^ k ∂(mu : Measure ℝ)) =
      (∫ x : ℝ in Iic u, x ^ k ∂(mu : Measure ℝ)) +
        u ^ k * (1 - ProbabilityTheory.cdf (mu : Measure ℝ) u) := by
  let f : ℝ → ℝ := fun x => positiveClockCap u x ^ k
  have hf : Integrable f (mu : Measure ℝ) := by
    exact BoundedContinuousFunction.integrable (mu : Measure ℝ)
      (positiveClockCapPowBCF k u hu)
  have hnonneg : ∀ᵐ x ∂(mu : Measure ℝ), 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le] using! hmu
  have hleft :
      (∫ x : ℝ in Iic u, f x ∂(mu : Measure ℝ)) =
        ∫ x : ℝ in Iic u, x ^ k ∂(mu : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic,
      ae_restrict_of_ae hnonneg] with x hxu hx0
    unfold f positiveClockCap
    rw [max_eq_left hx0, min_eq_left hxu]
  have hright :
      (∫ x : ℝ in (Iic u)ᶜ, f x ∂(mu : Measure ℝ)) =
        u ^ k * (1 - ProbabilityTheory.cdf (mu : Measure ℝ) u) := by
    rw [compl_Iic]
    calc
      (∫ x : ℝ in Ioi u, f x ∂(mu : Measure ℝ)) =
          ∫ _x : ℝ in Ioi u, u ^ k ∂(mu : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hxu
        unfold f positiveClockCap
        rw [max_eq_left (hu.trans hxu.le), min_eq_right hxu.le]
      _ = (mu : Measure ℝ).real (Ioi u) * u ^ k := by
        rw [integral_const]
        rw [measureReal_restrict_apply_univ]
        simp only [smul_eq_mul]
      _ = u ^ k * (1 - ProbabilityTheory.cdf (mu : Measure ℝ) u) := by
        rw [← compl_Iic,
          MeasureTheory.measureReal_compl measurableSet_Iic,
          ProbabilityTheory.cdf_eq_real]
        simp only [probReal_univ]
        ring
  rw [← integral_add_compl measurableSet_Iic hf, hleft, hright]

/-- The `k`-th physical affine Euler critical-clock moment below the hard window. -/
def eulerSquarefreeAffineCriticalClockCutMoment
    (k : ℕ) (sigma u : ℝ) : ℝ :=
  ∫ x : ℝ in Iic u, x ^ k
    ∂(eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma : Measure ℝ)

/-- The `k`-th positively capped physical affine Euler critical-clock moment. -/
def eulerSquarefreeAffineCriticalClockCappedMoment
    (k : ℕ) (sigma u : ℝ) : ℝ :=
  ∫ x : ℝ, positiveClockCap u x ^ k
    ∂(eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma : Measure ℝ)

/-- Exact cap--cut law for the physical affine Euler clock. -/
theorem eulerSquarefreeAffineCriticalClockCappedMoment_eq_cutMoment_add_tail
    (k : ℕ) {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerSquarefreeAffineCriticalClockCappedMoment k sigma u =
      eulerSquarefreeAffineCriticalClockCutMoment k sigma u +
        u ^ k *
          (1 - ProbabilityTheory.cdf
            (eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma :
              Measure ℝ) u) := by
  exact positiveClockCapMoment_eq_cutMoment_add_tail
    (eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma)
    (eulerSquarefreeAffineCriticalClockProbabilityMeasure_Iio_zero hsigma)
    k hu

private theorem tendsto_eulerSquarefreeAffineCriticalClockCappedMoment
    (k : ℕ) {u L : ℝ} (hu : 0 ≤ u)
    (hsquarefree :
      Tendsto
        (fun sigma : ℝ =>
          squarefreeMobiusCriticalClockCappedMoment k sigma u)
        (nhdsWithin 1 (Ioi 1)) (nhds L)) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCappedMoment k sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds L) := by
  let F := positiveClockCapPowBCF k u hu
  have heuler :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      tendsto_eulerSquarefreeAffineCriticalClockProbabilityMeasure) F
  have hsquareWeak :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      tendsto_squarefreeMobiusCriticalClockProbabilityMeasure) F
  change Tendsto (fun sigma : ℝ =>
      ∫ x : ℝ, positiveClockCap u x ^ k
        ∂(eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma :
          Measure ℝ))
      (nhdsWithin 1 (Ioi 1))
      (nhds (∫ x : ℝ, positiveClockCap u x ^ k
        ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ))) at heuler
  change Tendsto (fun sigma : ℝ =>
      ∫ x : ℝ, positiveClockCap u x ^ k
        ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ))
      (nhdsWithin 1 (Ioi 1))
      (nhds (∫ x : ℝ, positiveClockCap u x ^ k
        ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ))) at hsquareWeak
  have hsquareIntegral : Tendsto (fun sigma : ℝ =>
      ∫ x : ℝ, positiveClockCap u x ^ k
        ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds L) := by
    apply hsquarefree.congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact
      (integral_positiveClockCap_pow_squarefreeMobiusCriticalClock
        k hsigma hu).symm
  have hvalue :
      (∫ x : ℝ, positiveClockCap u x ^ k
        ∂(mobiusCriticalExponentialProbabilityMeasure : Measure ℝ)) = L :=
    tendsto_nhds_unique hsquareWeak hsquareIntegral
  rw [hvalue] at heuler
  exact heuler

/-- The physical affine capped first moment has the universal exponential limit. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCappedMoment_one
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCappedMoment 1 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (1 - Real.exp (-u))) :=
  tendsto_eulerSquarefreeAffineCriticalClockCappedMoment 1 hu
    (tendsto_squarefreeMobiusCriticalClockCappedMoment_one hu)

/-- The physical affine capped second moment has the universal exponential limit. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCappedMoment_two
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCappedMoment 2 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 - 2 * (u + 1) * Real.exp (-u))) :=
  tendsto_eulerSquarefreeAffineCriticalClockCappedMoment 2 hu
    (tendsto_squarefreeMobiusCriticalClockCappedMoment_two hu)

/-- CDF of the physical affine Euler critical clock. -/
def eulerSquarefreeAffineCriticalClockCDF (sigma u : ℝ) : ℝ :=
  ProbabilityTheory.cdf
    (eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma : Measure ℝ) u

/-- The physical affine Euler CDF has the same critical exponential limit as the squarefree CDF. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCDF (u : ℝ) :
    Tendsto (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if 0 ≤ u then 1 - Real.exp (-u) else 0)) := by
  have hnull :
      mobiusCriticalExponentialProbabilityMeasure (frontier (Iic u)) = 0 := by
    rw [frontier_Iic]
    ext
    simp [mobiusCriticalExponentialProbabilityMeasure,
      ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  have hmeasure :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      tendsto_eulerSquarefreeAffineCriticalClockProbabilityMeasure hnull
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp hmeasure
  have hreal' : Tendsto (fun sigma : ℝ =>
      ProbabilityTheory.cdf
        (eulerSquarefreeAffineCriticalClockProbabilityMeasure sigma : Measure ℝ) u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (ProbabilityTheory.cdf
        (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) u)) := by
    simpa [Function.comp_apply, ProbabilityTheory.cdf_eq_real, Measure.real,
      ProbabilityMeasure.coe_mk] using! hreal
  have hlimit := ProbabilityTheory.cdf_expMeasure_eq (r := (1 : ℝ))
    (by norm_num) u
  simpa [eulerSquarefreeAffineCriticalClockCDF,
    mobiusCriticalExponentialProbabilityMeasure, hlimit] using hreal'

/-- Exact hard-cut first-moment limit for the physical affine Euler clock. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCutMoment_one
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCutMoment 1 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (1 - (u + 1) * Real.exp (-u))) := by
  have hmass :
      Tendsto
        (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using
      tendsto_eulerSquarefreeAffineCriticalClockCDF u
  have hcap := tendsto_eulerSquarefreeAffineCriticalClockCappedMoment_one hu
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have hu' : Tendsto (fun _ : ℝ => u)
      (nhdsWithin 1 (Ioi 1)) (nhds u) := tendsto_const_nhds
  have h := hcap.sub (hu'.mul (hone.sub hmass))
  have hvalue :
      (1 - Real.exp (-u)) -
          u * (1 - (1 - Real.exp (-u))) =
        1 - (u + 1) * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [eulerSquarefreeAffineCriticalClockCappedMoment_eq_cutMoment_add_tail
    1 hsigma hu]
  simp only [pow_one, eulerSquarefreeAffineCriticalClockCDF]
  ring

/-- Exact hard-cut second-moment limit for the physical affine Euler clock. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCutMoment_two
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCutMoment 2 sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u))) := by
  have hmass :
      Tendsto
        (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using
      tendsto_eulerSquarefreeAffineCriticalClockCDF u
  have hcap := tendsto_eulerSquarefreeAffineCriticalClockCappedMoment_two hu
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have hu' : Tendsto (fun _ : ℝ => u ^ 2)
      (nhdsWithin 1 (Ioi 1)) (nhds (u ^ 2)) := tendsto_const_nhds
  have h := hcap.sub (hu'.mul (hone.sub hmass))
  have hvalue :
      (2 - 2 * (u + 1) * Real.exp (-u)) -
          u ^ 2 * (1 - (1 - Real.exp (-u))) =
        2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [eulerSquarefreeAffineCriticalClockCappedMoment_eq_cutMoment_add_tail
    2 hsigma hu]
  simp only [eulerSquarefreeAffineCriticalClockCDF]
  ring

/-- Physical affine cutoff displacement relative to the squarefree cutoff. -/
def eulerSquarefreeAffineCriticalClockCutoffDisplacement
    (sigma u : ℝ) : ℝ :=
  squarefreeMobiusCriticalClockCDF sigma u -
    eulerSquarefreeAffineCriticalClockCDF sigma u

/-- The affine Euler cutoff is stochastically later than its squarefree component. -/
theorem eulerSquarefreeAffineCriticalClockCutoffDisplacement_nonneg
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    0 ≤ eulerSquarefreeAffineCriticalClockCutoffDisplacement sigma u := by
  rw [eulerSquarefreeAffineCriticalClockCutoffDisplacement, sub_nonneg]
  let μ :=
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
  let ν :=
    (eulerSquareResidualCriticalClockProbabilityMeasure sigma : Measure ℝ)
  have hν : ∀ᵐ y ∂ν, 0 ≤ y := by
    exact ae_eulerSquareResidualCriticalClock_nonneg hsigma
  have hpair : ∀ᵐ p ∂μ.prod ν, p.1 + p.2 ≤ u → p.1 ≤ u := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards with x
    filter_upwards [hν] with y hy
    intro hxy
    linarith
  unfold squarefreeMobiusCriticalClockCDF
    eulerSquarefreeAffineCriticalClockCDF
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  unfold eulerSquarefreeAffineCriticalClockProbabilityMeasure
    eulerSquarefreeAffineCriticalClockPairProbabilityMeasure
    ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
  change (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) (Iic u)).toReal ≤
    (μ (Iic u)).toReal
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hle :
      μ.prod ν ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iic u) ≤
        μ.prod ν (Prod.fst ⁻¹' Iic u) := by
    apply measure_mono_ae
    filter_upwards [hpair] with p hp
    exact hp
  have hfinite : μ.prod ν (Prod.fst ⁻¹' Iic u) ≠ ∞ := by finiteness
  rw [← Measure.map_apply measurable_fst measurableSet_Iic,
    Measure.map_fst_prod, measure_univ, one_smul] at hle hfinite
  exact ENNReal.toReal_mono hfinite hle

/-- **Affine cutoff invisibility.**  At every fixed window, probability mass displaced by the
physical square channel vanishes at the critical boundary. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockCutoffDisplacement
    (u : ℝ) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalClockCutoffDisplacement sigma u)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hsq := tendsto_squarefreeMobiusCriticalClockCDF u
  have heuler := tendsto_eulerSquarefreeAffineCriticalClockCDF u
  simpa [eulerSquarefreeAffineCriticalClockCutoffDisplacement] using
    hsq.sub heuler

/-- Mean of the physical affine Euler clock, resolved into its two independent source channels. -/
def eulerSquarefreeAffineCriticalClockMean (sigma : ℝ) : ℝ :=
  (sigma - 1) * squarefreeMobiusLogMoment 1 sigma +
    eulerSquareResidualCriticalClockMoment 1 sigma

/-- Raw second moment of the physical affine Euler clock. -/
def eulerSquarefreeAffineCriticalClockSecondMoment (sigma : ℝ) : ℝ :=
  (sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma +
    2 * ((sigma - 1) * squarefreeMobiusLogMoment 1 sigma) *
      eulerSquareResidualCriticalClockMoment 1 sigma +
    eulerSquareResidualCriticalClockMoment 2 sigma

/-- Variance of the physical affine Euler clock. -/
def eulerSquarefreeAffineCriticalClockVariance (sigma : ℝ) : ℝ :=
  eulerSquarefreeAffineCriticalClockSecondMoment sigma -
    eulerSquarefreeAffineCriticalClockMean sigma ^ 2

/-- Exact independent-channel variance addition for the affine Euler clock. -/
theorem eulerSquarefreeAffineCriticalClockVariance_eq_add
    (sigma : ℝ) :
    eulerSquarefreeAffineCriticalClockVariance sigma =
      squarefreeMobiusCriticalClockVariance sigma +
        (eulerSquareResidualCriticalClockMoment 2 sigma -
          eulerSquareResidualCriticalClockMoment 1 sigma ^ 2) := by
  unfold eulerSquarefreeAffineCriticalClockVariance
    eulerSquarefreeAffineCriticalClockSecondMoment
    eulerSquarefreeAffineCriticalClockMean
    squarefreeMobiusCriticalClockVariance
  ring

/-- The full Euler clock has critical mean one. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockMean :
    Tendsto eulerSquarefreeAffineCriticalClockMean
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have h :=
    tendsto_squarefreeMobiusLogMoment_one_critical.add
      tendsto_eulerSquareResidualCriticalClockMoment_one
  simpa [eulerSquarefreeAffineCriticalClockMean] using! h

/-- **Critical square-invariance law.**  Adding every Euler square channel leaves the critical
clock variance equal to one. -/
theorem tendsto_eulerSquarefreeAffineCriticalClockVariance :
    Tendsto eulerSquarefreeAffineCriticalClockVariance
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have hresidual :
      Tendsto
        (fun sigma : ℝ =>
          eulerSquareResidualCriticalClockMoment 2 sigma -
            eulerSquareResidualCriticalClockMoment 1 sigma ^ 2)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using tendsto_eulerSquareResidualCriticalClockMoment_two.sub
      (tendsto_eulerSquareResidualCriticalClockMoment_one.pow 2)
  have h := tendsto_squarefreeMobiusCriticalClockVariance.add hresidual
  have heq : (fun sigma : ℝ =>
      squarefreeMobiusCriticalClockVariance sigma +
        (eulerSquareResidualCriticalClockMoment 2 sigma -
          eulerSquareResidualCriticalClockMoment 1 sigma ^ 2)) =ᶠ[
      nhdsWithin 1 (Ioi 1)] eulerSquarefreeAffineCriticalClockVariance :=
    Filter.Eventually.of_forall fun sigma =>
      (eulerSquarefreeAffineCriticalClockVariance_eq_add sigma).symm
  simpa using h.congr' heq

/-- Projective Fisher energy of the physical affine Euler source. -/
def eulerSquarefreeAffineCriticalProjectiveFisherEnergy (sigma : ℝ) : ℝ :=
  4 * eulerSquarefreeAffineCriticalClockVariance sigma

/-- **Full-Euler four-unit law.**  The actual affine Euler source, including every square channel,
carries exactly the universal four-unit critical Fisher budget. -/
theorem tendsto_eulerSquarefreeAffineCriticalProjectiveFisherEnergy :
    Tendsto eulerSquarefreeAffineCriticalProjectiveFisherEnergy
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  simpa [eulerSquarefreeAffineCriticalProjectiveFisherEnergy] using!
    tendsto_const_nhds.mul
      tendsto_eulerSquarefreeAffineCriticalClockVariance

/-- Square channels contribute no asymptotic projective Fisher energy beyond the squarefree
source. -/
theorem tendsto_eulerSquarefreeAffineFisherEnergy_sub_squarefree :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalProjectiveFisherEnergy sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  simpa using
    tendsto_eulerSquarefreeAffineCriticalProjectiveFisherEnergy.sub
      tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy

/-- Centered state--Fisher-tangent Gram entry below the physical affine Euler hard cutoff. -/
def eulerSquarefreeAffineCriticalFisherCutOverlap (sigma u : ℝ) : ℝ :=
  -2 * (eulerSquarefreeAffineCriticalClockCutMoment 1 sigma u -
    eulerSquarefreeAffineCriticalClockMean sigma *
      eulerSquarefreeAffineCriticalClockCDF sigma u)

/-- Centered Fisher-tangent energy below the physical affine Euler hard cutoff. -/
def eulerSquarefreeAffineCriticalFisherCutEnergy (sigma u : ℝ) : ℝ :=
  4 * (eulerSquarefreeAffineCriticalClockCutMoment 2 sigma u -
    2 * eulerSquarefreeAffineCriticalClockMean sigma *
      eulerSquarefreeAffineCriticalClockCutMoment 1 sigma u +
    eulerSquarefreeAffineCriticalClockMean sigma ^ 2 *
      eulerSquarefreeAffineCriticalClockCDF sigma u)

/-- Exact critical limit of the physical affine Euler truncated state--tangent overlap. -/
theorem tendsto_eulerSquarefreeAffineCriticalFisherCutOverlap
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalFisherCutOverlap sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 * u * Real.exp (-u))) := by
  have hmass :
      Tendsto
        (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using
      tendsto_eulerSquarefreeAffineCriticalClockCDF u
  have hfirst :=
    tendsto_eulerSquarefreeAffineCriticalClockCutMoment_one hu
  have hmean := tendsto_eulerSquarefreeAffineCriticalClockMean
  have hnegTwo : Tendsto (fun _ : ℝ => (-2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds (-2)) := tendsto_const_nhds
  have h := hnegTwo.mul (hfirst.sub (hmean.mul hmass))
  have hvalue :
      (-2 : ℝ) * ((1 - (u + 1) * Real.exp (-u)) -
        1 * (1 - Real.exp (-u))) = 2 * u * Real.exp (-u) := by
    ring
  rw [hvalue] at h
  simpa [eulerSquarefreeAffineCriticalFisherCutOverlap] using h

/-- Exact critical limit of physical affine Euler hard-cut Fisher energy. -/
theorem tendsto_eulerSquarefreeAffineCriticalFisherCutEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalFisherCutEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (4 * (1 - (1 + u ^ 2) * Real.exp (-u)))) := by
  have hmass :
      Tendsto
        (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using
      tendsto_eulerSquarefreeAffineCriticalClockCDF u
  have hfirst :=
    tendsto_eulerSquarefreeAffineCriticalClockCutMoment_one hu
  have hsecond :=
    tendsto_eulerSquarefreeAffineCriticalClockCutMoment_two hu
  have hmean := tendsto_eulerSquarefreeAffineCriticalClockMean
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := tendsto_const_nhds
  have hfour : Tendsto (fun _ : ℝ => (4 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := tendsto_const_nhds
  have hcentered := hsecond.sub ((htwo.mul hmean).mul hfirst) |>.add
    ((hmean.pow 2).mul hmass)
  have h := hfour.mul hcentered
  have hvalue :
      (4 : ℝ) * ((2 - (u ^ 2 + 2 * u + 2) * Real.exp (-u)) -
        2 * 1 * (1 - (u + 1) * Real.exp (-u)) +
        1 ^ 2 * (1 - Real.exp (-u))) =
        4 * (1 - (1 + u ^ 2) * Real.exp (-u)) := by
    ring
  rw [hvalue] at h
  simpa [eulerSquarefreeAffineCriticalFisherCutEnergy] using h

/-- Physical affine Euler source Ward Gram energy at finite inverse temperature. -/
def eulerSquarefreeAffineCriticalFisherCutoffWardEnergy
    (sigma u : ℝ) : ℝ :=
  (eulerSquarefreeAffineCriticalProjectiveFisherEnergy sigma -
      eulerSquarefreeAffineCriticalFisherCutEnergy sigma u) *
    eulerSquarefreeAffineCriticalClockCDF sigma u +
  (1 - eulerSquarefreeAffineCriticalClockCDF sigma u) *
    eulerSquarefreeAffineCriticalFisherCutEnergy sigma u -
  2 * eulerSquarefreeAffineCriticalFisherCutOverlap sigma u ^ 2

/-- **Physical affine Euler Ward law.**  The actual all-integer Euler cutoff has exactly the
squarefree four-unit Ward profile at criticality. -/
theorem tendsto_eulerSquarefreeAffineCriticalFisherCutoffWardEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalFisherCutoffWardEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (squarefreeMobiusCriticalFisherCutoffWardLimit u)) := by
  have hmass :
      Tendsto
        (fun sigma : ℝ => eulerSquarefreeAffineCriticalClockCDF sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - Real.exp (-u))) := by
    simpa only [if_pos hu] using
      tendsto_eulerSquarefreeAffineCriticalClockCDF u
  have htotal :=
    tendsto_eulerSquarefreeAffineCriticalProjectiveFisherEnergy
  have hcut := tendsto_eulerSquarefreeAffineCriticalFisherCutEnergy hu
  have hoverlap :=
    tendsto_eulerSquarefreeAffineCriticalFisherCutOverlap hu
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := tendsto_const_nhds
  have h := ((htotal.sub hcut).mul hmass).add
      ((hone.sub hmass).mul hcut) |>.sub
    (htwo.mul (hoverlap.pow 2))
  have hvalue :
      ((4 - 4 * (1 - (1 + u ^ 2) * Real.exp (-u))) *
          (1 - Real.exp (-u)) +
        (1 - (1 - Real.exp (-u))) *
          (4 * (1 - (1 + u ^ 2) * Real.exp (-u))) -
        2 * (2 * u * Real.exp (-u)) ^ 2) =
        squarefreeMobiusCriticalFisherCutoffWardLimit u := by
    rw [squarefreeMobiusCriticalFisherCutoffWardLimit_eq_gram]
    ring
  rw [hvalue] at h
  simpa [eulerSquarefreeAffineCriticalFisherCutoffWardEnergy] using h

/-- The physical affine Euler Ward law has sharp four-unit boundary density. -/
theorem tendsto_eulerSquarefreeAffineCriticalFisherWardBoundaryDensity :
    Tendsto
      (fun u : ℝ =>
        squarefreeMobiusCriticalFisherCutoffWardLimit u / (2 * u))
      (nhdsWithin 0 (Ioi 0)) (nhds 4) :=
  tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul

end RHTower
