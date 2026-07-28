import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator
import GaloisForLFunctions.HTGeometry.FiniteSpectralDressingStability
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect
import GaloisForLFunctions.RHTower.HypertranscendentalQuartetWardIndex
import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectDifferentialRank
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

/-!
# Compact-open Kolchin blindness and quantized Ward-charge escape

An off-critical functional-equation quartet can move to infinite height while:

* its normalized polynomial gauge converges locally uniformly to one;
* the gauged completed Xi function and every holomorphic jet converge locally uniformly to Xi;
* hypertranscendence and every rational-base differential-family matroid remain unchanged;
* its nonnegative Ward density retains exact mass `8π`, although it vanishes uniformly on every
  bounded height window.

The missing datum is the source-marked divisor charge at the noncompact height boundary.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances

/-! ## Escaping normalized quartet -/

/-- Canonical height tending to infinity. -/
def escapingQuartetHeight (n : ℕ) : ℝ := n + 1

/-- Reciprocal canonical height. -/
def escapingQuartetScale (n : ℕ) : ℝ := (escapingQuartetHeight n)⁻¹

/-- The centered quartet gauge normalized to tend to one on compact sets. -/
def normalizedEscapingQuartetGauge (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (1 + (escapingQuartetScale n : ℂ) ^ 2 *
      ((s - (1 / 2 : ℂ)) - (a : ℂ)) ^ 2) *
    (1 + (escapingQuartetScale n : ℂ) ^ 2 *
      ((s - (1 / 2 : ℂ)) + (a : ℂ)) ^ 2)

/-- Completed Xi with one normalized quartet at canonical height `n+1`. -/
def escapingQuartetGaugedXi (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  normalizedEscapingQuartetGauge a n s * xi s

theorem escapingQuartetHeight_pos (n : ℕ) :
    0 < escapingQuartetHeight n := by
  unfold escapingQuartetHeight
  positivity

theorem escapingQuartetScale_ne_zero (n : ℕ) :
    escapingQuartetScale n ≠ 0 := by
  exact inv_ne_zero (ne_of_gt (escapingQuartetHeight_pos n))

/-- Exact identification with the old quartic gauge divided by height to the fourth power. -/
theorem normalizedEscapingQuartetGauge_eq
    (a : ℝ) (n : ℕ) (s : ℂ) :
    normalizedEscapingQuartetGauge a n s =
      ((escapingQuartetScale n : ℂ) ^ 4) *
        centeredQuartetGauge a (escapingQuartetHeight n) s := by
  unfold normalizedEscapingQuartetGauge centeredQuartetGauge
    escapingQuartetScale
  have hb : (escapingQuartetHeight n : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (ne_of_gt (escapingQuartetHeight_pos n))
  push_cast
  field_simp [hb]
  ring

theorem escapingQuartetGaugedXi_eq
    (a : ℝ) (n : ℕ) :
    escapingQuartetGaugedXi a n =
      fun s => ((escapingQuartetScale n : ℂ) ^ 4) *
        quartetGaugedXi a (escapingQuartetHeight n) s := by
  funext s
  rw [escapingQuartetGaugedXi, normalizedEscapingQuartetGauge_eq,
    quartetGaugedXi]
  ring

/-! ## Exact analytic and differential-algebraic data -/

theorem escapingQuartetGaugedXi_hypertranscendental
    (a : ℝ) (n : ℕ) :
    Hypertranscendental (escapingQuartetGaugedXi a n) := by
  rw [escapingQuartetGaugedXi_eq]
  apply
    (hypertranscendental_const_mul_iff
      (pow_ne_zero 4 (ofReal_ne_zero.mpr (escapingQuartetScale_ne_zero n)))).2
  exact quartetGaugedXi_hypertranscendental (escapingQuartetHeight_pos n)

theorem escapingQuartetGaugedXi_analyticAt
    (a : ℝ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (escapingQuartetGaugedXi a n) s := by
  rw [escapingQuartetGaugedXi_eq]
  exact analyticAt_const.mul
    (quartetGaugedXi_analyticAt a (escapingQuartetHeight n) s)

theorem escapingQuartetGaugedXi_one_sub
    (a : ℝ) (n : ℕ) (s : ℂ) :
    escapingQuartetGaugedXi a n (1 - s) =
      escapingQuartetGaugedXi a n s := by
  rw [escapingQuartetGaugedXi_eq]
  change (escapingQuartetScale n : ℂ) ^ 4 *
      quartetGaugedXi a (escapingQuartetHeight n) (1 - s) =
    (escapingQuartetScale n : ℂ) ^ 4 *
      quartetGaugedXi a (escapingQuartetHeight n) s
  rw [quartetGaugedXi_one_sub]

theorem escapingQuartetGaugedXi_conj
    (a : ℝ) (n : ℕ) (s : ℂ) :
    escapingQuartetGaugedXi a n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (escapingQuartetGaugedXi a n s) := by
  rw [escapingQuartetGaugedXi_eq]
  change (escapingQuartetScale n : ℂ) ^ 4 *
      quartetGaugedXi a (escapingQuartetHeight n) ((starRingEnd ℂ) s) =
    (starRingEnd ℂ) ((escapingQuartetScale n : ℂ) ^ 4 *
      quartetGaugedXi a (escapingQuartetHeight n) s)
  rw [quartetGaugedXi_conj, map_mul, map_pow, Complex.conj_ofReal]

theorem escapingQuartetGaugedXi_real_anchor_ne_zero
    {a σ : ℝ} (n : ℕ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    escapingQuartetGaugedXi a n (σ : ℂ) ≠ 0 := by
  rw [escapingQuartetGaugedXi_eq]
  exact mul_ne_zero
    (pow_ne_zero 4 (ofReal_ne_zero.mpr (escapingQuartetScale_ne_zero n)))
    (quartetGaugedXi_real_anchor_ne_zero
      (escapingQuartetHeight_pos n) hσ0 hσ1)

theorem escapingQuartetGaugedXi_added_zero
    (a : ℝ) (n : ℕ) :
    escapingQuartetGaugedXi a n
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
  rw [escapingQuartetGaugedXi_eq]
  change (escapingQuartetScale n : ℂ) ^ 4 *
      quartetGaugedXi a (escapingQuartetHeight n)
        (quartetPoint a (escapingQuartetHeight n)) = 0
  rw [quartetGaugedXi_quartetPoint, mul_zero]

theorem escapingQuartetGaugedXi_added_zero_off_critical
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 :=
  quartetPoint_off_critical ha

/-! ## Exact rational logarithmic correction -/

/-- Polynomial whose evaluation is the normalized escaping gauge. -/
def normalizedEscapingQuartetPolynomial (a : ℝ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.C ((escapingQuartetScale n : ℂ) ^ 4) *
    centeredQuartetPolynomial a (escapingQuartetHeight n)

theorem normalizedEscapingQuartetPolynomial_eval
    (a : ℝ) (n : ℕ) (s : ℂ) :
    Polynomial.eval s (normalizedEscapingQuartetPolynomial a n) =
      normalizedEscapingQuartetGauge a n s := by
  rw [normalizedEscapingQuartetPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, centeredQuartetPolynomial_eval,
    normalizedEscapingQuartetGauge_eq]

theorem normalizedEscapingQuartetPolynomial_ne_zero
    (a : ℝ) (n : ℕ) :
    normalizedEscapingQuartetPolynomial a n ≠ 0 := by
  unfold normalizedEscapingQuartetPolynomial
  apply mul_ne_zero
  · simp [escapingQuartetScale_ne_zero]
  · exact centeredQuartetPolynomial_ne_zero (escapingQuartetHeight_pos n)

/-- The logarithmic source correction is literally a rational function: derivative polynomial
divided by the polynomial itself. -/
theorem normalizedEscapingQuartetGauge_logDeriv_eq_polynomial
    (a : ℝ) (n : ℕ) (s : ℂ) :
    logDeriv (normalizedEscapingQuartetGauge a n) s =
      Polynomial.eval s (normalizedEscapingQuartetPolynomial a n).derivative /
        Polynomial.eval s (normalizedEscapingQuartetPolynomial a n) := by
  have hfun : normalizedEscapingQuartetGauge a n =
      fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n) := by
    funext z
    exact (normalizedEscapingQuartetPolynomial_eval a n z).symm
  rw [hfun]
  rw [logDeriv_apply, Polynomial.deriv]

/-- Even-shift logarithmic-source defect. -/
def evenShiftLogDerivDefect (F : ℂ → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  logDeriv F (s + (2 * m : ℕ)) - logDeriv F s

/-- Explicit rational correction induced by the normalized quartet gauge. -/
def escapingQuartetEvenShiftCorrection
    (a : ℝ) (n m : ℕ) (s : ℂ) : ℂ :=
  Polynomial.eval (s + (2 * m : ℕ))
      (normalizedEscapingQuartetPolynomial a n).derivative /
      Polynomial.eval (s + (2 * m : ℕ))
        (normalizedEscapingQuartetPolynomial a n) -
    Polynomial.eval s (normalizedEscapingQuartetPolynomial a n).derivative /
      Polynomial.eval s (normalizedEscapingQuartetPolynomial a n)

theorem normalizedEscapingQuartetGauge_evenShiftLogDerivDefect_eq_rational
    (a : ℝ) (n m : ℕ) (s : ℂ) :
    evenShiftLogDerivDefect (normalizedEscapingQuartetGauge a n) m s =
      escapingQuartetEvenShiftCorrection a n m s := by
  rw [evenShiftLogDerivDefect, escapingQuartetEvenShiftCorrection,
    normalizedEscapingQuartetGauge_logDeriv_eq_polynomial,
    normalizedEscapingQuartetGauge_logDeriv_eq_polynomial]

/-- Away from the sampled divisor, quartet surgery changes every even-shift Xi defect by exactly
the explicit rational correction above. -/
theorem escapingQuartetGaugedXi_evenShiftLogDerivDefect_eq
    (a : ℝ) (n m : ℕ) (s : ℂ)
    (hGs : normalizedEscapingQuartetGauge a n s ≠ 0)
    (hGsm : normalizedEscapingQuartetGauge a n (s + (2 * m : ℕ)) ≠ 0)
    (hxis : xi s ≠ 0) (hxism : xi (s + (2 * m : ℕ)) ≠ 0) :
    evenShiftLogDerivDefect (escapingQuartetGaugedXi a n) m s =
      evenShiftLogDerivDefect xi m s +
        escapingQuartetEvenShiftCorrection a n m s := by
  unfold evenShiftLogDerivDefect escapingQuartetGaugedXi
  rw [logDeriv_mul (s + (2 * m : ℕ)) hGsm hxism,
    logDeriv_mul s hGs hxis]
  · rw [normalizedEscapingQuartetGauge_logDeriv_eq_polynomial,
      normalizedEscapingQuartetGauge_logDeriv_eq_polynomial]
    unfold escapingQuartetEvenShiftCorrection
    ring
  all_goals
    first
    | exact (escapingQuartetGaugedXi_analyticAt a n _).differentiableAt
    | unfold normalizedEscapingQuartetGauge; fun_prop
    | exact xi_differentiable _

/-! ## Compact-open convergence, including every holomorphic jet -/

theorem escapingQuartetScale_tendsto_zero :
    Tendsto escapingQuartetScale atTop (nhds 0) := by
  unfold escapingQuartetScale escapingQuartetHeight
  have h :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp

theorem escapingQuartetScale_sq_complex_tendsto_zero :
    Tendsto (fun n : ℕ => (escapingQuartetScale n : ℂ) ^ 2)
      atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => (escapingQuartetScale n : ℂ))
      atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp escapingQuartetScale_tendsto_zero
  simpa using hcast.pow 2

private theorem normalizedEscapingQuartetFactor_tendstoLocallyUniformly
    (a : ℝ) (sign : ℂ) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (s : ℂ) =>
        1 + (escapingQuartetScale n : ℂ) ^ 2 *
          ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2)
      (fun _ : ℂ => 1) atTop := by
  have hcoeff : TendstoLocallyUniformly
      (fun n (_ : ℂ) => (escapingQuartetScale n : ℂ) ^ 2)
      (fun _ : ℂ => 0) atTop := by
    have hu : TendstoUniformly
        (fun n (_ : ℂ) => (escapingQuartetScale n : ℂ) ^ 2)
        (fun _ : ℂ => 0) atTop :=
      escapingQuartetScale_sq_complex_tendsto_zero.tendstoUniformly_const
    exact hu.tendstoLocallyUniformly
  have hshape : TendstoLocallyUniformly
      (fun _n : ℕ => fun s : ℂ =>
        ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2)
      (fun s : ℂ => ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2) atTop :=
    tendstoLocallyUniformly_const_sequence _
  have hmul := hcoeff.mul₀ hshape continuous_const (by fun_prop)
  have hone : TendstoLocallyUniformly
      (fun _n : ℕ => fun _s : ℂ => (1 : ℂ))
      (fun _s : ℂ => (1 : ℂ)) atTop :=
    tendstoLocallyUniformly_const_sequence _
  have hadd : TendstoLocallyUniformly
      ((fun _n : ℕ => fun _s : ℂ => (1 : ℂ)) +
        ((fun n (_ : ℂ) => (escapingQuartetScale n : ℂ) ^ 2) *
          (fun _n : ℕ => fun s : ℂ =>
            ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2)))
      ((fun _s : ℂ => (1 : ℂ)) +
        ((fun _ : ℂ => (0 : ℂ)) *
          (fun s : ℂ => ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2)))
      atTop :=
    TendstoLocallyUniformly.add (α := ℂ) (ι := ℕ) (X := ℂ) hone hmul
  change TendstoLocallyUniformly
    (fun n s => 1 + (escapingQuartetScale n : ℂ) ^ 2 *
      ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2)
    (fun s => 1 + 0 *
      ((s - (1 / 2 : ℂ)) + sign * (a : ℂ)) ^ 2) atTop at hadd
  simpa using hadd

theorem normalizedEscapingQuartetGauge_tendstoLocallyUniformly
    (a : ℝ) :
    TendstoLocallyUniformly
      (normalizedEscapingQuartetGauge a) (fun _ : ℂ => 1) atTop := by
  have hminus :=
    normalizedEscapingQuartetFactor_tendstoLocallyUniformly a (-1)
  have hplus :=
    normalizedEscapingQuartetFactor_tendstoLocallyUniformly a 1
  have hprod := hminus.mul₀ hplus continuous_const continuous_const
  convert hprod using 1
  · funext n s
    dsimp [normalizedEscapingQuartetGauge]
    ring
  · funext s
    simp

theorem escapingQuartetGaugedXi_tendstoLocallyUniformly
    (a : ℝ) :
    TendstoLocallyUniformly
      (escapingQuartetGaugedXi a) xi atTop := by
  have hxi : TendstoLocallyUniformly (fun _n : ℕ => xi) xi atTop :=
    tendstoLocallyUniformly_const_sequence xi
  have hxiContinuous : Continuous xi :=
    continuous_iff_continuousAt.mpr fun s =>
      (xi_analyticOnNhd_univ s (Set.mem_univ s)).continuousAt
  have hprod :=
    (normalizedEscapingQuartetGauge_tendstoLocallyUniformly a).mul₀
      hxi continuous_const hxiContinuous
  change TendstoLocallyUniformly
      (fun n s => normalizedEscapingQuartetGauge a n s * xi s)
      (fun s => 1 * xi s) atTop at hprod
  simpa only [escapingQuartetGaugedXi, one_mul] using hprod

/-- Every holomorphic jet of the escaping countermodels converges compact-open to the
corresponding Xi jet. -/
theorem escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly
    (a : ℝ) (j : ℕ) :
    TendstoLocallyUniformly
      (fun n => iteratedDeriv j (escapingQuartetGaugedXi a n))
      (iteratedDeriv j xi) atTop := by
  have hconvOn : TendstoLocallyUniformlyOn
      (escapingQuartetGaugedXi a) xi atTop Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      escapingQuartetGaugedXi_tendstoLocallyUniformly a
  have hdiff : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (escapingQuartetGaugedXi a n) Set.univ :=
    Filter.Eventually.of_forall fun n =>
      fun s _ =>
        (escapingQuartetGaugedXi_analyticAt a n s).differentiableAt.differentiableWithinAt
  have hj :=
    iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
      isOpen_univ hconvOn hdiff j
  simpa [tendstoLocallyUniformlyOn_univ] using hj

/-! ## Quantized Ward charge escapes every bounded window -/

theorem quartetWardInfinitesimalDensity_window_bound
    {a b R t : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (hR : 0 ≤ R) (hbR : R < b) (ht : |t| ≤ R) :
    quartetWardInfinitesimalDensity a b t ≤ 8 / (b - R) ^ 2 := by
  have hx0 : 0 < a + 1 / 2 := by linarith
  have hx1 : a + 1 / 2 < 1 := by linarith
  have hgap : 0 < b - R := sub_pos.mpr hbR
  have htlo : -R ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ R := (abs_le.mp ht).2
  have hplus : b - R ≤ t + b := by linarith
  have hminus : b - R ≤ b - t := by linarith
  have hplusSq : (b - R) ^ 2 ≤ (t + b) ^ 2 :=
    (sq_le_sq₀ hgap.le (le_trans hgap.le hplus)).2 hplus
  have hminusSq : (b - R) ^ 2 ≤ (t - b) ^ 2 := by
    rw [show (t - b) ^ 2 = (b - t) ^ 2 by ring]
    exact (sq_le_sq₀ hgap.le (le_trans hgap.le hminus)).2 hminus
  have hdenPlus : (b - R) ^ 2 ≤
      (a + 1 / 2) ^ 2 + (t + b) ^ 2 := by nlinarith [sq_nonneg (a + 1 / 2)]
  have hdenMinus : (b - R) ^ 2 ≤
      (a + 1 / 2) ^ 2 + (t - b) ^ 2 := by nlinarith [sq_nonneg (a + 1 / 2)]
  have hgapSq : 0 < (b - R) ^ 2 := sq_pos_of_pos hgap
  have hfracPlus :
      2 * (a + 1 / 2) /
          ((a + 1 / 2) ^ 2 + (t + b) ^ 2) ≤
        2 / (b - R) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) hgapSq).2
    nlinarith
  have hfracMinus :
      2 * (a + 1 / 2) /
          ((a + 1 / 2) ^ 2 + (t - b) ^ 2) ≤
        2 / (b - R) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) hgapSq).2
    nlinarith
  unfold quartetWardInfinitesimalDensity
  calc
    2 * (2 * (a + 1 / 2) /
          ((a + 1 / 2) ^ 2 + (t + b) ^ 2) +
        2 * (a + 1 / 2) /
          ((a + 1 / 2) ^ 2 + (t - b) ^ 2)) ≤
        2 * (2 / (b - R) ^ 2 + 2 / (b - R) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hfracPlus hfracMinus) (by norm_num)
    _ = 8 / (b - R) ^ 2 := by ring

theorem escapingQuartetWard_window_tendstoUniformly
    {a R : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun n t => quartetWardInfinitesimalDensity a
        (escapingQuartetHeight n) t)
      (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hdenTop : Tendsto
      (fun n : ℕ => escapingQuartetHeight n - R) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (1 - R)
      (tendsto_natCast_atTop_atTop (R := ℝ))
    convert h using 1
    funext n
    dsimp [escapingQuartetHeight]
    push_cast
    ring
  have hboundZero : Tendsto
      (fun n : ℕ => 8 / (escapingQuartetHeight n - R) ^ 2)
      atTop (nhds 0) := by
    have hinvZero : Tendsto
        (fun n : ℕ => (escapingQuartetHeight n - R)⁻¹)
        atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hdenTop
    have hsquareZero := hinvZero.pow 2
    convert hsquareZero.const_mul 8 using 1
    funext n
    field_simp
    ring
  filter_upwards [hboundZero.eventually (Metric.ball_mem_nhds 0 hε),
    hdenTop.eventually_gt_atTop 0] with n hn hgap t ht
  have hheight : R < escapingQuartetHeight n := by linarith
  have hboundNonneg :
      0 ≤ 8 / (escapingQuartetHeight n - R) ^ 2 := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hboundNonneg] at hn
  have hnonneg : 0 ≤ quartetWardInfinitesimalDensity a
      (escapingQuartetHeight n) t :=
    quartetWardInfinitesimalDensity_nonneg
      (a := a) (b := escapingQuartetHeight n)
        (by linarith : 0 < a + 1 / 2) t
  have hlt := lt_of_le_of_lt
    (quartetWardInfinitesimalDensity_window_bound
      ha0 ha1 hR hheight ht) hn
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

theorem escapingQuartetWard_mass
    {a : ℝ} (ha0 : 0 < a) (n : ℕ) :
    ∫⁻ t : ℝ, ENNReal.ofReal
      (quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t) =
        ENNReal.ofReal (8 * π) :=
  lintegral_quartetWardInfinitesimalDensity (by linarith)

/-! ## Arbitrarily large invisible divisor charge -/

/-- The normalized escaping quartet repeated with divisor multiplicity `N`. -/
def multiplicityEscapingQuartetGauge
    (a : ℝ) (N n : ℕ) (s : ℂ) : ℂ :=
  normalizedEscapingQuartetGauge a n s ^ N

/-- Completed Xi with an escaping quartet of arbitrary prescribed multiplicity. -/
def multiplicityEscapingQuartetGaugedXi
    (a : ℝ) (N n : ℕ) (s : ℂ) : ℂ :=
  multiplicityEscapingQuartetGauge a N n s * xi s

/-- Polynomial representative of the multiplicity-`N` normalized gauge. -/
def multiplicityEscapingQuartetPolynomial
    (a : ℝ) (N n : ℕ) : Polynomial ℂ :=
  normalizedEscapingQuartetPolynomial a n ^ N

theorem multiplicityEscapingQuartetPolynomial_eval
    (a : ℝ) (N n : ℕ) (s : ℂ) :
    Polynomial.eval s (multiplicityEscapingQuartetPolynomial a N n) =
      multiplicityEscapingQuartetGauge a N n s := by
  simp [multiplicityEscapingQuartetPolynomial,
    multiplicityEscapingQuartetGauge,
    normalizedEscapingQuartetPolynomial_eval]

theorem multiplicityEscapingQuartetPolynomial_ne_zero
    (a : ℝ) (N n : ℕ) :
    multiplicityEscapingQuartetPolynomial a N n ≠ 0 :=
  pow_ne_zero N (normalizedEscapingQuartetPolynomial_ne_zero a n)

theorem multiplicityEscapingQuartetGaugedXi_hypertranscendental
    (a : ℝ) (N n : ℕ) :
    Hypertranscendental (multiplicityEscapingQuartetGaugedXi a N n) := by
  have hxiSmooth : ContDiff ℂ (⊤ : ℕ∞) xi :=
    xi_analyticOnNhd_univ.contDiff
  have hfun :
      multiplicityEscapingQuartetGaugedXi a N n =
        fun s : ℂ =>
          Polynomial.eval s (multiplicityEscapingQuartetPolynomial a N n) * xi s := by
    funext s
    rw [multiplicityEscapingQuartetGaugedXi,
      multiplicityEscapingQuartetPolynomial_eval]
  rw [hfun]
  exact hypertranscendental_mul_polynomial hxiSmooth
    (multiplicityEscapingQuartetPolynomial_ne_zero a N n)
    xi_hypertranscendental

theorem multiplicityEscapingQuartetGaugedXi_analyticAt
    (a : ℝ) (N n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (multiplicityEscapingQuartetGaugedXi a N n) s := by
  change AnalyticAt ℂ
    (fun z => normalizedEscapingQuartetGauge a n z ^ N * xi z) s
  have hG : AnalyticAt ℂ
      (fun z => normalizedEscapingQuartetGauge a n z) s := by
    have hfun : (fun z => normalizedEscapingQuartetGauge a n z) =
        fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n) := by
      funext z
      exact (normalizedEscapingQuartetPolynomial_eval a n z).symm
    rw [hfun]
    simpa using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) s).aeval_polynomial
        (normalizedEscapingQuartetPolynomial a n)
  exact (hG.pow N).mul
      (xi_analyticOnNhd_univ s (Set.mem_univ s))

theorem normalizedEscapingQuartetGauge_one_sub
    (a : ℝ) (n : ℕ) (s : ℂ) :
    normalizedEscapingQuartetGauge a n (1 - s) =
      normalizedEscapingQuartetGauge a n s := by
  rw [normalizedEscapingQuartetGauge_eq,
    normalizedEscapingQuartetGauge_eq, centeredQuartetGauge_one_sub]

theorem normalizedEscapingQuartetGauge_conj
    (a : ℝ) (n : ℕ) (s : ℂ) :
    normalizedEscapingQuartetGauge a n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (normalizedEscapingQuartetGauge a n s) := by
  rw [normalizedEscapingQuartetGauge_eq,
    normalizedEscapingQuartetGauge_eq, centeredQuartetGauge_conj,
    map_mul, map_pow, Complex.conj_ofReal]

theorem multiplicityEscapingQuartetGaugedXi_one_sub
    (a : ℝ) (N n : ℕ) (s : ℂ) :
    multiplicityEscapingQuartetGaugedXi a N n (1 - s) =
      multiplicityEscapingQuartetGaugedXi a N n s := by
  simp only [multiplicityEscapingQuartetGaugedXi,
    multiplicityEscapingQuartetGauge,
    normalizedEscapingQuartetGauge_one_sub, xi_one_sub]

theorem multiplicityEscapingQuartetGaugedXi_conj
    (a : ℝ) (N n : ℕ) (s : ℂ) :
    multiplicityEscapingQuartetGaugedXi a N n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (multiplicityEscapingQuartetGaugedXi a N n s) := by
  simp only [multiplicityEscapingQuartetGaugedXi,
    multiplicityEscapingQuartetGauge,
    normalizedEscapingQuartetGauge_conj, xi_conj, map_mul, map_pow]

theorem multiplicityEscapingQuartetGaugedXi_real_anchor_ne_zero
    {a σ : ℝ} (N n : ℕ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    multiplicityEscapingQuartetGaugedXi a N n (σ : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · apply pow_ne_zero
    intro hzero
    apply escapingQuartetGaugedXi_real_anchor_ne_zero
      (a := a) (σ := σ) n hσ0 hσ1
    rw [escapingQuartetGaugedXi, hzero, zero_mul]
  · intro hzero
    apply escapingQuartetGaugedXi_real_anchor_ne_zero
      (a := a) (σ := σ) n hσ0 hσ1
    rw [escapingQuartetGaugedXi, hzero, mul_zero]

theorem multiplicityEscapingQuartetGaugedXi_added_zero
    (a : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    multiplicityEscapingQuartetGaugedXi a N n
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
  have hG : normalizedEscapingQuartetGauge a n
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
    rw [normalizedEscapingQuartetGauge_eq,
      centeredQuartetGauge_quartetPoint, mul_zero]
  simp [multiplicityEscapingQuartetGaugedXi,
    multiplicityEscapingQuartetGauge, hG, Nat.ne_of_gt hN]

/-- For each fixed multiplicity, normalized gauges converge compact-open to one. -/
theorem multiplicityEscapingQuartetGauge_tendstoLocallyUniformly
    (a : ℝ) (N : ℕ) :
    TendstoLocallyUniformly
      (fun n => multiplicityEscapingQuartetGauge a N n)
      (fun _ : ℂ => 1) atTop := by
  induction N with
  | zero =>
      simpa [multiplicityEscapingQuartetGauge] using
        (tendstoLocallyUniformly_const_sequence (fun _ : ℂ => 1))
  | succ N ih =>
      have hmul := ih.mul₀
        (normalizedEscapingQuartetGauge_tendstoLocallyUniformly a)
        continuous_const continuous_const
      have hsource :
          (fun n => multiplicityEscapingQuartetGauge a (N + 1) n) =
            (fun n => multiplicityEscapingQuartetGauge a N n) *
              normalizedEscapingQuartetGauge a := by
        funext n s
        exact pow_succ (normalizedEscapingQuartetGauge a n s) N
      have htarget :
          (fun _ : ℂ => (1 : ℂ)) =
            (fun _ : ℂ => (1 : ℂ)) * (fun _ : ℂ => (1 : ℂ)) := by
        funext s
        simp
      rw [hsource, htarget]
      exact hmul

/-- For every prescribed divisor multiplicity, the countermodels converge compact-open to Xi. -/
theorem multiplicityEscapingQuartetGaugedXi_tendstoLocallyUniformly
    (a : ℝ) (N : ℕ) :
    TendstoLocallyUniformly
      (fun n => multiplicityEscapingQuartetGaugedXi a N n)
      xi atTop := by
  have hxi : TendstoLocallyUniformly (fun _n : ℕ => xi) xi atTop :=
    tendstoLocallyUniformly_const_sequence xi
  have hxiContinuous : Continuous xi :=
    continuous_iff_continuousAt.mpr fun s =>
      (xi_analyticOnNhd_univ s (Set.mem_univ s)).continuousAt
  have hprod :=
    (multiplicityEscapingQuartetGauge_tendstoLocallyUniformly a N).mul₀
      hxi continuous_const hxiContinuous
  change TendstoLocallyUniformly
      (fun n s => multiplicityEscapingQuartetGauge a N n s * xi s)
      (fun s => 1 * xi s) atTop at hprod
  simpa only [multiplicityEscapingQuartetGaugedXi, one_mul] using hprod

/-- Every holomorphic jet converges compact-open even at arbitrarily prescribed finite divisor
multiplicity. -/
theorem multiplicityEscapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly
    (a : ℝ) (N j : ℕ) :
    TendstoLocallyUniformly
      (fun n => iteratedDeriv j (multiplicityEscapingQuartetGaugedXi a N n))
      (iteratedDeriv j xi) atTop := by
  have hconvOn : TendstoLocallyUniformlyOn
      (fun n => multiplicityEscapingQuartetGaugedXi a N n)
      xi atTop Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      multiplicityEscapingQuartetGaugedXi_tendstoLocallyUniformly a N
  have hdiff : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (multiplicityEscapingQuartetGaugedXi a N n) Set.univ :=
    Filter.Eventually.of_forall fun n =>
      fun s _ =>
        (multiplicityEscapingQuartetGaugedXi_analyticAt a N n s).differentiableAt.differentiableWithinAt
  have hj :=
    iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
      isOpen_univ hconvOn hdiff j
  simpa [tendstoLocallyUniformlyOn_univ] using hj

/-- Aggregate Ward density of a quartet repeated with multiplicity `N`. -/
def multiplicityEscapingQuartetWardDensity
    (a : ℝ) (N n : ℕ) (t : ℝ) : ℝ :=
  N * quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t

/-- Aggregate Ward density still disappears on every bounded window for each prescribed
multiplicity. -/
theorem multiplicityEscapingQuartetWard_window_tendstoUniformly
    {a R : ℝ} (N : ℕ) (ha0 : 0 < a) (ha1 : a < 1 / 2) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun n => multiplicityEscapingQuartetWardDensity a N n)
      (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hN : N = 0
  · subst N
    simp [multiplicityEscapingQuartetWardDensity, hε]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hbase := escapingQuartetWard_window_tendstoUniformly ha0 ha1 hR
    rw [Metric.tendstoUniformlyOn_iff] at hbase
    filter_upwards [hbase (ε / N) (div_pos hε hNpos)] with n hn t ht
    have hnonneg : 0 ≤ quartetWardInfinitesimalDensity a
        (escapingQuartetHeight n) t :=
      quartetWardInfinitesimalDensity_nonneg
        (by linarith : 0 < a + 1 / 2) t
    have hprodnonneg : 0 ≤ (N : ℝ) *
        quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t :=
      mul_nonneg (Nat.cast_nonneg N) hnonneg
    have hdist := hn t ht
    simp only [Real.dist_eq, zero_sub, abs_neg, sub_zero,
      abs_of_nonneg hnonneg] at hdist
    simp only [multiplicityEscapingQuartetWardDensity, Real.dist_eq,
      zero_sub, abs_neg, sub_zero, abs_of_nonneg hprodnonneg]
    calc
      (N : ℝ) * quartetWardInfinitesimalDensity a
          (escapingQuartetHeight n) t <
        (N : ℝ) * (ε / N) :=
          mul_lt_mul_of_pos_left hdist hNpos
      _ = ε := by field_simp

/-- Ward mass of the repeated quartet. -/
def multiplicityEscapingQuartetWardMass
    (a : ℝ) (N n : ℕ) : ENNReal :=
  ∫⁻ t : ℝ, ENNReal.ofReal
    (multiplicityEscapingQuartetWardDensity a N n t)

/-- Every escaping quartet multiplicity carries exactly `N` quanta of `8π`. -/
theorem multiplicityEscapingQuartetWardMass_eq
    {a : ℝ} (ha0 : 0 < a) (N n : ℕ) :
    multiplicityEscapingQuartetWardMass a N n =
      N • ENNReal.ofReal (8 * π) := by
  unfold multiplicityEscapingQuartetWardMass
    multiplicityEscapingQuartetWardDensity
  simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
  calc
    (∫⁻ t : ℝ, (N : ENNReal) * ENNReal.ofReal
        (quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t)) =
        (N : ENNReal) * ∫⁻ t : ℝ, ENNReal.ofReal
          (quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t) :=
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = N • ENNReal.ofReal (8 * π) := by
      rw [escapingQuartetWard_mass ha0]
      simp [nsmul_eq_mul]

/-- The multiplicity-`N` surgery changes every even-shift Xi defect by `N` times the same
explicit rational correction. -/
theorem multiplicityEscapingQuartetGaugedXi_evenShiftLogDerivDefect_eq
    (a : ℝ) (N n m : ℕ) (s : ℂ)
    (hGs : normalizedEscapingQuartetGauge a n s ≠ 0)
    (hGsm : normalizedEscapingQuartetGauge a n (s + (2 * m : ℕ)) ≠ 0)
    (hxis : xi s ≠ 0) (hxism : xi (s + (2 * m : ℕ)) ≠ 0) :
    evenShiftLogDerivDefect (multiplicityEscapingQuartetGaugedXi a N n) m s =
      evenShiftLogDerivDefect xi m s +
        N * escapingQuartetEvenShiftCorrection a n m s := by
  have hGdiff : ∀ z, DifferentiableAt ℂ
      (normalizedEscapingQuartetGauge a n) z := by
    intro z
    unfold normalizedEscapingQuartetGauge
    fun_prop
  unfold evenShiftLogDerivDefect multiplicityEscapingQuartetGaugedXi
    multiplicityEscapingQuartetGauge
  rw [logDeriv_mul
      (f := fun z => normalizedEscapingQuartetGauge a n z ^ N)
      (g := xi) (s + (2 * m : ℕ)) (pow_ne_zero N hGsm) hxism
      ((hGdiff _).pow N) (xi_differentiable _),
    logDeriv_mul
      (f := fun z => normalizedEscapingQuartetGauge a n z ^ N)
      (g := xi) s (pow_ne_zero N hGs) hxis
      ((hGdiff _).pow N) (xi_differentiable _),
    logDeriv_fun_pow (hGdiff (s + (2 * m : ℕ))) N,
    logDeriv_fun_pow (hGdiff s) N,
    normalizedEscapingQuartetGauge_logDeriv_eq_polynomial,
    normalizedEscapingQuartetGauge_logDeriv_eq_polynomial]
  unfold escapingQuartetEvenShiftCorrection
  push_cast
  ring

/-! ## Abstract exact Kolchin blindness -/

/-- Any coordinatewise correction already in the rational differential base leaves the complete
represented matroid unchanged. This is the exact HT-geometric mechanism used by every rational
quartet logarithmic correction. -/
theorem rationalCorrection_preserves_upperEndDifferentialMatroid
    {A : Type*} (x : A → upperEndMeroField)
    (r : A → upperEndRationalCoordinateField) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => x a +
          algebraMap upperEndRationalCoordinateField upperEndMeroField (r a)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField) x :=
  differentialFamilyMatroid_addBase_eq x r

/-- Rational correction remains invisible after adjoining every scalar Euler valuation layer. -/
theorem rationalCorrection_preserves_allValuationDifferentialMatroid
    {A : Type*} (x : A → upperEndMeroField)
    (r : A → analyticScalarValuationLayerDifferentialField) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a => x a +
          algebraMap analyticScalarValuationLayerDifferentialField upperEndMeroField (r a)) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField) x :=
  differentialFamilyMatroid_addBase_eq x r

/-! ## The actual quartet correction inside the upper-end rational base -/

/-- Substitute the upper-end spectral coordinate `s=-iz+c` into a polynomial. -/
def upperEndSpectralSubstitutionPolynomial (c : ℂ) : Polynomial ℂ :=
  Polynomial.C (-I) * Polynomial.X + Polynomial.C c

/-- The exact rational function
`q(-iz+2m)-q(-iz)`, where `q=P'/P` is the quartet logarithmic correction. -/
def escapingQuartetEvenShiftCorrectionRatFunc
    (a : ℝ) (n m : ℕ) : RatFunc ℂ :=
  let P := normalizedEscapingQuartetPolynomial a n
  let σm := upperEndSpectralSubstitutionPolynomial ((2 * m : ℕ) : ℂ)
  let σ0 := upperEndSpectralSubstitutionPolynomial 0
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.derivative.comp σm) /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp σm) -
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.derivative.comp σ0) /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp σ0)

/-- Concrete quartet correction as an element of the genuine `ℂ(z)` coefficient field. -/
def escapingQuartetEvenShiftCorrectionCoordinate
    (a : ℝ) (n m : ℕ) : upperEndRationalCoordinateField :=
  upperEndRatfuncToRationalCoordinateField
    (escapingQuartetEvenShiftCorrectionRatFunc a n m)

/-- Raw Xi even-shift carrier after the exact rational quartet correction. -/
def escapingQuartetEvenShiftUpperEndCarrier
    (a : ℝ) (n m : ℕ) : upperEndMeroField :=
  xiEvenShiftRawLogDerivDefectUpperEndCarrier m +
    algebraMap upperEndRationalCoordinateField upperEndMeroField
      (escapingQuartetEvenShiftCorrectionCoordinate a n m)

/-- Every packet of quartet-gauged carriers generates exactly the same differential field as the
actual raw Xi packet over the rational coordinate base. -/
theorem escapingQuartetEvenShiftUpperEndCarrier_differentialAdjoin_eq_raw
    {A : Type*} (a : ℝ) (n : ℕ) (grade : A → ℕ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun q =>
          escapingQuartetEvenShiftUpperEndCarrier a n (grade q)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun q =>
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  unfold escapingQuartetEvenShiftUpperEndCarrier
  simpa using differentialAdjoin_range_affineBase_eq
    (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q))
    (fun _ => 1)
    (fun q => escapingQuartetEvenShiftCorrectionCoordinate a n (grade q))
    (fun _ => one_ne_zero)

/-- Exact rational quartet surgery preserves the complete represented Xi shift matroid. -/
theorem escapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw
    {A : Type*} (a : ℝ) (n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q => escapingQuartetEvenShiftUpperEndCarrier a n (grade q)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  unfold escapingQuartetEvenShiftUpperEndCarrier
  exact differentialFamilyMatroid_addBase_eq _ _

/-- Consequently the quartet-gauged packet has the same exact pointed-collision matroid as Xi:
zero grades are loops, repeated grades are parallel, and distinct positive grades are free. -/
theorem escapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (a : ℝ) (n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q => escapingQuartetEvenShiftUpperEndCarrier a n (grade q)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [escapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision]

/-- The same concrete correction inside the field containing every scalar prime-valuation
layer. -/
def escapingQuartetEvenShiftCorrectionAllValuation
    (a : ℝ) (n m : ℕ) :
    analyticScalarValuationLayerDifferentialField :=
  ⟨(escapingQuartetEvenShiftCorrectionCoordinate a n m : upperEndMeroField),
    IntermediateField.algebraMap_mem
      analyticScalarValuationLayerDifferentialField
      (escapingQuartetEvenShiftCorrectionCoordinate a n m)⟩

/-- Exact quartet surgery remains matroid-invisible after adjoining every scalar Euler valuation
layer. -/
theorem escapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw
    {A : Type*} (a : ℝ) (n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q => escapingQuartetEvenShiftUpperEndCarrier a n (grade q)) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  change differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q) +
        algebraMap analyticScalarValuationLayerDifferentialField upperEndMeroField
          (escapingQuartetEvenShiftCorrectionAllValuation a n (grade q))) = _
  exact differentialFamilyMatroid_addBase_eq _ _

/-- The full all-valuation pointed-collision law survives every escaping quartet surgery. -/
theorem escapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
    {A : Type*} (a : ℝ) (n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q => escapingQuartetEvenShiftUpperEndCarrier a n (grade q)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [escapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision]

/-! ## Arbitrary charge remains in the identical Kolchin stratum -/

/-- Exact rational coordinate correction for quartet multiplicity `N`. -/
def multiplicityEscapingQuartetEvenShiftCorrectionCoordinate
    (a : ℝ) (N n m : ℕ) : upperEndRationalCoordinateField :=
  N • escapingQuartetEvenShiftCorrectionCoordinate a n m

/-- Xi even-shift carrier after a quartet surgery of multiplicity `N`. -/
def multiplicityEscapingQuartetEvenShiftUpperEndCarrier
    (a : ℝ) (N n m : ℕ) : upperEndMeroField :=
  xiEvenShiftRawLogDerivDefectUpperEndCarrier m +
    algebraMap upperEndRationalCoordinateField upperEndMeroField
      (multiplicityEscapingQuartetEvenShiftCorrectionCoordinate a N n m)

/-- Every prescribed divisor multiplicity generates exactly the raw Xi differential field. -/
theorem multiplicityEscapingQuartetEvenShiftUpperEndCarrier_differentialAdjoin_eq_raw
    {A : Type*} (a : ℝ) (N n : ℕ) (grade : A → ℕ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun q =>
          multiplicityEscapingQuartetEvenShiftUpperEndCarrier a N n (grade q)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun q =>
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  unfold multiplicityEscapingQuartetEvenShiftUpperEndCarrier
  simpa using differentialAdjoin_range_affineBase_eq
    (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q))
    (fun _ => 1)
    (fun q =>
      multiplicityEscapingQuartetEvenShiftCorrectionCoordinate a N n (grade q))
    (fun _ => one_ne_zero)

/-- Every prescribed divisor multiplicity has exactly the raw Xi represented differential
matroid over the rational coordinate field. -/
theorem multiplicityEscapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw
    {A : Type*} (a : ℝ) (N n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q =>
          multiplicityEscapingQuartetEvenShiftUpperEndCarrier a N n (grade q)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  unfold multiplicityEscapingQuartetEvenShiftUpperEndCarrier
  exact differentialFamilyMatroid_addBase_eq _ _

/-- Consequently every charge level retains the exact pointed-collision Xi matroid. -/
theorem multiplicityEscapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (a : ℝ) (N n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun q =>
          multiplicityEscapingQuartetEvenShiftUpperEndCarrier a N n (grade q)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [multiplicityEscapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision]

/-- Multiplicity correction embedded into the field containing all scalar Euler valuations. -/
def multiplicityEscapingQuartetEvenShiftCorrectionAllValuation
    (a : ℝ) (N n m : ℕ) :
    analyticScalarValuationLayerDifferentialField :=
  ⟨(multiplicityEscapingQuartetEvenShiftCorrectionCoordinate a N n m :
      upperEndMeroField),
    IntermediateField.algebraMap_mem
      analyticScalarValuationLayerDifferentialField
      (multiplicityEscapingQuartetEvenShiftCorrectionCoordinate a N n m)⟩

/-- Arbitrarily large Ward charge remains invisible even after adjoining every scalar
prime-valuation layer. -/
theorem multiplicityEscapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw
    {A : Type*} (a : ℝ) (N n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q =>
          multiplicityEscapingQuartetEvenShiftUpperEndCarrier a N n (grade q)) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q)) := by
  change differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun q => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade q) +
        algebraMap analyticScalarValuationLayerDifferentialField upperEndMeroField
          (multiplicityEscapingQuartetEvenShiftCorrectionAllValuation
            a N n (grade q))) = _
  exact differentialFamilyMatroid_addBase_eq _ _

/-- Every charge level has the pointed-collision Xi matroid over the full scalar-valuation base. -/
theorem
    multiplicityEscapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
    {A : Type*} (a : ℝ) (N n : ℕ) (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun q =>
          multiplicityEscapingQuartetEvenShiftUpperEndCarrier a N n (grade q)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [
    multiplicityEscapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision]

/-! ## The common divisor mode is differentially free -/

/-- Universal local law: the logarithmic derivative of a nonzero analytic germ has an exact
simple pole at every zero, independently of its multiplicity. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one_of_analyticAt
    {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfinite : analyticOrderAt f ρ ≠ ⊤) (hzero : f ρ = 0) :
    meromorphicOrderAt (logDeriv f) ρ = ((-1 : ℤ) : WithTop ℤ) := by
  have hmne : (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt f ρ = 0 := by
      rw [(ENat.coe_toNat hfinite).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hf
    · exact h hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt f ρ = (k + 1 : ℕ) := by
    calc
      analyticOrderAt f ρ = ((analyticOrderAt f ρ).toNat : ℕ∞) :=
        (ENat.coe_toNat hfinite).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv f) ρ = k :=
    analyticOrderAt_deriv_of_pos hf horder
  rw [show logDeriv f = deriv f / f by
    funext z
    rw [logDeriv_apply]
    rfl]
  rw [meromorphicOrderAt_div hf.deriv.meromorphicAt hf.meromorphicAt,
    hf.deriv.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq,
    hderiv, horder, ENat.map_coe, ENat.map_coe]
  exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)

/-- The rational multiplicity gauge has finite local vanishing order everywhere. -/
theorem multiplicityEscapingQuartetGauge_analyticOrderAt_ne_top
    (a : ℝ) (N n : ℕ) (ρ : ℂ) :
    analyticOrderAt (multiplicityEscapingQuartetGauge a N n) ρ ≠ ⊤ := by
  have hP : multiplicityEscapingQuartetPolynomial a N n ≠ 0 :=
    multiplicityEscapingQuartetPolynomial_ne_zero a N n
  have hfun : multiplicityEscapingQuartetGauge a N n =
      fun z => Polynomial.eval z (multiplicityEscapingQuartetPolynomial a N n) := by
    funext z
    exact (multiplicityEscapingQuartetPolynomial_eval a N n z).symm
  rw [hfun,
    Bottcher.analyticOrderAt_polynomial_eval_eq_rootMultiplicity hP]
  exact WithTop.coe_ne_top

/-- Every positive multiplicity makes the displayed off-critical point a source-gauge zero. -/
theorem multiplicityEscapingQuartetGauge_added_zero
    (a : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    multiplicityEscapingQuartetGauge a N n
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
  have hG : normalizedEscapingQuartetGauge a n
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
    rw [normalizedEscapingQuartetGauge_eq,
      centeredQuartetGauge_quartetPoint, mul_zero]
  simp [multiplicityEscapingQuartetGauge, hG, Nat.ne_of_gt hN]

/-- The marked rational source correction has an exact simple pole at the inserted divisor,
independently of its positive multiplicity. -/
theorem multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole
    (a : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    meromorphicOrderAt
        (logDeriv (multiplicityEscapingQuartetGauge a N n))
        (quartetPoint a (escapingQuartetHeight n)) =
      ((-1 : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one_of_analyticAt
  · have hfun : multiplicityEscapingQuartetGauge a N n =
        fun z => Polynomial.eval z
          (multiplicityEscapingQuartetPolynomial a N n) := by
      funext z
      exact (multiplicityEscapingQuartetPolynomial_eval a N n z).symm
    rw [hfun]
    simpa using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z)
        (quartetPoint a (escapingQuartetHeight n))).aeval_polynomial
          (multiplicityEscapingQuartetPolynomial a N n)
  · exact multiplicityEscapingQuartetGauge_analyticOrderAt_ne_top a N n _
  · exact multiplicityEscapingQuartetGauge_added_zero a hN n

/-- The escaping countermodel is not locally zero at any point. -/
theorem escapingQuartetGaugedXi_analyticOrderAt_ne_top
    (a : ℝ) (n : ℕ) (ρ : ℂ) :
    analyticOrderAt (escapingQuartetGaugedXi a n) ρ ≠ ⊤ := by
  have hP : normalizedEscapingQuartetPolynomial a n ≠ 0 :=
    normalizedEscapingQuartetPolynomial_ne_zero a n
  have hPan : AnalyticAt ℂ
      (fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n)) ρ := by
    simpa using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) ρ).aeval_polynomial
        (normalizedEscapingQuartetPolynomial a n)
  have hxi : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have hfun : escapingQuartetGaugedXi a n =
      fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n) * xi z := by
    funext z
    rw [escapingQuartetGaugedXi, normalizedEscapingQuartetPolynomial_eval]
  rw [hfun]
  have hord : analyticOrderAt
      (fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n) * xi z) ρ =
      analyticOrderAt
          (fun z => Polynomial.eval z (normalizedEscapingQuartetPolynomial a n)) ρ +
        analyticOrderAt xi ρ := by
    simpa only [Pi.mul_apply] using analyticOrderAt_mul hPan hxi
  rw [hord,
    Bottcher.analyticOrderAt_polynomial_eval_eq_rootMultiplicity hP]
  exact WithTop.add_ne_top.mpr
    ⟨WithTop.coe_ne_top, xi_orderAt_ne_top ρ⟩

/-- The source-marked common divisor mode of every escaping countermodel has an exact simple pole
at its inserted off-critical zero. -/
theorem escapingQuartetGaugedXi_logDeriv_addedZero_simplePole
    (a : ℝ) (n : ℕ) :
    meromorphicOrderAt (logDeriv (escapingQuartetGaugedXi a n))
        (quartetPoint a (escapingQuartetHeight n)) =
      ((-1 : ℤ) : WithTop ℤ) :=
  meromorphicOrderAt_logDeriv_eq_neg_one_of_analyticAt
    (escapingQuartetGaugedXi_analyticAt a n _)
    (escapingQuartetGaugedXi_analyticOrderAt_ne_top a n _)
    (escapingQuartetGaugedXi_added_zero a n)

/-- A nonzero constant-coefficient differential operator cannot annihilate the principal-part
class of a meromorphic simple pole: its pole order is exactly degree plus one. -/
theorem nonzeroDifferentialOperator_detects_simplePole
    {L : Polynomial ℂ} (hL : L ≠ 0) {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt (constantCoeffDifferentialOperator L f) ρ =
      ((-((L.natDegree + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
  meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole
    hL hf horder

/-- Operator application commutes with finite summation of its polynomial symbols. -/
theorem constantCoeffDifferentialOperator_finset_sum
    {I : Type*} (S : Finset I) (L : I → Polynomial ℂ) (f : ℂ → ℂ) :
    constantCoeffDifferentialOperator (∑ i ∈ S, L i) f =
      ∑ i ∈ S, constantCoeffDifferentialOperator (L i) f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      ext z
      simp [constantCoeffDifferentialOperator]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        HTGeometry.constantCoeffDifferentialOperator_add_operator, ih]

/-- Finite family of differential operators all applied to one common meromorphic mode. -/
def commonModeDifferentialCombination
    {I : Type*} [Fintype I]
    (L : I → Polynomial ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  ∑ i, constantCoeffDifferentialOperator (L i) f

/-- Every common-mode family factors through coefficient summation. -/
theorem commonModeDifferentialCombination_eq_operator_sum
    {I : Type*} [Fintype I]
    (L : I → Polynomial ℂ) (f : ℂ → ℂ) :
    commonModeDifferentialCombination L f =
      constantCoeffDifferentialOperator (∑ i, L i) f := by
  rw [commonModeDifferentialCombination,
    constantCoeffDifferentialOperator_finset_sum]

/-- **Exact `A_(|I|-1)` kernel law.** At a simple pole, a finite family of
constant-coefficient differential operators on the common mode vanishes exactly when its
polynomial symbols sum to zero. -/
theorem commonModeDifferentialCombination_eq_zero_iff_sum_eq_zero
    {I : Type*} [Fintype I]
    (L : I → Polynomial ℂ) {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ)) :
    commonModeDifferentialCombination L f = 0 ↔ ∑ i, L i = 0 := by
  rw [commonModeDifferentialCombination_eq_operator_sum]
  constructor
  · intro hzero
    by_contra hsum
    have hpole :=
      meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole
        hsum hf horder
    rw [hzero] at hpole
    simp at hpole
    exact (WithTop.add_ne_top.mpr
      ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩) hpole.symm
  · intro hsum
    rw [hsum]
    funext z
    simp [constantCoeffDifferentialOperator]

/-- **Cyclic image law.** For every nonempty finite packet, all combinations of its common mode
have exactly the same image as one arbitrary constant-coefficient differential operator. -/
theorem range_commonModeDifferentialCombination_eq
    {I : Type*} [Fintype I] [Nonempty I] (f : ℂ → ℂ) :
    Set.range (fun L : I → Polynomial ℂ =>
      commonModeDifferentialCombination L f) =
      Set.range (fun P : Polynomial ℂ =>
        constantCoeffDifferentialOperator P f) := by
  classical
  ext g
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨∑ i, L i, (commonModeDifferentialCombination_eq_operator_sum L f).symm⟩
  · rintro ⟨P, rfl⟩
    let i₀ : I := Classical.choice ‹Nonempty I›
    let L : I → Polynomial ℂ := fun i => if i = i₀ then P else 0
    refine ⟨L, ?_⟩
    change commonModeDifferentialCombination L f =
      constantCoeffDifferentialOperator P f
    rw [commonModeDifferentialCombination_eq_operator_sum]
    congr 1
    simp [L]

/-- The inserted divisor mode has the exact augmentation kernel for every finite differential
packet. -/
theorem escapingQuartetGaugedXi_commonMode_kernel
    {I : Type*} [Fintype I]
    (a : ℝ) (n : ℕ) (L : I → Polynomial ℂ) :
    commonModeDifferentialCombination L
        (logDeriv (escapingQuartetGaugedXi a n)) = 0 ↔
      ∑ i, L i = 0 := by
  apply commonModeDifferentialCombination_eq_zero_iff_sum_eq_zero
    (ρ := quartetPoint a (escapingQuartetHeight n))
  · rw [show logDeriv (escapingQuartetGaugedXi a n) =
        deriv (escapingQuartetGaugedXi a n) /
          escapingQuartetGaugedXi a n by
      funext z
      rw [logDeriv_apply]
      rfl]
    exact (escapingQuartetGaugedXi_analyticAt a n _).deriv.meromorphicAt.div
      (escapingQuartetGaugedXi_analyticAt a n _).meromorphicAt
  · exact escapingQuartetGaugedXi_logDeriv_addedZero_simplePole a n

/-- Arbitrarily large marked source charge retains the same exact augmentation kernel: all
differential packets factor through coefficient summation and no nonzero symbol annihilates the
common source mode. -/
theorem multiplicityEscapingQuartetGauge_commonMode_kernel
    {I : Type*} [Fintype I]
    (a : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ)
    (L : I → Polynomial ℂ) :
    commonModeDifferentialCombination L
        (logDeriv (multiplicityEscapingQuartetGauge a N n)) = 0 ↔
      ∑ i, L i = 0 := by
  apply commonModeDifferentialCombination_eq_zero_iff_sum_eq_zero
    (ρ := quartetPoint a (escapingQuartetHeight n))
  · rw [show logDeriv (multiplicityEscapingQuartetGauge a N n) =
        deriv (multiplicityEscapingQuartetGauge a N n) /
          multiplicityEscapingQuartetGauge a N n by
      funext z
      rw [logDeriv_apply]
      rfl]
    have hAn : AnalyticAt ℂ (multiplicityEscapingQuartetGauge a N n)
        (quartetPoint a (escapingQuartetHeight n)) := by
      have hfun : multiplicityEscapingQuartetGauge a N n =
          fun z => Polynomial.eval z
            (multiplicityEscapingQuartetPolynomial a N n) := by
        funext z
        exact (multiplicityEscapingQuartetPolynomial_eval a N n z).symm
      rw [hfun]
      simpa using
        (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z)
          (quartetPoint a (escapingQuartetHeight n))).aeval_polynomial
            (multiplicityEscapingQuartetPolynomial a N n)
    exact hAn.deriv.meromorphicAt.div hAn.meromorphicAt
  · exact multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole
      a hN n

/-! ## Packaged escape law -/

/-- **Compact-open Kolchin/Ward charge-escape law.** Every admissible horizontal displacement has
a sequence of hypertranscendental completed-Xi countermodels with exact completed symmetries and
one off-critical zero at every stage. Every holomorphic jet converges compact-open to Xi, while a
nonnegative Ward packet of fixed mass `8π` vanishes uniformly on each bounded height window.
Rational differential gauges preserve the full represented matroid, including after every scalar
Euler valuation layer is adjoined. -/
theorem compactOpenKolchinWardChargeEscape_law
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    (∀ n, Hypertranscendental (escapingQuartetGaugedXi a n)) ∧
    (∀ n s, AnalyticAt ℂ (escapingQuartetGaugedXi a n) s) ∧
    (∀ n s, escapingQuartetGaugedXi a n (1 - s) =
      escapingQuartetGaugedXi a n s) ∧
    (∀ n s, escapingQuartetGaugedXi a n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (escapingQuartetGaugedXi a n s)) ∧
    (∀ n, (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 ∧
      escapingQuartetGaugedXi a n
        (quartetPoint a (escapingQuartetHeight n)) = 0) ∧
    (∀ j, TendstoLocallyUniformly
      (fun n => iteratedDeriv j (escapingQuartetGaugedXi a n))
      (iteratedDeriv j xi) atTop) ∧
    (∀ R, 0 ≤ R → TendstoUniformlyOn
      (fun n t => quartetWardInfinitesimalDensity a
        (escapingQuartetHeight n) t)
      (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
    (∀ n, ∫⁻ t : ℝ, ENNReal.ofReal
      (quartetWardInfinitesimalDensity a (escapingQuartetHeight n) t) =
        ENNReal.ofReal (8 * π)) := by
  refine ⟨escapingQuartetGaugedXi_hypertranscendental a,
    escapingQuartetGaugedXi_analyticAt a,
    escapingQuartetGaugedXi_one_sub a,
    escapingQuartetGaugedXi_conj a, ?_,
    escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly a,
    fun R hR => escapingQuartetWard_window_tendstoUniformly ha0 ha1 hR,
    escapingQuartetWard_mass ha0⟩
  intro n
  exact ⟨escapingQuartetGaugedXi_added_zero_off_critical
    (ne_of_gt ha0) n, escapingQuartetGaugedXi_added_zero a n⟩

/-- **Unbounded compact-open Kolchin/Ward nonproperness law.** For every positive integer `N`
there is a sequence in the same completed-symmetry class, converging to Xi through every
holomorphic jet, with an off-critical quartet of multiplicity `N`. Its nonnegative aggregate Ward
density vanishes on every bounded window although its exact mass is `N` quanta of `8π`. The marked
rational source mode retains an exact simple pole. Together with the multiplicity matroid theorems
above, `N` is arbitrary while the complete Kolchin stratum stays fixed. -/
theorem unboundedCompactOpenKolchinWardChargeEscape_law
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    ∀ N : ℕ, 0 < N →
      (∀ n, Hypertranscendental
        (multiplicityEscapingQuartetGaugedXi a N n)) ∧
      (∀ n s, AnalyticAt ℂ
        (multiplicityEscapingQuartetGaugedXi a N n) s) ∧
      (∀ n s, multiplicityEscapingQuartetGaugedXi a N n (1 - s) =
        multiplicityEscapingQuartetGaugedXi a N n s) ∧
      (∀ n s,
        multiplicityEscapingQuartetGaugedXi a N n ((starRingEnd ℂ) s) =
          (starRingEnd ℂ) (multiplicityEscapingQuartetGaugedXi a N n s)) ∧
      (∀ n, (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 ∧
        multiplicityEscapingQuartetGaugedXi a N n
          (quartetPoint a (escapingQuartetHeight n)) = 0) ∧
      (∀ j, TendstoLocallyUniformly
        (fun n => iteratedDeriv j
          (multiplicityEscapingQuartetGaugedXi a N n))
        (iteratedDeriv j xi) atTop) ∧
      (∀ R, 0 ≤ R → TendstoUniformlyOn
        (fun n => multiplicityEscapingQuartetWardDensity a N n)
        (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
      (∀ n, multiplicityEscapingQuartetWardMass a N n =
        N • ENNReal.ofReal (8 * π)) ∧
      (∀ n, meromorphicOrderAt
          (logDeriv (multiplicityEscapingQuartetGauge a N n))
          (quartetPoint a (escapingQuartetHeight n)) =
        ((-1 : ℤ) : WithTop ℤ)) := by
  intro N hN
  refine ⟨
    multiplicityEscapingQuartetGaugedXi_hypertranscendental a N,
    multiplicityEscapingQuartetGaugedXi_analyticAt a N,
    multiplicityEscapingQuartetGaugedXi_one_sub a N,
    multiplicityEscapingQuartetGaugedXi_conj a N, ?_,
    multiplicityEscapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly a N,
    fun R hR =>
      multiplicityEscapingQuartetWard_window_tendstoUniformly N ha0 ha1 hR,
    multiplicityEscapingQuartetWardMass_eq ha0 N,
    multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole a hN⟩
  intro n
  exact ⟨escapingQuartetGaugedXi_added_zero_off_critical
      (ne_of_gt ha0) n,
    multiplicityEscapingQuartetGaugedXi_added_zero a hN n⟩

end RHTower
