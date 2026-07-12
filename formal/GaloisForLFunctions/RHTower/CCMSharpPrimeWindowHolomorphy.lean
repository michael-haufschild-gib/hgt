import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowQuadrature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Holomorphy of the sharp-window quadrature remainder

The dyadic discrete-to-continuous error is entire term by term.  Its von-Mangoldt weighted
series converges locally normally on `Re s > 1/2`, exactly the half-plane supplied by the
quadrature estimate.  This turns the absolutely convergent remainder from the sharp-window
construction into an honest holomorphic function, without a piecewise-linear test-function
interface.
-/

open Complex Filter Function Finset intervalIntegral MeasureTheory Set

noncomputable section

namespace RHTower

private theorem hasDerivAt_ofReal_const_cpow_neg
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (x : ℂ) ^ (-z))
      (-(Real.log x : ℂ) * (x : ℂ) ^ (-s)) s := by
  have h := ((hasDerivAt_id s).neg).const_cpow
    (c := (x : ℂ)) (Or.inl (by exact_mod_cast hx.ne'))
  rw [← Complex.ofReal_log hx.le] at h
  convert h using 1 <;> simp [Function.id_def] <;> ring

private theorem dyadicSharpPrimeWindowIntegralMain_differentiableAt
    {k : ℕ} (hk : 1 ≤ k) (s₀ : ℂ) :
    DifferentiableAt ℂ (dyadicSharpPrimeWindowIntegralMain k) s₀ := by
  let a : ℝ := k
  let b : ℝ := 2 * k
  let F : ℂ → ℝ → ℂ := fun s x => (x : ℂ) ^ (-s)
  let F' : ℂ → ℝ → ℂ := fun s x =>
    -(Real.log x : ℂ) * (x : ℂ) ^ (-s)
  let K : Set (ℂ × ℝ) := Metric.closedBall s₀ 1 ×ˢ Set.uIcc a b
  have hka : 0 < a := by
    dsimp only [a]
    exact_mod_cast (show 0 < k by omega)
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact_mod_cast (show k ≤ 2 * k by omega)
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hka.trans_le hx.1
  have hFcont : ∀ s : ℂ, ContinuousOn (F s) (Set.uIcc a b) := by
    intro s
    dsimp only [F]
    apply ContinuousOn.cpow_const (by fun_prop)
    intro x hx
    left
    simpa using hpos x hx
  have hF'cont : ∀ s : ℂ, ContinuousOn (F' s) (Set.uIcc a b) := by
    intro s
    dsimp only [F']
    have hlogReal : ContinuousOn Real.log (Set.uIcc a b) :=
      Real.continuousOn_log.mono fun x hx => (hpos x hx).ne'
    have hlogComplex : ContinuousOn
        (fun x : ℝ => (Real.log x : ℂ)) (Set.uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn hlogReal
    apply ContinuousOn.mul
    · exact hlogComplex.neg
    · exact hFcont s
  have hKcompact : IsCompact K :=
    IsCompact.prod (isCompact_closedBall s₀ 1) isCompact_uIcc
  have hbaseCont : ContinuousOn
      (fun p : ℂ × ℝ => (p.2 : ℂ)) K :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hexpCont : ContinuousOn (fun p : ℂ × ℝ => -p.1) K :=
    continuous_fst.neg.continuousOn
  have hcpowCont : ContinuousOn
      (fun p : ℂ × ℝ => (p.2 : ℂ) ^ (-p.1)) K := by
    apply hbaseCont.cpow hexpCont
    intro p hp
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hpos p.2 hp.2
  have hlogCont : ContinuousOn
      (fun p : ℂ × ℝ => (Real.log p.2 : ℂ)) K := by
    have hlogReal : ContinuousOn Real.log (Set.uIcc a b) :=
      Real.continuousOn_log.mono fun x hx => (hpos x hx).ne'
    have hlogProd : ContinuousOn (fun p : ℂ × ℝ => Real.log p.2) K :=
      hlogReal.comp continuousOn_snd fun p hp => hp.2
    exact Complex.continuous_ofReal.comp_continuousOn hlogProd
  have hderivCont : ContinuousOn
      (fun p : ℂ × ℝ => ‖-(Real.log p.2 : ℂ) *
        (p.2 : ℂ) ^ (-p.1)‖) K :=
    (hlogCont.neg.mul hcpowCont).norm
  obtain ⟨R, hR⟩ := hKcompact.exists_bound_of_continuousOn hderivCont
  have hresult := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (F := F) (F' := F')
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := fun _ => R)
    (Metric.ball_mem_nhds s₀ (by norm_num))
    (Filter.Eventually.of_forall fun s =>
      ((hFcont s).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    ((hFcont s₀).intervalIntegrable)
    (((hF'cont s₀).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (by
      filter_upwards with x
      intro hx s hs
      dsimp only [F']
      simpa only [Prod.fst, Prod.snd, Real.norm_of_nonneg (norm_nonneg _)] using
        hR (s, x) ⟨Metric.mem_closedBall.mpr (le_of_lt
          (Metric.mem_ball.mp hs)), Set.uIoc_subset_uIcc hx⟩)
    _root_.intervalIntegrable_const
    (by
      filter_upwards with x
      intro hx s _hs
      dsimp only [F, F']
      exact hasDerivAt_ofReal_const_cpow_neg
        (hpos x (Set.uIoc_subset_uIcc hx)) s)
  exact hresult.2.differentiableAt

/-- Every dyadic quadrature error is entire in its Mellin coordinate. -/
theorem differentiable_dyadicSharpPrimeWindowError (k : ℕ) :
    Differentiable ℂ (dyadicSharpPrimeWindowError k) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hzero : dyadicSharpPrimeWindowError 0 = fun _ => 0 := by
      funext s
      simp [dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
        dyadicSharpPrimeWindowIntegralMain]
    rw [hzero]
    fun_prop
  · intro s
    apply DifferentiableAt.sub
    · unfold dyadicSharpPrimeWindowKernel
      apply DifferentiableAt.fun_sum
      intro j hj
      have hbase : (((k + j : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast (show k + j ≠ 0 by omega)
      exact ((hasDerivAt_id s).neg.const_cpow
        (c := ((k + j : ℕ) : ℂ)) (Or.inl hbase)).differentiableAt
    · exact dyadicSharpPrimeWindowIntegralMain_differentiableAt hk s

/-- Every von-Mangoldt-weighted error term is entire. -/
theorem differentiable_dyadicSharpPrimeWindowErrorSummand (k : ℕ) :
    Differentiable ℂ (fun s => dyadicSharpPrimeWindowErrorSummand s k) := by
  unfold dyadicSharpPrimeWindowErrorSummand
  exact (differentiable_const
    (((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ))).mul
      (differentiable_dyadicSharpPrimeWindowError k)

/-- The weighted sharp-window quadrature remainder converges locally normally on the maximal
half-plane supplied by the cell estimate. -/
theorem summableLocallyUniformlyOn_dyadicSharpPrimeWindowErrorSummand :
    SummableLocallyUniformlyOn
      (fun k : ℕ => fun s : ℂ => dyadicSharpPrimeWindowErrorSummand s k)
      {s : ℂ | 1 / 2 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 1 / 2 < s.re at hs
  let r : ℝ := (s.re - 1 / 2) / 2
  let sigma : ℝ := s.re - r
  let R : ℝ := ‖s‖ + r
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hsigma : 1 / 2 < sigma := by
    dsimp only [sigma, r]
    linarith
  let z : ℂ := ((sigma + 1 / 2 : ℝ) : ℂ)
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hz : 1 < z.re := by
    dsimp only [z]
    simp only [ofReal_re]
    linarith
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hmajor : Summable (fun k => R *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
    hvm.norm.mul_left R
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable hmajor
  intro k x hx
  have hxball : ‖x - s‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hx
  have hxre : sigma < x.re := by
    have hre := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re] at hre
    have hreLower := (abs_le.mp hre).1
    dsimp only [sigma]
    linarith
  have hxnorm : ‖x‖ ≤ R := by
    dsimp only [R]
    calc
      ‖x‖ ≤ ‖x - s‖ + ‖s‖ := by
        calc
          ‖x‖ = ‖(x - s) + s‖ := by ring_nf
          _ ≤ ‖x - s‖ + ‖s‖ := norm_add_le _ _
      _ ≤ ‖s‖ + r := by linarith
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [dyadicSharpPrimeWindowErrorSummand,
      dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
      dyadicSharpPrimeWindowIntegralMain]
  · have hk1 : 1 ≤ k := hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have herr := norm_dyadicSharpPrimeWindowError_le hk1
      (by linarith : 0 < x.re)
    rw [dyadicSharpPrimeWindowErrorSummand, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_nonneg k))]
    calc
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          ‖dyadicSharpPrimeWindowError k x‖ ≤
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (‖x‖ * (k : ℝ) ^ (-x.re)) := by
            exact mul_le_mul_of_nonneg_left herr
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (Real.sqrt_nonneg k))
      _ ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (R * (k : ℝ) ^ (-sigma)) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            ‖x‖ * (k : ℝ) ^ (-x.re) ≤
                R * (k : ℝ) ^ (-x.re) :=
              mul_le_mul_of_nonneg_right hxnorm
                (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le k)) _)
            _ ≤ R * (k : ℝ) ^ (-sigma) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le
                  (by exact_mod_cast hk1) (by linarith)) hR0
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.sqrt_nonneg k)
      _ = R * ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
        rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hk]
        simp only [z, ofReal_re]
        rw [Real.sqrt_eq_rpow]
        rw [show ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (1 / 2 : ℝ) *
            (R * (k : ℝ) ^ (-sigma)) =
          R * ArithmeticFunction.vonMangoldt k *
            ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-sigma)) by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le]
              ring]
        rw [← Real.rpow_add hkreal]
        rw [show -(1 / 2 : ℝ) + -sigma = -(sigma + 1 / 2) by ring]
        rw [Real.rpow_neg hkreal.le]
        field_simp

/-- The sharp-window quadrature remainder series is holomorphic on `Re s > 1/2`. -/
theorem differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf :
    DifferentiableOn ℂ dyadicSharpPrimeWindowErrorSeries
      {s : ℂ | 1 / 2 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    summableLocallyUniformlyOn_dyadicSharpPrimeWindowErrorSummand
  intro k s _hs
  exact (differentiable_dyadicSharpPrimeWindowErrorSummand k s)

/-- The dyadic sharp-window Mellin factor itself is entire.  The proof reads it as the
parameter-dependent integral on `[1,2]`, so the removable value at `s = 1` is handled without
case-splitting. -/
theorem differentiable_sharpPrimeWindowMellin_logTwo :
    Differentiable ℂ (sharpPrimeWindowMellin (Real.log 2)) := by
  have heq : dyadicSharpPrimeWindowIntegralMain 1 =
      sharpPrimeWindowMellin (Real.log 2) := by
    funext s
    simpa using dyadicSharpPrimeWindowIntegralMain_eq_scaledMellin
      (k := 1) (by norm_num) s
  rw [← heq]
  intro s
  exact dyadicSharpPrimeWindowIntegralMain_differentiableAt (by norm_num) s

end RHTower
