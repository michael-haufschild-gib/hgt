import GaloisForLFunctions.RHTower.XiGaussianExplicitFormula
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder
import GaloisForLFunctions.RHTower.PolynomialGaussianCompletedPrimeGammaWedge

/-!
# Polynomial-square Gaussian completed-source formula

Finite coefficient polarization lifts the exact monomial Gaussian formula to the native Route-U
density `Q(x²)² exp (-t x²)`.  The crossed polar residue becomes the literal square
`Q(-1/4)² exp (t/4)`, while the complete prime term is the native unnormalized Fourier source.
The existing completed prime--Gamma wedge then gives strict positivity of the exact Xi trace.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Complete critical half-density prime source of the native Route-U polynomial Gaussian. -/
def routeUPolynomialGaussianPrimeSource
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 : ℂ) n *
      routeUPolynomialGaussianFourier Q t (Real.log n)

/-- Canonical finite coefficient expansion used by the polynomial-square lift. -/
theorem routeUPolynomial_eq_coeff_rangeSum (Q : Polynomial ℝ) :
    Q = ∑ j ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (Q.coeff j) * Polynomial.X ^ j := by
  conv_lhs =>
    rw [Polynomial.as_sum_range' Q (Q.natDegree + 1) (Nat.lt_succ_self _)]
  exact Finset.sum_congr rfl fun j _ => Polynomial.C_mul_X_pow_eq_monomial.symm

/-- Pointwise coefficient expansion of the native polynomial Gaussian density. -/
theorem routeUPolynomialGaussianDensity_eq_coeff_sum
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUPolynomialGaussianDensity Q t x =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          (((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            xiGaussianTestC t.1 (j + k) (x : ℂ)) := by
  have heval : Q.eval (x ^ 2) =
      ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * (x ^ 2) ^ j := by
    conv_lhs => rw [routeUPolynomial_eq_coeff_rangeSum Q]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [routeUPolynomialGaussianDensity, evenSquarePolynomial, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, heval]
  simp_rw [xiGaussianTestC_ofReal, xiGaussianHermiteProfile]
  push_cast
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr
  · rfl
  · intro j _
    apply Finset.sum_congr
    · rfl
    · intro k _
      have hpow : ((x : ℂ) ^ 2) ^ j * ((x : ℂ) ^ 2) ^ k =
          (x : ℂ) ^ (2 * (j + k)) := by
        rw [← pow_add, pow_mul]
      calc
        (Q.coeff j : ℂ) * ((x : ℂ) ^ 2) ^ j *
              ((Q.coeff k : ℂ) * ((x : ℂ) ^ 2) ^ k) *
              Complex.exp (-((t.1 : ℂ) * (x : ℂ) ^ 2)) =
            (Q.coeff j : ℂ) * (Q.coeff k : ℂ) *
              ((((x : ℂ) ^ 2) ^ j * ((x : ℂ) ^ 2) ^ k) *
                Complex.exp (-((t.1 : ℂ) * (x : ℂ) ^ 2))) := by ring
        _ = _ := by rw [hpow]

/-- The norm in the existing Gamma wedge is the literal nonnegative polynomial-square density. -/
theorem norm_routeUPolynomialGaussianDensity_eq_coeff_sum
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    ‖routeUPolynomialGaussianDensity Q t x‖ =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * Q.coeff k * xiGaussianHermiteProfile t.1 (j + k) x := by
  have heval : Q.eval (x ^ 2) =
      ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * (x ^ 2) ^ j := by
    conv_lhs => rw [routeUPolynomial_eq_coeff_rangeSum Q]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [routeUPolynomialGaussianDensity, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)),
    evenSquarePolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
    heval]
  simp only [xiGaussianHermiteProfile]
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr
  · rfl
  · intro j _
    apply Finset.sum_congr
    · rfl
    · intro k _
      have hpow : (x ^ 2) ^ j * (x ^ 2) ^ k = x ^ (2 * (j + k)) := by
        rw [← pow_add, pow_mul]
      calc
        Q.coeff j * (x ^ 2) ^ j * (Q.coeff k * (x ^ 2) ^ k) *
              Real.exp (-(t.1 * x ^ 2)) =
            Q.coeff j * Q.coeff k *
              (((x ^ 2) ^ j * (x ^ 2) ^ k) * Real.exp (-(t.1 * x ^ 2))) := by
          ring
        _ = _ := by rw [hpow]

private theorem integrable_xiGaussianHermiteProfile_mul_gammaHardyPhaseRate
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun x : ℝ =>
      xiGaussianHermiteProfile t k x * gammaHardyPhaseRate x) := by
  have hcomplex : Integrable (xiGaussianCenteredArchIntegrand t k) :=
    integrable_xiGaussianArchHorizontalIntegrand ht
      (by norm_num : (1 / 2 : ℝ) < 1) k
      (y := 0) ⟨by norm_num, le_rfl⟩ (by norm_num)
  exact hcomplex.re.congr (Filter.Eventually.of_forall fun x =>
    re_xiGaussianCenteredArchIntegrand t k x)

/-- Finite coefficient polarization identifies the monomial Gamma sum with the native density. -/
theorem routeUPolynomialGaussian_gammaIntegral_eq_coeff_sum
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * Q.coeff k *
            (∫ x : ℝ,
              xiGaussianHermiteProfile t.1 (j + k) x * gammaHardyPhaseRate x) := by
  have hterm (j k : ℕ) : Integrable (fun x : ℝ =>
      (Q.coeff j * Q.coeff k) *
        (xiGaussianHermiteProfile t.1 (j + k) x * gammaHardyPhaseRate x)) :=
    (integrable_xiGaussianHermiteProfile_mul_gammaHardyPhaseRate t.property (j + k)).const_mul _
  calc
    (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) =
        ∫ x : ℝ, ∑ j ∈ Finset.range (Q.natDegree + 1),
          ∑ k ∈ Finset.range (Q.natDegree + 1),
            (Q.coeff j * Q.coeff k) *
              (xiGaussianHermiteProfile t.1 (j + k) x * gammaHardyPhaseRate x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_routeUPolynomialGaussianDensity_eq_coeff_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ j ∈ Finset.range (Q.natDegree + 1),
          ∫ x : ℝ, ∑ k ∈ Finset.range (Q.natDegree + 1),
            (Q.coeff j * Q.coeff k) *
              (xiGaussianHermiteProfile t.1 (j + k) x * gammaHardyPhaseRate x) := by
      rw [MeasureTheory.integral_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => hterm j k]
    _ = ∑ j ∈ Finset.range (Q.natDegree + 1),
          ∑ k ∈ Finset.range (Q.natDegree + 1),
            ∫ x : ℝ, (Q.coeff j * Q.coeff k) *
              (xiGaussianHermiteProfile t.1 (j + k) x * gammaHardyPhaseRate x) := by
      exact Finset.sum_congr rfl fun j _ =>
        MeasureTheory.integral_finsetSum _ fun k _ => hterm j k
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MeasureTheory.integral_const_mul]

/-- Native polynomial Fourier source is the finite polarization of Gaussian--Hermite transforms. -/
theorem routeUPolynomialGaussianFourier_eq_coeff_sum
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (w : ℝ) :
    routeUPolynomialGaussianFourier Q t w =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          (((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            xiGaussianHermiteFourier t.1 (j + k) w) := by
  have hfourier (m : ℕ) : Integrable (fun x : ℝ =>
      xiGaussianTestC t.1 m (x : ℂ) *
        Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) := by
    simpa using integrable_xiGaussianTestC_fourier_horizontal t.property m w 0
  have hterm (j k : ℕ) : Integrable (fun x : ℝ =>
      ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
        (xiGaussianTestC t.1 (j + k) (x : ℂ) *
          Complex.exp (-(I * (w : ℂ) * (x : ℂ))))) :=
    (hfourier (j + k)).const_mul _
  rw [routeUPolynomialGaussianFourier]
  calc
    (∫ x : ℝ, Complex.exp (((-(w * x) : ℝ) : ℂ) * I) *
        routeUPolynomialGaussianDensity Q t x) =
      ∫ x : ℝ, ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            (xiGaussianTestC t.1 (j + k) (x : ℂ) *
              Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [routeUPolynomialGaussianDensity_eq_coeff_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hphase :
          Complex.exp (((-(w * x) : ℝ) : ℂ) * I) =
            Complex.exp (-(I * (w : ℂ) * (x : ℂ))) := by
        congr 1
        push_cast
        ring
      rw [hphase]
      ring
    _ = ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∫ x : ℝ, ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            (xiGaussianTestC t.1 (j + k) (x : ℂ) *
              Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) := by
      rw [MeasureTheory.integral_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => hterm j k]
    _ = ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ∫ x : ℝ, ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            (xiGaussianTestC t.1 (j + k) (x : ℂ) *
              Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) := by
      exact Finset.sum_congr rfl fun j _ =>
        MeasureTheory.integral_finsetSum _ fun k _ => hterm j k
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MeasureTheory.integral_const_mul]
      rfl

/-- The native polynomial prime source is absolutely summable at every positive heat time. -/
theorem summable_routeUPolynomialGaussianPrimeSourceTerm
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    Summable (fun n : ℕ =>
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 : ℂ) n *
        routeUPolynomialGaussianFourier Q t (Real.log n)) := by
  have hpoint : (fun n : ℕ =>
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 : ℂ) n *
        routeUPolynomialGaussianFourier Q t (Real.log n)) =
      fun n => ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            xiGaussianCenteredPrimeAtom t.1 (j + k) n := by
    funext n
    rw [routeUPolynomialGaussianFourier_eq_coeff_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [xiGaussianCenteredPrimeAtom]
    ring
  rw [hpoint]
  exact summable_sum fun j _ => summable_sum fun k _ =>
    (summable_xiGaussianCenteredPrimeAtom t.property (j + k)).mul_left _

/-- Prime-source finite polarization, with the only infinite interchange justified absolutely. -/
theorem routeUPolynomialGaussianPrimeSource_eq_coeff_sum
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    routeUPolynomialGaussianPrimeSource Q t =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            ∑' n : ℕ, xiGaussianCenteredPrimeAtom t.1 (j + k) n := by
  rw [routeUPolynomialGaussianPrimeSource]
  have hpoint : (fun n : ℕ =>
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 : ℂ) n *
        routeUPolynomialGaussianFourier Q t (Real.log n)) =
      fun n => ∑ j ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          ((Q.coeff j * Q.coeff k : ℝ) : ℂ) *
            xiGaussianCenteredPrimeAtom t.1 (j + k) n := by
    funext n
    rw [routeUPolynomialGaussianFourier_eq_coeff_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [xiGaussianCenteredPrimeAtom]
    ring
  rw [hpoint,
    Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
      (summable_xiGaussianCenteredPrimeAtom t.property (j + k)).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum (fun k _ =>
    (summable_xiGaussianCenteredPrimeAtom t.property (j + k)).mul_left _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]

/-- The crossed polar residue of a polynomial square is a literal nonnegative square. -/
theorem routeUPolynomialGaussian_polar_eq_coeff_sum
    (Q : Polynomial ℝ) (t : ℝ) :
    ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        Q.coeff j * Q.coeff k *
          ((-(1 / 4 : ℝ)) ^ (j + k) * Real.exp (t / 4)) =
      (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t / 4) := by
  have heval : Q.eval (-(1 / 4 : ℝ)) =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        Q.coeff j * (-(1 / 4 : ℝ)) ^ j := by
    conv_lhs => rw [routeUPolynomial_eq_coeff_rangeSum Q]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr
  · rfl
  · intro j _
    apply Finset.sum_congr
    · rfl
    · intro k _
      rw [pow_add]
      ring

/-- Real monomial explicit formula in the normalization used by the polynomial lift. -/
theorem pi_mul_xiGaussianHeatMomentReal_eq_primeGamma
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Real.pi * xiGaussianHeatMomentReal m t =
      (∫ x : ℝ, xiGaussianHermiteProfile t m x * gammaHardyPhaseRate x) +
        2 * Real.pi * ((-(1 / 4 : ℝ)) ^ m * Real.exp (t / 4)) -
          (∑' n : ℕ, xiGaussianCenteredPrimeAtom t m n).re := by
  rw [xiGaussianHeatMomentReal,
    xiGaussianHeatMoment_eq_completedBottomSource_div_pi ht,
    Complex.mul_re, re_integral_xiGaussianCompletedBottomSource_eq
      ht (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

/-- **Exact polynomial-square Gaussian completed-source formula.** -/
theorem pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 =
      (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) +
        2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.1 / 4) -
          (routeUPolynomialGaussianPrimeSource Q t).re := by
  let N := Q.natDegree + 1
  let a : ℕ → ℝ := Q.coeff
  have hQ := routeUPolynomial_eq_coeff_rangeSum Q
  have hprime := congrArg Complex.re
    (routeUPolynomialGaussianPrimeSource_eq_coeff_sum Q t)
  simp only [Complex.re_sum, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hprime
  have htraceRange : xiPolynomialGaussianHeatTraceReal Q t.1 =
      xiHeatHankelForm (Q.natDegree + 1) Q.coeff t.1 := by
    calc
      xiPolynomialGaussianHeatTraceReal Q t.1 =
          xiPolynomialGaussianHeatTraceReal
            (∑ j ∈ Finset.range (Q.natDegree + 1),
              Polynomial.C (Q.coeff j) * Polynomial.X ^ j) t.1 :=
        congrArg (fun P => xiPolynomialGaussianHeatTraceReal P t.1) hQ
      _ = xiHeatHankelForm (Q.natDegree + 1) Q.coeff t.1 :=
        xiPolynomialGaussianHeatTraceReal_rangeSum t.property _ _
  rw [htraceRange, xiHeatHankelForm]
  change Real.pi *
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        a j * a k * xiGaussianHeatMomentReal (j + k) t.1) = _
  calc
    Real.pi *
        (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          a j * a k * xiGaussianHeatMomentReal (j + k) t.1) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        a j * a k * (Real.pi * xiGaussianHeatMomentReal (j + k) t.1) := by
      simp only [Finset.mul_sum]
      ring
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        a j * a k *
          ((∫ x : ℝ, xiGaussianHermiteProfile t.1 (j + k) x *
              gammaHardyPhaseRate x) +
            2 * Real.pi * ((-(1 / 4 : ℝ)) ^ (j + k) * Real.exp (t.1 / 4)) -
              (∑' n : ℕ, xiGaussianCenteredPrimeAtom t.1 (j + k) n).re) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pi_mul_xiGaussianHeatMomentReal_eq_primeGamma t.property]
    _ = (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          a j * a k *
            (∫ x : ℝ, xiGaussianHermiteProfile t.1 (j + k) x *
              gammaHardyPhaseRate x)) +
        2 * Real.pi *
          (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            a j * a k * ((-(1 / 4 : ℝ)) ^ (j + k) * Real.exp (t.1 / 4))) -
        (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          a j * a k *
            (∑' n : ℕ, xiGaussianCenteredPrimeAtom t.1 (j + k) n).re) := by
      simp_rw [mul_sub, mul_add]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
      have hpolarReorder :
          (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            a j * a k *
              (2 * Real.pi *
                ((-(1 / 4 : ℝ)) ^ (j + k) * Real.exp (t.1 / 4)))) =
          ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            2 * Real.pi *
              (a j * a k *
                ((-(1 / 4 : ℝ)) ^ (j + k) * Real.exp (t.1 / 4))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hpolarReorder]
    _ = _ := by
      rw [show N = Q.natDegree + 1 by rfl,
        show a = Q.coeff by rfl,
        ← routeUPolynomialGaussian_gammaIntegral_eq_coeff_sum Q t,
        routeUPolynomialGaussian_polar_eq_coeff_sum Q t.1,
        ← hprime]
      ring

private theorem norm_LSeries_vonMangoldt_half_term
    (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (1 / 2 : ℂ) n‖ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  rcases n with _ | n
  · simp [LSeries.term_zero]
  · have hn : 0 < n + 1 := Nat.succ_pos n
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn, Real.sqrt_eq_rpow]
    norm_num

/-- Real part of the exact prime source is bounded by the existing complete absolute tail. -/
theorem re_routeUPolynomialGaussianPrimeSource_le_absoluteTail
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) :
    (routeUPolynomialGaussianPrimeSource Q t.heat).re ≤
      routeUPolynomialGaussianPrimeAbsoluteTail Q t := by
  have hsource := summable_routeUPolynomialGaussianPrimeSourceTerm Q t.heat
  have hsourceRe := hsource.mapL Complex.reCLM
  rw [routeUPolynomialGaussianPrimeSource, Complex.re_tsum hsource]
  exact hsourceRe.tsum_le_tsum
    (fun n => by
      calc
        (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n *
            routeUPolynomialGaussianFourier Q t.heat (Real.log n)).re ≤
            ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n *
                routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖ :=
          Complex.re_le_norm _
        _ = ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖ := by
          rw [norm_mul, norm_LSeries_vonMangoldt_half_term])
    (summable_routeUPolynomialGaussianPrimeAbsoluteTail Q t)

/-- **Strict exact Xi-trace positivity throughout the completed Route-U aperture.** -/
theorem xiPolynomialGaussianHeatTraceReal_pos_of_completedWedge
    (Q : {Q : Polynomial ℝ // Q ≠ 0})
    (t : routeUCompletedPrimeGammaWedge Q.1) :
    0 < xiPolynomialGaussianHeatTraceReal Q.1 t.1 := by
  have hformula := pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma Q.1 t.heat
  have hgap := routeUPolynomialGaussianCompletedPrimeGammaGap_pos Q t
  have hprime := re_routeUPolynomialGaussianPrimeSource_le_absoluteTail Q.1 t.prime
  have hprime' :
      (routeUPolynomialGaussianPrimeSource Q.1 t.heat).re ≤
        routeUPolynomialGaussianPrimeAbsoluteTail Q.1 t.prime := by
    have hheat : t.prime.heat = t.heat := by
      apply Subtype.ext
      rfl
    rw [hheat] at hprime
    exact hprime
  have hpolar : 0 ≤
      2 * Real.pi * (Q.1.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.heat.1 / 4) := by
    positivity
  have hpiTrace : 0 < Real.pi * xiPolynomialGaussianHeatTraceReal Q.1 t.heat.1 := by
    calc
      0 < (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q.1 t.heat x‖ *
              gammaHardyPhaseRate x) -
            routeUPolynomialGaussianPrimeAbsoluteTail Q.1 t.prime := hgap
      _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q.1 t.heat x‖ *
              gammaHardyPhaseRate x) -
            (routeUPolynomialGaussianPrimeSource Q.1 t.heat).re :=
        sub_le_sub_left hprime' _
      _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q.1 t.heat x‖ *
              gammaHardyPhaseRate x) +
            2 * Real.pi * (Q.1.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.heat.1 / 4) -
              (routeUPolynomialGaussianPrimeSource Q.1 t.heat).re := by
        linarith
      _ = Real.pi * xiPolynomialGaussianHeatTraceReal Q.1 t.heat.1 := hformula.symm
  have htrace : 0 < xiPolynomialGaussianHeatTraceReal Q.1 t.heat.1 :=
    pos_of_mul_pos_right hpiTrace Real.pi_pos.le
  simpa only [routeUCompletedPrimeGammaWedge.heat] using htrace

/-- Every strictly negative polynomial-square trace lies beyond the completed Route-U aperture. -/
theorem xiPolynomialGaussianHeatTraceReal_negative_outside_completedAperture :
    ∀ (Q : {Q : Polynomial ℝ // Q ≠ 0}) (t : {τ : ℝ // 0 < τ}),
      xiPolynomialGaussianHeatTraceReal Q.1 t.1 < 0 →
        routeUCompletedPrimeGammaAperture < t.1 * (Q.1.natDegree + 1) := by
  intro Q t hneg
  by_contra hnot
  have haperture : t.1 * (Q.1.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture :=
    le_of_not_gt hnot
  let tw : routeUCompletedPrimeGammaWedge Q.1 :=
    ⟨t.1, t.property, haperture⟩
  have hpos := xiPolynomialGaussianHeatTraceReal_pos_of_completedWedge Q tw
  exact (not_lt_of_ge hpos.le) hneg

/-- **Exact Route-U obstruction under failure of RH.**  A false RH forces a nonzero negative
polynomial Gaussian witness, and every such witness crosses the completed source aperture. -/
theorem not_riemannHypothesis_forces_negative_trace_beyond_completedAperture :
    ¬ RiemannHypothesis →
      ∃ (Q : {Q : Polynomial ℝ // Q ≠ 0}) (t : {τ : ℝ // 0 < τ}),
        xiPolynomialGaussianHeatTraceReal Q.1 t.1 < 0 ∧
          routeUCompletedPrimeGammaAperture < t.1 * (Q.1.natDegree + 1) := by
  intro hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  obtain ⟨P, t, ht, hneg⟩ :=
    exists_neg_xiPolynomialGaussianHeatTraceReal_of_spectralSq_im_pos hq
  have hP : P ≠ 0 := by
    intro hzero
    subst P
    simp [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
      xiPolynomialGaussianHeatTerm] at hneg
  let Q : {Q : Polynomial ℝ // Q ≠ 0} := ⟨P, hP⟩
  let τ : {τ : ℝ // 0 < τ} := ⟨t, ht⟩
  exact ⟨Q, τ, hneg,
    xiPolynomialGaussianHeatTraceReal_negative_outside_completedAperture Q τ hneg⟩

end

end RHTower
