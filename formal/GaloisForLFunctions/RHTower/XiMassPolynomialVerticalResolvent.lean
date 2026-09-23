import GaloisForLFunctions.RHTower.XiMassVerticalResolvent
import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# Polynomial-weighted vertical edge for the analytic mass test

Multiplying the analytic mass test by a fixed real polynomial in the contour variable leaves the
right vertical edge of a symmetric mass rectangle cofinally negligible.  The exponential mass
envelope absorbs both the polynomial weight and its derivative, so the slowly varying Cauchy
estimate applies verbatim with a numerator enlarged by coefficient-sum majorants.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## Coefficient majorants and the complex derivative of a real polynomial -/

/-- Sum of the coefficient norms of a real polynomial. -/
def evalRealPolynomialCoeffSum (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖

theorem evalRealPolynomialCoeffSum_nonneg (p : Polynomial ℝ) :
    0 ≤ evalRealPolynomialCoeffSum p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- On a disk of radius `r` the coefficient majorant is dominated by a single shifted power. -/
theorem evalRealPolynomialNormBound_le_coeffSum_mul_pow (p : Polynomial ℝ) {r : ℝ}
    (hr : 0 ≤ r) {n : ℕ} (hn : p.natDegree ≤ n) :
    evalRealPolynomialNormBound p r ≤ evalRealPolynomialCoeffSum p * (1 + r) ^ n := by
  rw [evalRealPolynomialNormBound, evalRealPolynomialCoeffSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ n := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hn
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc r ^ k ≤ (1 + r) ^ k := by
        exact pow_le_pow_left₀ hr (by linarith) k
    _ ≤ (1 + r) ^ n := pow_le_pow_right₀ (by linarith) hk'

/-- A real polynomial is complex differentiable with the mapped formal derivative. -/
theorem hasDerivAt_evalRealPolynomial (Q : Polynomial ℝ) (z : ℂ) :
    HasDerivAt (evalRealPolynomial Q)
      (evalRealPolynomial (Polynomial.derivative Q) z) z := by
  have h : HasDerivAt (fun x : ℂ => Polynomial.eval x (Q.map (algebraMap ℝ ℂ)))
      (Polynomial.eval z ((Q.map (algebraMap ℝ ℂ)).derivative)) z :=
    (Q.map (algebraMap ℝ ℂ)).hasDerivAt z
  rw [Polynomial.derivative_map] at h
  exact h

theorem continuous_evalRealPolynomial (Q : Polynomial ℝ) :
    Continuous (evalRealPolynomial Q) := by
  rw [continuous_iff_continuousAt]
  exact fun z => (hasDerivAt_evalRealPolynomial Q z).continuousAt

/-! ## The weighted raw resolvent term -/

/-- Polynomial-weighted raw resolvent term on the depth-`c` right edge. -/
def xiMassPolyVerticalRawTerm (Q : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R : ℝ)
    (q : XiZeroCopy) (y : ℝ) : ℂ :=
  evalRealPolynomial Q ((R : ℂ) + y * I) * xiMassVerticalRawTerm a τ R q y

/-- Gap-free integrated numerator for one divisor copy under a polynomial weight. -/
def xiMassPolyVerticalIntegratedNumerator (Q : Polynomial ℝ) (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  xiMassVerticalEnvelope c τ R *
    (evalRealPolynomialNormBound Q (R + c) * (R + c) * xiVerticalCauchyKernelBoundAt c +
      2 * c * ((evalRealPolynomialNormBound (Polynomial.derivative Q) (R + c) +
            evalRealPolynomialNormBound Q (R + c) * ‖τ‖ * (R + c)) * (R + c) +
          evalRealPolynomialNormBound Q (R + c)))

theorem xiMassPolyVerticalIntegratedNumerator_nonneg (Q : Polynomial ℝ)
    {c R : ℝ} (hc : 1 / 2 < c) (hR : 0 ≤ R) (τ : ℂ) :
    0 ≤ xiMassPolyVerticalIntegratedNumerator Q c τ R := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hRc : 0 ≤ R + c := by linarith
  have hB := evalRealPolynomialNormBound_nonneg Q hRc
  have hB' := evalRealPolynomialNormBound_nonneg (Polynomial.derivative Q) hRc
  have hK := xiVerticalCauchyKernelBoundAt_nonneg hc
  have hE := (xiMassVerticalEnvelope_pos c τ R).le
  unfold xiMassPolyVerticalIntegratedNumerator
  have hτ := norm_nonneg τ
  positivity


/-! ## The slowly varying near estimate under a polynomial weight -/

private theorem polyVerticalPoint_norm_le {R c y : ℝ} (hR : 0 ≤ R) (hy : |y| ≤ c) :
    ‖((R : ℂ) + y * I)‖ ≤ R + c := by
  have hbound := Complex.norm_le_abs_re_add_abs_im ((R : ℂ) + y * I)
  have hre : (((R : ℂ) + y * I)).re = R := by simp
  have him : (((R : ℂ) + y * I)).im = y := by simp
  rw [hre, him, abs_of_nonneg hR] at hbound
  linarith

private theorem polyVerticalPoint_mem_strip {a c R y : ℝ} (hca : c < a) (hy : |y| ≤ c) :
    ((R : ℂ) + y * I) ∈ xiMassStrip a := by
  change |(((R : ℂ) + y * I)).im| < a
  have him : (((R : ℂ) + y * I)).im = y := by simp
  rw [him]
  exact lt_of_le_of_lt hy hca

/-- Under a polynomial weight the integrated contribution of one Xi divisor copy is still
exponentially small times `1/|p|`, uniformly as the vertical edge approaches the pole. -/
theorem norm_integral_xiMassPolyVerticalRawTerm_le
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ‖∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
      xiMassPolyVerticalIntegratedNumerator Q c τ R / ‖xiSpectralPoint q‖ := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  let W : ℂ → ℂ := evalRealPolynomial Q
  let g : ℂ → ℂ := xiMassAnalyticTest a τ
  let h : ℝ → ℂ := fun y => W (z y) * g (z y) * z y / p
  let E : ℝ := xiMassVerticalEnvelope c τ R
  let B : ℝ := evalRealPolynomialNormBound Q (R + c)
  let B' : ℝ := evalRealPolynomialNormBound (Polynomial.derivative Q) (R + c)
  let M : ℝ := E * ((B' + B * ‖τ‖ * (R + c)) * (R + c) + B) / ‖p‖
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRc : 0 ≤ R + c := by linarith
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hpNorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hpim := xiSpectralPoint_im_mem_openHalf q
  have hpimAbs : |p.im| ≤ c := by
    rw [abs_le]
    constructor <;> linarith [hpim.1, hpim.2]
  have hB : 0 ≤ B := evalRealPolynomialNormBound_nonneg Q hRc
  have hB' : 0 ≤ B' := evalRealPolynomialNormBound_nonneg _ hRc
  have hE : 0 < E := xiMassVerticalEnvelope_pos c τ R
  have hzMem : ∀ y ∈ Icc (-c) c, z y ∈ xiMassStrip a := by
    intro y hy
    exact polyVerticalPoint_mem_strip hca ((abs_le).2 hy)
  have hzNorm : ∀ y ∈ Icc (-c) c, ‖z y‖ ≤ R + c := by
    intro y hy
    exact polyVerticalPoint_norm_le hR0 ((abs_le).2 hy)
  have hzDeriv (y : ℝ) : HasDerivAt z I y := by
    dsimp only [z]
    have hmul : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using hmul.const_add (R : ℂ)
  have hWDeriv (y : ℝ) : HasDerivAt (fun y : ℝ => W (z y))
      (evalRealPolynomial (Polynomial.derivative Q) (z y) * I) y :=
    (hasDerivAt_evalRealPolynomial Q (z y)).comp y (hzDeriv y)
  have hgDeriv (y : ℝ) (hy : y ∈ Icc (-c) c) : HasDerivAt (fun y => g (z y))
      ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) y :=
    (hasDerivAt_xiMassAnalyticTest ha τ (hzMem y hy)).comp y (hzDeriv y)
  have hprodDeriv (y : ℝ) (hy : y ∈ Icc (-c) c) :
      HasDerivAt (fun y : ℝ => W (z y) * g (z y))
        (evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
          W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) y :=
    (hWDeriv y).mul (hgDeriv y hy)
  have hhDeriv (y : ℝ) (hy : y ∈ Icc (-c) c) : HasDerivAt h
      (((evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
            W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) * z y +
          W (z y) * g (z y) * I) / p) y := by
    dsimp only [h]
    exact ((hprodDeriv y hy).mul (hzDeriv y)).div_const p
  have hgValue : ∀ y ∈ Icc (-c) c, ‖g (z y)‖ ≤ E := by
    intro y hy
    have hyAbs : |y| ≤ c := (abs_le).2 hy
    have hraw := norm_xiMassAnalyticTest_le ha hτ.le (hzMem y hy)
    calc
      ‖g (z y)‖ ≤ Real.exp (-τ.re * |(z y).re| + |τ.im| * |(z y).im|) := hraw
      _ ≤ E := by
        dsimp only [E, xiMassVerticalEnvelope]
        rw [Real.exp_le_exp]
        have hzre : |(z y).re| = R := by dsimp only [z]; simp [abs_of_pos hRp]
        have hzim : |(z y).im| = |y| := by dsimp only [z]; simp
        rw [hzre, hzim]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hyAbs (abs_nonneg τ.im))
  have hWValue : ∀ y ∈ Icc (-c) c, ‖W (z y)‖ ≤ B :=
    fun y hy => norm_evalRealPolynomial_le Q (hzNorm y hy)
  have hW'Value : ∀ y ∈ Icc (-c) c,
      ‖evalRealPolynomial (Polynomial.derivative Q) (z y)‖ ≤ B' :=
    fun y hy => norm_evalRealPolynomial_le _ (hzNorm y hy)
  have hM : 0 ≤ M := by
    dsimp only [M]
    have := norm_nonneg τ
    positivity
  have hdiff : ∀ y ∈ Icc (-c) c, DifferentiableAt ℝ h y :=
    fun y hy => (hhDeriv y hy).differentiableAt
  have hderiv : ∀ y ∈ Icc (-c) c, ‖deriv h y‖ ≤ M := by
    intro y hy
    have hyAbs : |y| ≤ c := (abs_le).2 hy
    have hzN := hzNorm y hy
    have hsqrtRe := abs_re_le_xiMassAnalyticSqrt_re a (z y)
    have hsqrtNorm : 1 ≤ ‖xiMassAnalyticSqrt a (z y)‖ := by
      have hreNorm := Complex.abs_re_le_norm (xiMassAnalyticSqrt a (z y))
      have hzre : |(z y).re| = R := by dsimp only [z]; simp [abs_of_pos hRp]
      rw [hzre] at hsqrtRe
      exact hR.trans (hsqrtRe.trans ((le_abs_self _).trans hreNorm))
    have hratio : ‖z y / xiMassAnalyticSqrt a (z y)‖ ≤ R + c := by
      rw [norm_div]
      exact (div_le_self (norm_nonneg (z y)) hsqrtNorm).trans hzN
    have htest := hgValue y hy
    have hWv := hWValue y hy
    have hW'v := hW'Value y hy
    rw [(hhDeriv y hy).deriv, norm_div]
    have hnum : ‖(evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
            W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) * z y +
          W (z y) * g (z y) * I‖
        ≤ E * ((B' + B * ‖τ‖ * (R + c)) * (R + c) + B) := by
      calc
      ‖(evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
            W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) * z y +
          W (z y) * g (z y) * I‖
          ≤ ‖(evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
              W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) * z y‖ +
            ‖W (z y) * g (z y) * I‖ := norm_add_le _ _
      _ = (‖evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
              W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)‖) * ‖z y‖ +
            ‖W (z y)‖ * ‖g (z y)‖ := by
        simp [mul_assoc]
      _ ≤ ((‖evalRealPolynomial (Polynomial.derivative Q) (z y)‖ * ‖g (z y)‖) +
              ‖W (z y)‖ * (‖τ‖ * ‖z y / xiMassAnalyticSqrt a (z y)‖ * ‖g (z y)‖)) * ‖z y‖ +
            ‖W (z y)‖ * ‖g (z y)‖ := by
        gcongr
        · calc
            ‖evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
                W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)‖
                ≤ ‖evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y)‖ +
                  ‖W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)‖ :=
                norm_add_le _ _
            _ = _ := by simp [mul_assoc]
      _ ≤ ((B' * E) + B * (‖τ‖ * (R + c) * E)) * (R + c) + B * E := by
        gcongr
      _ = E * ((B' + B * ‖τ‖ * (R + c)) * (R + c) + B) := by ring
    calc ‖(evalRealPolynomial (Polynomial.derivative Q) (z y) * I * g (z y) +
            W (z y) * ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I)) * z y +
          W (z y) * g (z y) * I‖ / ‖p‖
        ≤ (E * ((B' + B * ‖τ‖ * (R + c)) * (R + c) + B)) / ‖p‖ := by
          apply div_le_div_of_nonneg_right _ (norm_nonneg p)
          exact hnum
      _ = M := rfl
  have hhValue : ‖h p.im‖ ≤ B * E * (R + c) / ‖p‖ := by
    have hpMem : p.im ∈ Icc (-c) c := (abs_le).mp hpimAbs
    dsimp only [h]
    rw [norm_div, norm_mul, norm_mul]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg p)
    exact mul_le_mul
      (mul_le_mul (hWValue _ hpMem) (hgValue _ hpMem) (norm_nonneg _) hB)
      (hzNorm _ hpMem) (norm_nonneg _) (by positivity)
  have hweighted := norm_integral_mul_vertical_cauchyKernel_le_at
    hc hM hdiff hderiv hpim (R := R) (by simpa only [p] using havoid)
  have hrewrite : ∀ y : ℝ,
      xiMassPolyVerticalRawTerm Q a τ R q y = h y * ((z y - p)⁻¹) := by
    intro y
    have hzp : z y - p ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [z, p, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
      exact havoid (sub_eq_zero.mp hre)
    dsimp only [xiMassPolyVerticalRawTerm, xiMassVerticalRawTerm, h, W, g, z, p]
    rw [show xiSpectralPoint q - ((R : ℂ) + y * I) =
        -(((R : ℂ) + y * I) - xiSpectralPoint q) by ring,
      mul_neg, div_neg]
    simp only [neg_div, neg_neg]
    field_simp [hp0, hzp]
  calc
    ‖∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ =
        ‖∫ y in -c..c, h y * ((z y - p)⁻¹)‖ := by
      congr 1
      exact integral_congr (fun y _ => hrewrite y)
    _ ≤ ‖h p.im‖ * xiVerticalCauchyKernelBoundAt c + (2 * c) * M := hweighted
    _ ≤ (B * E * (R + c) / ‖p‖) * xiVerticalCauchyKernelBoundAt c + (2 * c) * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hhValue (xiVerticalCauchyKernelBoundAt_nonneg hc)) le_rfl
    _ = xiMassPolyVerticalIntegratedNumerator Q c τ R / ‖xiSpectralPoint q‖ := by
      dsimp only [M, E, B, B', p]
      unfold xiMassPolyVerticalIntegratedNumerator
      field_simp

/-! ## Far divisor copies under a polynomial weight -/

theorem norm_xiMassPolyVerticalRawTerm_le_inv_sq
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re)
    (hR : 1 ≤ R) (hc0 : 0 ≤ c) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖) {y : ℝ} (hy : |y| ≤ c) :
    ‖xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
      evalRealPolynomialNormBound Q (R + c) *
          ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hB : ‖evalRealPolynomial Q ((R : ℂ) + y * I)‖ ≤
      evalRealPolynomialNormBound Q (R + c) :=
    norm_evalRealPolynomial_le Q (polyVerticalPoint_norm_le hR0 hy)
  have hraw := norm_xiMassVerticalRawTerm_le_inv_sq ha hca hτ hR hc0 q hfar hy
  have hB0 : 0 ≤ evalRealPolynomialNormBound Q (R + c) :=
    evalRealPolynomialNormBound_nonneg Q (by linarith)
  rw [xiMassPolyVerticalRawTerm, norm_mul]
  calc ‖evalRealPolynomial Q ((R : ℂ) + y * I)‖ * ‖xiMassVerticalRawTerm a τ R q y‖
      ≤ evalRealPolynomialNormBound Q (R + c) *
          (((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
            ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
        mul_le_mul hB hraw (norm_nonneg _) hB0
    _ = _ := by ring

theorem norm_integral_xiMassPolyVerticalRawTerm_le_inv_sq
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re)
    (hR : 1 ≤ R) (hc0 : 0 ≤ c) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖) :
    ‖∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
      evalRealPolynomialNormBound Q (R + c) *
          (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hpoint : ∀ y ∈ uIoc (-c) c,
      ‖xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
        evalRealPolynomialNormBound Q (R + c) *
            ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) c := by
      simpa [uIoc_of_le (by linarith : -c ≤ c)] using hy
    exact norm_xiMassPolyVerticalRawTerm_le_inv_sq Q ha hca hτ hR hc0 q hfar
      ((abs_le).2 ⟨hyIoc.1.le, hyIoc.2⟩)
  calc
    ‖∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
        (evalRealPolynomialNormBound Q (R + c) *
            ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * |c - (-c)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ c - -c)]
      ring

/-! ## The complete weighted vertical spectral law -/

/-- Mixed reciprocal-moment majorant for the polynomial-weighted mass vertical edge. -/
def xiMassPolyVerticalIntegratedMajorant (Q : Polynomial ℝ) (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  (xiMassPolyVerticalIntegratedNumerator Q c τ R * Real.sqrt (3 * (R + c))) *
      (∑' q : XiZeroCopy,
        1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
    (evalRealPolynomialNormBound Q (R + c) *
        (3 * c * xiMassVerticalEnvelope c τ R * (R + c))) *
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))

theorem summable_integral_xiMassPolyVerticalRawTerm_and_norm_tsum_le
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    Summable (fun q : XiZeroCopy => ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y) ∧
      ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ ≤
        xiMassPolyVerticalIntegratedMajorant Q c τ R := by
  let T : XiZeroCopy → ℂ := fun q =>
    ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y
  let w₃ : XiZeroCopy → ℝ := fun q =>
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let w₂ : XiZeroCopy → ℝ := fun q => 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  let N : ℝ := xiMassPolyVerticalIntegratedNumerator Q c τ R
  let c₃ : ℝ := N * Real.sqrt (3 * (R + c))
  let c₂ : ℝ := evalRealPolynomialNormBound Q (R + c) *
    (3 * c * xiMassVerticalEnvelope c τ R * (R + c))
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRc : 0 < R + c := by linarith
  have hN : 0 ≤ N := xiMassPolyVerticalIntegratedNumerator_nonneg Q hc hR0 τ
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hc₂ : 0 ≤ c₂ := by
    have hB : 0 ≤ evalRealPolynomialNormBound Q (R + c) :=
      evalRealPolynomialNormBound_nonneg Q hRc.le
    have hE := (xiMassVerticalEnvelope_pos c τ R).le
    dsimp only [c₂]
    positivity
  have hw₃ : Summable w₃ := by
    simpa only [w₃] using xiSpectralPoint_inv_three_halves_summable
  have hw₂ : Summable w₂ := by
    simpa only [w₂] using xiSpectralPoint_inv_sq_summable
  have hsum₃ : Summable (fun q => c₃ * w₃ q) := hw₃.mul_left c₃
  have hsum₂ : Summable (fun q => c₂ * w₂ q) := hw₂.mul_left c₂
  have hmajorant : Summable (fun q => c₃ * w₃ q + c₂ * w₂ q) := hsum₃.add hsum₂
  have hbound : ∀ q : XiZeroCopy, ‖T q‖ ≤ c₃ * w₃ q + c₂ * w₂ q := by
    intro q
    have hp : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    by_cases hnear : ‖xiSpectralPoint q‖ ≤ 3 * (R + c)
    · have hinv := one_div_norm_le_sqrt_mul_one_div_norm_sqrt_norm q
        (by simpa [abs_of_pos hRc] using hnear)
      calc
        ‖T q‖ ≤ N / ‖xiSpectralPoint q‖ := by
          simpa only [T, N] using
            norm_integral_xiMassPolyVerticalRawTerm_le Q ha hc hca hτ hR q (havoid q)
        _ = N * (1 / ‖xiSpectralPoint q‖) := by ring
        _ ≤ N * (Real.sqrt (3 * (R + c)) * w₃ q) :=
          mul_le_mul_of_nonneg_left (by simpa only [w₃] using hinv) hN
        _ = c₃ * w₃ q := by dsimp only [c₃]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_right (mul_nonneg hc₂ (by dsimp only [w₂]; positivity))
    · have hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖ := le_of_lt (lt_of_not_ge hnear)
      calc
        ‖T q‖ ≤ c₂ / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
          simpa only [T, c₂] using
            norm_integral_xiMassPolyVerticalRawTerm_le_inv_sq Q ha hca hτ hR hc0 q hfar
        _ = c₂ * w₂ q := by dsimp only [w₂]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_left (mul_nonneg hc₃ (by dsimp only [w₃]; positivity))
  have hT : Summable T := hmajorant.of_norm_bounded hbound
  refine ⟨by simpa only [T] using hT, ?_⟩
  calc
    ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y‖ =
        ‖∑' q, T q‖ := by rfl
    _ ≤ ∑' q, ‖T q‖ := norm_tsum_le_tsum_norm hT.norm
    _ ≤ ∑' q, (c₃ * w₃ q + c₂ * w₂ q) := Summable.tsum_mono hT.norm hmajorant hbound
    _ = c₃ * (∑' q, w₃ q) + c₂ * (∑' q, w₂ q) := by
      rw [hsum₃.tsum_add hsum₂, tsum_mul_left, tsum_mul_left]
    _ = xiMassPolyVerticalIntegratedMajorant Q c τ R := rfl

/-! ## The weighted majorant still vanishes -/

private theorem le_mul_of_one_le_right' {X V : ℝ} (hX : 0 ≤ X) (hV : 1 ≤ V) : X ≤ X * V := by
  nlinarith

theorem tendsto_exp_neg_mul_shift_pow {delta b : ℝ} (hd : 0 < delta) (n : ℕ) :
    Tendsto (fun R : ℝ => Real.exp (-delta * R) * (b + R) ^ n) atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hcomp : Tendsto (fun R : ℝ => (delta * (b + R)) ^ n *
      Real.exp (-(delta * (b + R)))) atTop (𝓝 0) := by
    refine hbase.comp ?_
    exact Filter.tendsto_atTop_add_const_left _ _ (tendsto_id) |>.const_mul_atTop hd
  have hfin : Tendsto (fun R : ℝ => (Real.exp (-(delta * b)) * delta ^ n)⁻¹ *
      ((delta * (b + R)) ^ n * Real.exp (-(delta * (b + R))))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul ((Real.exp (-(delta * b)) * delta ^ n)⁻¹)
  refine hfin.congr fun R => ?_
  rw [mul_pow, show -(delta * (b + R)) = -(delta * b) + (-delta * R) by ring,
    Real.exp_add]
  have hne : Real.exp (-(delta * b)) ≠ 0 := Real.exp_ne_zero _
  have hdn : (delta : ℝ) ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hd)
  field_simp

/-- Abstract decay of a near/far vertical majorant whose weight grows at most polynomially. -/
private theorem tendsto_polyEnvelope_aux {delta c A A' K TN S₃ S₂ E₀ : ℝ}
    (hdelta : 0 < delta) (hc0 : 0 ≤ c) (hA : 0 ≤ A) (hA' : 0 ≤ A') (hK : 0 ≤ K)
    (hTN : 0 ≤ TN) (hS₃ : 0 ≤ S₃) (hS₂ : 0 ≤ S₂) (hE₀ : 0 < E₀) (d : ℕ)
    {B B' : ℝ → ℝ}
    (hB0 : ∀ R : ℝ, 1 ≤ R → 0 ≤ B R) (hB'0 : ∀ R : ℝ, 1 ≤ R → 0 ≤ B' R)
    (hB : ∀ R : ℝ, 1 ≤ R → B R ≤ A * (1 + c + R) ^ d)
    (hB' : ∀ R : ℝ, 1 ≤ R → B' R ≤ A' * (1 + c + R) ^ d) :
    Tendsto (fun R : ℝ =>
      ((E₀ * Real.exp (-delta * R)) *
            (B R * (R + c) * K +
              2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R)) *
          Real.sqrt (3 * (R + c))) * S₃ +
        (B R * (3 * c * (E₀ * Real.exp (-delta * R)) * (R + c))) * S₂) atTop (𝓝 0) := by
  set C : ℝ := E₀ * (3 * (A * K + 2 * c * (A' + A * TN + A)) * S₃ + 3 * c * A * S₂) with hCEq
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ((E₀ * Real.exp (-delta * R)) *
            (B R * (R + c) * K +
              2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R)) *
          Real.sqrt (3 * (R + c))) * S₃ +
        (B R * (3 * c * (E₀ * Real.exp (-delta * R)) * (R + c))) * S₂ ≤
        C * (Real.exp (-delta * R) * (1 + c + R) ^ (d + 3)) := by
    intro R hR
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    have hV1 : (1 : ℝ) ≤ 1 + c + R := by linarith
    have hRcV : R + c ≤ 1 + c + R := by linarith
    have hRc0 : 0 ≤ R + c := by linarith
    have hP0 : (0 : ℝ) ≤ (1 + c + R) ^ d := by positivity
    have hE : (0 : ℝ) < E₀ * Real.exp (-delta * R) := by positivity
    have hBR := hB R hR
    have hB'R := hB' R hR
    have hBR0 := hB0 R hR
    have hB'R0 := hB'0 R hR
    have hsqrt : Real.sqrt (3 * (R + c)) ≤ 3 * (1 + c + R) := by
      have h2 : Real.sqrt (3 * (R + c)) ≤ 3 * (R + c) := by
        have h := Real.sqrt_le_sqrt (show 3 * (R + c) ≤ (3 * (R + c)) ^ (2 : ℕ) by nlinarith)
        rwa [Real.sqrt_sq (by linarith)] at h
      linarith
    have hinner : B R * (R + c) * K +
          2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R) ≤
        (A * K + 2 * c * (A' + A * TN + A)) *
          ((1 + c + R) ^ d * (1 + c + R) * (1 + c + R)) := by
      have hstep : B R * (R + c) * K +
            2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R) ≤
          (A * (1 + c + R) ^ d) * (1 + c + R) * K +
            2 * c * (((A' * (1 + c + R) ^ d) +
                (A * (1 + c + R) ^ d) * TN * (1 + c + R)) * (1 + c + R) +
              (A * (1 + c + R) ^ d)) := by
        gcongr
      have e1 : A * K * (1 + c + R) ^ d * (1 + c + R) ≤
          A * K * (1 + c + R) ^ d * (1 + c + R) * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      have e2 : 2 * c * A' * (1 + c + R) ^ d * (1 + c + R) ≤
          2 * c * A' * (1 + c + R) ^ d * (1 + c + R) * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      have e3 : 2 * c * A * (1 + c + R) ^ d ≤
          2 * c * A * (1 + c + R) ^ d * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      have e4 : 2 * c * A * (1 + c + R) ^ d * (1 + c + R) ≤
          2 * c * A * (1 + c + R) ^ d * (1 + c + R) * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      linarith
    have hinner0 : 0 ≤ B R * (R + c) * K +
        2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R) := by positivity
    have hterm1 : ((E₀ * Real.exp (-delta * R)) *
          (B R * (R + c) * K +
            2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R)) *
        Real.sqrt (3 * (R + c))) * S₃ ≤
        (E₀ * Real.exp (-delta * R)) *
          ((A * K + 2 * c * (A' + A * TN + A)) *
            ((1 + c + R) ^ d * (1 + c + R) * (1 + c + R))) *
          (3 * (1 + c + R)) * S₃ := by
      have h1 : (E₀ * Real.exp (-delta * R)) *
            (B R * (R + c) * K +
              2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R)) ≤
          (E₀ * Real.exp (-delta * R)) *
            ((A * K + 2 * c * (A' + A * TN + A)) *
              ((1 + c + R) ^ d * (1 + c + R) * (1 + c + R))) :=
        mul_le_mul_of_nonneg_left hinner hE.le
      have h2 := mul_le_mul h1 hsqrt (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right h2 hS₃
    have hterm2 : (B R * (3 * c * (E₀ * Real.exp (-delta * R)) * (R + c))) * S₂ ≤
        (A * (1 + c + R) ^ d) *
          (3 * c * (E₀ * Real.exp (-delta * R)) * (1 + c + R)) * S₂ := by
      have h1 : B R * (3 * c * (E₀ * Real.exp (-delta * R)) * (R + c)) ≤
          (A * (1 + c + R) ^ d) *
            (3 * c * (E₀ * Real.exp (-delta * R)) * (1 + c + R)) := by
        gcongr
      exact mul_le_mul_of_nonneg_right h1 hS₂
    have hpow3 : (1 + c + R) ^ (d + 3)
        = (1 + c + R) ^ d * (1 + c + R) * (1 + c + R) * (1 + c + R) := by
      rw [pow_add]; ring
    have hlast : (A * (1 + c + R) ^ d) *
        (3 * c * (E₀ * Real.exp (-delta * R)) * (1 + c + R)) * S₂ ≤
        (3 * c * A * S₂) * (E₀ * (Real.exp (-delta * R) *
          ((1 + c + R) ^ d * (1 + c + R) * (1 + c + R) * (1 + c + R)))) := by
      have h1 : A * (1 + c + R) ^ d * (3 * c * S₂) *
            (E₀ * Real.exp (-delta * R)) * (1 + c + R) ≤
          A * (1 + c + R) ^ d * (3 * c * S₂) *
            (E₀ * Real.exp (-delta * R)) * (1 + c + R) * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      have h2 : A * (1 + c + R) ^ d * (3 * c * S₂) *
            (E₀ * Real.exp (-delta * R)) * (1 + c + R) * (1 + c + R) ≤
          A * (1 + c + R) ^ d * (3 * c * S₂) *
            (E₀ * Real.exp (-delta * R)) * (1 + c + R) * (1 + c + R) * (1 + c + R) :=
        le_mul_of_one_le_right' (by positivity) hV1
      linarith
    rw [hCEq, hpow3]
    linarith
  refine squeeze_zero' (eventually_atTop.2 ⟨1, fun R hR => ?_⟩)
    (eventually_atTop.2 ⟨1, hbound⟩) ?_
  · have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    have hRc0 : 0 ≤ R + c := by linarith
    have hBR0 := hB0 R hR
    have hB'R0 := hB'0 R hR
    have hE : (0 : ℝ) < E₀ * Real.exp (-delta * R) := by positivity
    have t1 : 0 ≤ B R * (R + c) * K := mul_nonneg (mul_nonneg hBR0 hRc0) hK
    have t2 : 0 ≤ (B' R + B R * TN * (R + c)) * (R + c) + B R :=
      add_nonneg (mul_nonneg (add_nonneg hB'R0
        (mul_nonneg (mul_nonneg hBR0 hTN) hRc0)) hRc0) hBR0
    have hinner0 : 0 ≤ B R * (R + c) * K +
        2 * c * ((B' R + B R * TN * (R + c)) * (R + c) + B R) :=
      add_nonneg t1 (mul_nonneg (by linarith) t2)
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hE.le hinner0) (Real.sqrt_nonneg _)) hS₃)
      (mul_nonneg (mul_nonneg hBR0
        (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * c) hE.le) hRc0)) hS₂)
  · simpa using (tendsto_exp_neg_mul_shift_pow (b := 1 + c) hdelta (d + 3)).const_mul C

/-- Exponential mass decay absorbs the polynomial weight together with the complete near/far
reciprocal-moment majorant. -/
theorem tendsto_xiMassPolyVerticalIntegratedMajorant_atTop
    (Q : Polynomial ℝ) {c : ℝ} (hc : 1 / 2 < c) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (xiMassPolyVerticalIntegratedMajorant Q c τ) atTop (𝓝 0) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hd' : (Polynomial.derivative Q).natDegree ≤ Q.natDegree :=
    le_trans (Polynomial.natDegree_derivative_le Q) (Nat.sub_le _ _)
  have haux := tendsto_polyEnvelope_aux (delta := τ.re) (c := c)
    (A := evalRealPolynomialCoeffSum Q)
    (A' := evalRealPolynomialCoeffSum (Polynomial.derivative Q))
    (K := xiVerticalCauchyKernelBoundAt c) (TN := ‖τ‖)
    (S₃ := ∑' q : XiZeroCopy, 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖))
    (S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
    (E₀ := Real.exp (|τ.im| * c))
    hτ hc0 (evalRealPolynomialCoeffSum_nonneg Q) (evalRealPolynomialCoeffSum_nonneg _)
    (xiVerticalCauchyKernelBoundAt_nonneg hc) (norm_nonneg τ)
    (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity)
    (Real.exp_pos _) Q.natDegree
    (B := fun R => evalRealPolynomialNormBound Q (R + c))
    (B' := fun R => evalRealPolynomialNormBound (Polynomial.derivative Q) (R + c))
    (fun R _ => evalRealPolynomialNormBound_nonneg Q (by linarith))
    (fun R _ => evalRealPolynomialNormBound_nonneg _ (by linarith))
    (fun R hR => by
      have h := evalRealPolynomialNormBound_le_coeffSum_mul_pow Q
        (show (0 : ℝ) ≤ R + c by linarith) (le_refl Q.natDegree)
      rwa [show 1 + (R + c) = 1 + c + R by ring] at h)
    (fun R hR => by
      have h := evalRealPolynomialNormBound_le_coeffSum_mul_pow (Polynomial.derivative Q)
        (show (0 : ℝ) ≤ R + c by linarith) hd'
      rwa [show 1 + (R + c) = 1 + c + R by ring] at h)
  refine haux.congr fun R => ?_
  rw [xiMassPolyVerticalIntegratedMajorant, xiMassPolyVerticalIntegratedNumerator,
    xiMassVerticalEnvelope,
    show -τ.re * R + |τ.im| * c = |τ.im| * c + -τ.re * R by ring, Real.exp_add]

/-! ## Exchanging the divisor sum with the weighted edge integral -/

theorem continuousOn_xiMassPolyVerticalRawTerm (Q : Polynomial ℝ) {a c R : ℝ}
    (ha : 0 < a) (hca : c < a) (τ : ℂ) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ContinuousOn (xiMassPolyVerticalRawTerm Q a τ R q) (Icc (-c) c) := by
  have hW : Continuous (fun y : ℝ => evalRealPolynomial Q ((R : ℂ) + y * I)) := by
    exact (continuous_evalRealPolynomial Q).comp (by fun_prop)
  exact hW.continuousOn.mul (continuousOn_xiMassVerticalRawTerm ha hca τ q havoid)

/-- Far weighted mass spectrum is absolutely integrable with reciprocal-square size. -/
theorem integral_norm_xiMassPolyVerticalRawTerm_le_inv_sq
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖) :
    (∫ y in -c..c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖) ≤
      evalRealPolynomialNormBound Q (R + c) *
          (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have him := xiSpectralPoint_im_mem_openHalf q
  have himAbs : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [him.1, him.2]
  have havoid : R ≠ (xiSpectralPoint q).re := by
    intro heq
    have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [← heq, abs_of_nonneg hR0] at hnorm
    linarith
  have hcont := continuousOn_xiMassPolyVerticalRawTerm Q ha hca τ q havoid
  have hcontu : ContinuousOn (xiMassPolyVerticalRawTerm Q a τ R q) (uIcc (-c) c) := by
    simpa only [uIcc_of_le (by linarith : -c ≤ c)] using hcont
  have hfint : IntervalIntegrable (xiMassPolyVerticalRawTerm Q a τ R q) volume (-c) c :=
    hcontu.intervalIntegrable
  let C : ℝ := evalRealPolynomialNormBound Q (R + c) *
    ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hmono : (∫ y in -c..c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖) ≤
      ∫ _y in -c..c, C := by
    apply intervalIntegral.integral_mono_on (by linarith) hfint.norm
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    exact norm_xiMassPolyVerticalRawTerm_le_inv_sq Q ha hca hτ hR hc0 q hfar
      ((abs_le).2 hy)
  calc
    (∫ y in -c..c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖) ≤ ∫ _y in -c..c, C := hmono
    _ = _ := by
      rw [intervalIntegral.integral_const]
      dsimp only [C]
      simp only [smul_eq_mul]
      ring

/-- Absolute integrability justifies exchanging the full mass divisor sum with the weighted edge
integral. -/
theorem integral_tsum_xiMassPolyVerticalRawTerm_eq_tsum_integral
    (Q : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in -c..c, ∑' q : XiZeroCopy, xiMassPolyVerticalRawTerm Q a τ R q y) =
      ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y := by
  let A : ℝ := evalRealPolynomialNormBound Q (R + c) *
    (3 * c * xiMassVerticalEnvelope c τ R * (R + c))
  let b : XiZeroCopy → ℝ := fun q => A / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hb : Summable b := by
    have hscaled := xiSpectralPoint_inv_sq_summable.mul_left A
    refine hscaled.congr (fun q => ?_)
    dsimp only [b]
    ring
  have hfarEventually :
      ∀ᶠ q : XiZeroCopy in Filter.cofinite, 3 * (R + c) ≤ ‖xiSpectralPoint q‖ := by
    have hRc : 0 < R + c := by linarith [le_trans (show (0:ℝ) ≤ 1 by norm_num) hR]
    have hfinite := xiSpectralPoint_finite_norm_le (B := 3 * (R + c)) (by positivity)
    have houtside :
        ∀ᶠ q : XiZeroCopy in Filter.cofinite, 3 * (R + c) < ‖xiSpectralPoint q‖ := by
      simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_le] using!
        hfinite.compl_mem_cofinite
    filter_upwards [houtside] with q hq
    exact hq.le
  have hnormSum : Summable (fun q : XiZeroCopy =>
      ∫ y in -c..c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖) := by
    apply hb.of_norm_bounded_eventually
    filter_upwards [hfarEventually] with q hfar
    have hnonneg : 0 ≤ ∫ y in -c..c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖ :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [b, A] using
      integral_norm_xiMassPolyVerticalRawTerm_le_inv_sq Q ha hc hca hτ hR q hfar
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiMassPolyVerticalRawTerm Q a τ R q)
        (volume.restrict (Ioc (-c) c)) := by
    intro q
    have hcont := continuousOn_xiMassPolyVerticalRawTerm Q ha hca τ q (havoid q)
    have hcontu : ContinuousOn (xiMassPolyVerticalRawTerm Q a τ R q) (uIcc (-c) c) := by
      simpa only [uIcc_of_le (by linarith : -c ≤ c)] using hcont
    have hint : IntervalIntegrable (xiMassPolyVerticalRawTerm Q a τ R q) volume (-c) c :=
      hcontu.intervalIntegrable
    rw [intervalIntegrable_iff] at hint
    simpa only [uIoc_of_le (by linarith : -c ≤ c)] using! hint
  have hnormSumRestrict : Summable (fun q : XiZeroCopy =>
      ∫ y in Ioc (-c) c, ‖xiMassPolyVerticalRawTerm Q a τ R q y‖) := by
    apply hnormSum.congr
    intro q
    exact intervalIntegral.integral_of_le (by linarith)
  rw [intervalIntegral.integral_of_le (by linarith : -c ≤ c)]
  calc
    (∫ y in Ioc (-c) c, ∑' q : XiZeroCopy, xiMassPolyVerticalRawTerm Q a τ R q y) =
        ∑' q : XiZeroCopy, ∫ y in Ioc (-c) c, xiMassPolyVerticalRawTerm Q a τ R q y :=
          (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
            hnormSumRestrict).symm
    _ = ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y := by
      apply tsum_congr
      intro q
      exact (intervalIntegral.integral_of_le (by linarith)).symm

theorem tsum_xiMassPolyVerticalRawTerm_eq_mul_relativeResolventTrace
    (Q : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R y : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑' q : XiZeroCopy, xiMassPolyVerticalRawTerm Q a τ R q y) =
      evalRealPolynomial Q ((R : ℂ) + y * I) *
        (xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
          xiRelativeResolventTrace ((R : ℂ) + y * I)) := by
  simp only [xiMassPolyVerticalRawTerm]
  rw [tsum_mul_left,
    tsum_xiMassVerticalRawTerm_eq_mul_relativeResolventTrace a τ R y havoid]

/-- **Cofinal vanishing of the polynomial-weighted vertical edge.** -/
theorem exists_large_integral_xiMassPoly_mul_logDeriv_XiC_norm_lt
    (Q : Polynomial ℝ) {a c : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧ 1 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      ‖∫ y in -c..c, evalRealPolynomial Q ((R : ℂ) + y * I) *
          (xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I))‖ < epsilon := by
  have hevent :=
    (tendsto_xiMassPolyVerticalIntegratedMajorant_atTop Q hc hτ).eventually_lt_const hepsilon
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  let u : ℝ := max (max X 1) M
  obtain ⟨R, hRI, havoid⟩ :=
    exists_real_avoiding_all_xiSpectralPoint_re (show u < u + 1 by linarith)
  have hXu : X ≤ u := le_trans (le_max_left X 1) (le_max_left (max X 1) M)
  have h1u : 1 ≤ u := le_trans (le_max_right X 1) (le_max_left (max X 1) M)
  have hMu : M ≤ u := le_max_right (max X 1) M
  have hXR : X < R := lt_of_le_of_lt hXu hRI.1
  have hR : 1 ≤ R := le_trans h1u hRI.1.le
  have hMR : M ≤ R := le_trans hMu hRI.1.le
  obtain ⟨_hsum, hbound⟩ :=
    summable_integral_xiMassPolyVerticalRawTerm_and_norm_tsum_le Q ha hc hca hτ hR havoid
  refine ⟨R, hXR, hR, havoid, ?_⟩
  have hedge : (∫ y in -c..c, evalRealPolynomial Q ((R : ℂ) + y * I) *
        (xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
          logDeriv XiC ((R : ℂ) + y * I))) =
      ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassPolyVerticalRawTerm Q a τ R q y := by
    rw [← integral_tsum_xiMassPolyVerticalRawTerm_eq_tsum_integral Q ha hc hca hτ hR havoid]
    apply integral_congr
    intro y _
    show evalRealPolynomial Q ((R : ℂ) + y * I) *
        (xiMassAnalyticTest a τ ((R : ℂ) + y * I) * logDeriv XiC ((R : ℂ) + y * I)) =
      ∑' q : XiZeroCopy, xiMassPolyVerticalRawTerm Q a τ R q y
    rw [tsum_xiMassPolyVerticalRawTerm_eq_mul_relativeResolventTrace Q a τ R y havoid,
      logDeriv_XiC_eq_relativeResolventTrace
        (XiC_ne_zero_on_avoiding_vertical R y havoid)]
  rw [hedge]
  exact lt_of_le_of_lt hbound (hM R hMR)

end

end RHTower
