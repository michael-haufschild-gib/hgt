import GaloisForLFunctions.RHTower.XiMassSymmetricContour
import GaloisForLFunctions.RHTower.XiMassPolynomialVerticalResolvent

/-!
# Exact finite Xi contour law for a polynomial-filtered analytic mass test

Squaring an arbitrary real polynomial evaluated at `z ^ 2` gives an even entire weight.  Multiplied
into the analytic mass test it stays analytic on the mass branch strip, so the local weighted
argument principle applies to every closed Xi rectangle inside that strip and the symmetric
rectangle still folds to twice its bottom Euler edge plus one right vertical edge.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The even real polynomial `P(X ^ 2) ^ 2`. -/
def xiMassPolySquare (P : Polynomial ℝ) : Polynomial ℝ :=
  (P.comp (Polynomial.X ^ 2)) * (P.comp (Polynomial.X ^ 2))

theorem evalRealPolynomial_comp_sq (P : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (P.comp (Polynomial.X ^ 2)) z = evalRealPolynomial P (z ^ 2) := by
  rw [evalRealPolynomial, evalRealPolynomial, Polynomial.map_comp, Polynomial.eval_comp]
  simp

theorem analyticAt_evalRealPolynomial (Q : Polynomial ℝ) (z : ℂ) :
    AnalyticAt ℂ (evalRealPolynomial Q) z := by
  have hdiff : Differentiable ℂ (evalRealPolynomial Q) :=
    fun w => (hasDerivAt_evalRealPolynomial Q w).differentiableAt
  exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

theorem evalRealPolynomial_xiMassPolySquare (P : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (xiMassPolySquare P) z = evalRealPolynomial P (z ^ 2) ^ 2 := by
  rw [xiMassPolySquare, evalRealPolynomial, Polynomial.map_mul, Polynomial.eval_mul]
  rw [show ((P.comp (Polynomial.X ^ 2)).map (algebraMap ℝ ℂ)).eval z =
      evalRealPolynomial (P.comp (Polynomial.X ^ 2)) z from rfl,
    evalRealPolynomial_comp_sq]
  ring

theorem evalRealPolynomial_xiMassPolySquare_neg (P : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (xiMassPolySquare P) (-z) =
      evalRealPolynomial (xiMassPolySquare P) z := by
  rw [evalRealPolynomial_xiMassPolySquare, evalRealPolynomial_xiMassPolySquare, neg_sq]

/-- The polynomial-filtered analytic mass test. -/
def xiMassPolyAnalyticTest (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (z : ℂ) : ℂ :=
  evalRealPolynomial P (z ^ 2) ^ 2 * xiMassAnalyticTest a τ z

theorem xiMassPolyAnalyticTest_neg (P : Polynomial ℝ) (a : ℝ) (τ z : ℂ) :
    xiMassPolyAnalyticTest P a τ (-z) = xiMassPolyAnalyticTest P a τ z := by
  rw [xiMassPolyAnalyticTest, xiMassPolyAnalyticTest, neg_sq, xiMassAnalyticTest_neg]

theorem analyticOnNhd_xiMassPolyAnalyticTest (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    AnalyticOnNhd ℂ (xiMassPolyAnalyticTest P a τ) (xiMassStrip a) := by
  intro z hz
  have hw : AnalyticAt ℂ (fun w : ℂ => evalRealPolynomial P (w ^ 2) ^ 2) z := by
    have hQ : AnalyticAt ℂ (evalRealPolynomial (xiMassPolySquare P)) z :=
      analyticAt_evalRealPolynomial _ z
    exact hQ.congr (Filter.Eventually.of_forall
      (fun w => evalRealPolynomial_xiMassPolySquare P w))
  exact hw.mul (analyticOnNhd_xiMassAnalyticTest ha τ z hz)

/-- A polynomial-filtered mass test on a branch-strip rectangle extracts every enclosed centered Xi
zero with exact analytic multiplicity. -/
theorem rectIntegral_xiMassPolyAnalyticTest_mul_logDeriv_eq_closedRectangleZeroSum
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (τ : ℂ) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiMassPolyAnalyticTest P a τ w := by
  classical
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ := exists_xiC_closedRectangle_factorization z₁ z₂
  let U : Set ℂ := {z : ℂ | h z ≠ 0} ∩ xiMassStrip a
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    exact fun z => (hhan z (Set.mem_univ z)).continuousAt
  have hUopen : IsOpen U :=
    (isOpen_compl_singleton.preimage hhcont).inter (isOpen_xiMassStrip a)
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := fun z hz => ⟨hhK z hz, hstrip hz⟩
  have hin : ∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_xiCClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hre.le] at hwre
    rw [uIcc_of_le him.le] at hwim
    have hrel : z₁.re < w.re := by
      have hne : z₁.re ≠ w.re := by
        intro heq
        have hedge : (z₁.re : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
        have hneXi := hleft w.im hwimU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.1 hne
    have hrer : w.re < z₂.re := by
      have hne : w.re ≠ z₂.re := by
        intro heq
        have hedge : (z₂.re : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
        have hneXi := hright w.im hwimU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.2 hne
    have himl : z₁.im < w.im := by
      have hne : z₁.im ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₁.im * I = w := by apply Complex.ext <;> simp [heq]
        have hneXi := hbot w.re hwreU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.1 hne
    have himr : w.im < z₂.im := by
      have hne : w.im ≠ z₂.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₂.im * I = w := by apply Complex.ext <;> simp [heq]
        have hneXi := htop w.re hwreU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.2 hne
    exact ⟨hrel, hrer, himl, himr⟩
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m hUopen
      (fun z hz => analyticOnNhd_xiMassPolyAnalyticTest P ha τ z hz.2) hin hsub
      (fun z _ => hhan z (Set.mem_univ z)) (fun _ hz => hz.1)
      (fun z _ => hfact z)
  calc
    rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z) z₁ z₂ =
        2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
          (m w : ℂ) * xiMassPolyAnalyticTest P a τ w := by simpa only using hres
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hm w hw]

/-- The same exact finite contour law in the multiplicity-copy carrier. -/
theorem rectIntegral_xiMassPolyAnalyticTest_mul_logDeriv_eq_xiZeroCopyClosedRectangleSum
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (τ : ℂ) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z) z₁ z₂ =
      2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiMassPolyAnalyticTest P a τ (xiSpectralPoint q) := by
  calc
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiMassPolyAnalyticTest P a τ w :=
      rectIntegral_xiMassPolyAnalyticTest_mul_logDeriv_eq_closedRectangleZeroSum
        P ha τ hre him hstrip hbot htop hright hleft
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * xiMassPolyAnalyticTest P a τ w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hzero : XiC w = 0 := (mem_xiCClosedRectangleZeros.mp hw).2
      rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
    _ = _ := by rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]

/-! ## Symmetric folding of the polynomial-filtered mass contour -/

theorem xiMassPolyLogDerivIntegrand_neg (P : Polynomial ℝ) (a : ℝ) (τ z : ℂ) :
    xiMassPolyAnalyticTest P a τ (-z) * logDeriv XiC (-z) =
      -(xiMassPolyAnalyticTest P a τ z * logDeriv XiC z) := by
  rw [xiMassPolyAnalyticTest_neg, logDeriv_XiC_neg]
  ring

theorem rectIntegral_xiMassPolyLogDeriv_symmetric (P : Polynomial ℝ) (a : ℝ) (τ : ℂ)
    (R c : ℝ) :
    rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * ((∫ x in -R..R,
          xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
            logDeriv XiC ((x : ℂ) - c * I)) +
        I • (∫ y in -c..c,
          xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I))) :=
  rectIntegral_symmetric_eq_two_bottom_add_vertical
    (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z)
    (xiMassPolyLogDerivIntegrand_neg P a τ) R c

theorem rectIntegral_xiMassPolyLogDeriv_symmetric_eq_xiZeroCopyClosedRectangleSum
    (P : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a)
    (hR : 0 < R) (τ : ℂ)
    (hright : ∀ y ∈ uIcc (-c) c, XiC ((R : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-c) c, XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassPolyAnalyticTest P a τ (xiSpectralPoint q) := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
  let z₂ : ℂ := (((R : ℝ) : ℂ) + c * I)
  have hz₁re : z₁.re = -R := by simp [z₁, Complex.mul_re]
  have hz₁im : z₁.im = -c := by simp [z₁, Complex.mul_im]
  have hz₂re : z₂.re = R := by simp [z₂, Complex.mul_re]
  have hz₂im : z₂.im = c := by simp [z₂, Complex.mul_im]
  have hre : z₁.re < z₂.re := by rw [hz₁re, hz₂re]; linarith
  have him : z₁.im < z₂.im := by rw [hz₁im, hz₂im]; linarith
  have hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a := by
    intro z hz
    have hzim := (Complex.mem_reProdIm.mp hz).2
    rw [hz₁im, hz₂im, uIcc_of_le (by linarith : -c ≤ c)] at hzim
    obtain ⟨hzim_lo, hzim_hi⟩ := hzim
    change |z.im| < a
    rw [abs_lt]
    constructor <;> linarith
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x _ hzero
    have hz := xiC_zero_im_mem_openHalf hzero
    have hedge : (((x : ℂ) + z₁.im * I)).im = -c := by rw [hz₁im]; simp
    rw [hedge] at hz
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x _ hzero
    have hz := xiC_zero_im_mem_openHalf hzero
    have hedge : (((x : ℂ) + z₂.im * I)).im = c := by rw [hz₂im]; simp
    rw [hedge] at hz
    linarith
  have hright' : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₂.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im] at hy
    simpa only [hz₂re] using hright y hy
  have hleft' : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₁.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im] at hy
    simpa only [hz₁re, Complex.ofReal_neg] using hleft y hy
  change rectIntegral (fun z => xiMassPolyAnalyticTest P a τ z * logDeriv XiC z) z₁ z₂ =
    2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
      xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)
  exact rectIntegral_xiMassPolyAnalyticTest_mul_logDeriv_eq_xiZeroCopyClosedRectangleSum
    P ha τ hre him hstrip hbot htop hright' hleft'

/-- On every symmetric mass rectangle the polynomial-filtered finite copied spectral sum equals
twice an honest Euler-line bottom integral plus one vertical error integral. -/
theorem xiMassPolyFiniteSpectralSum_eq_bottomPrimeArch_add_vertical
    (P : Polynomial ℝ) {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a)
    (hR : 0 < R) (τ : ℂ)
    (hright : ∀ y ∈ uIcc (-c) c, XiC ((R : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-c) c, XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0) :
    2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassPolyAnalyticTest P a τ (xiSpectralPoint q) =
      2 * ((∫ x in -R..R,
          xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
            (-I *
              (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  (((1 / 2 + c : ℝ) : ℂ) + x * I) -
                logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)))) +
        I • (∫ y in -c..c,
          xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I))) := by
  rw [← rectIntegral_xiMassPolyLogDeriv_symmetric_eq_xiZeroCopyClosedRectangleSum
    P ha hhalf hca hR τ hright hleft,
    rectIntegral_xiMassPolyLogDeriv_symmetric]
  congr 2
  apply intervalIntegral.integral_congr
  intro x _
  change xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
      logDeriv XiC ((x : ℂ) - c * I) = _
  rw [logDeriv_XiC_bottom_eq_primeArch hhalf x]

end

end RHTower
