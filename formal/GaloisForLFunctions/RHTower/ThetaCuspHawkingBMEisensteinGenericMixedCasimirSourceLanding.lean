import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinMixedCasimirPoleFillLanding

/-!
# Generic mixed-Casimir landing of the literal HB Eisenstein source

The earlier normalization audit evaluated the literal repeated-leg triple-Eisenstein source only
at `(P,Q)=(2,5)`.  This module closes the full strict unfolding chamber.  For packed parameters

```text
1 < Re P,       2 Re P < Re Q,
```

put `u=P-1/2`, `a=1-2P`, `w=Q-2P+1`, and `A=2P+Q-1`.  The literal nonconstant Whittaker source is

```text
8 Λ(2Q) (2π)^(-Q) ∫₀∞ x^(Q-1) K_u(x)^2 dx · L(σ_a σ_a,w).
```

The corpus two-shift Ramanujan product and two-K Mellin theorem, together with an exact
complex-cpow archimedean cancellation proved here, give

```text
S(P,Q) = Λ(A) Λ(Q)^2 Λ(w).
```

The positive fourth source argument is `w=1-(2P-Q)`.  Using the entire Xi functional equation on
that channel and multiplying by the already forced rank-three mixed-Casimir pole-fill multiplier
then gives the canonical four-Xi vertex throughout the chamber.  The balanced C-A.9u landing is
therefore no longer a fixed-point calibration.

Zagier's regularized triple-Eisenstein four-completed-zeta formula is literature.  The new result
here is the dependency-closed source-side weld from the literal Whittaker/Bessel/Dirichlet source
to the exact rank-three pole-fill normalization used by the HB chain:

```text
literal generic source -> rank-three mixed Casimir -> canonical scalar family -> C-A.9u
  -> negative BM -> left QNM -> HC94 source/clock cocycle -> RH.
```

`[NEW SOURCE WELD] [PAPER-PROVED] [LEAN-PROVED] [HB] [C-A.9x-f]`
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- Strict repeated-leg triple-unfolding chamber, carried as data so every final result is a
closed theorem without hypotheses. -/
structure D4BMStrictTripleUnfoldingParameters where
  P : D4BMEisensteinAbsoluteConvergenceParameter
  Q : D4BMEisensteinAbsoluteConvergenceParameter
  two_P_re_lt_Q_re : 2 * P.s.re < Q.s.re

namespace D4BMStrictTripleUnfoldingParameters

/-- Repeated-leg Bessel order. -/
def u (X : D4BMStrictTripleUnfoldingParameters) : ℂ := X.P.s - 1 / 2

/-- Generalized-divisor shift in the repeated Whittaker coefficient. -/
def a (X : D4BMStrictTripleUnfoldingParameters) : ℂ := 1 - 2 * X.P.s

/-- Positive functional-equation reflection of the fourth canonical channel. -/
def w (X : D4BMStrictTripleUnfoldingParameters) : ℂ := X.Q.s - 2 * X.P.s + 1

/-- First positive completed-zeta channel. -/
def A (X : D4BMStrictTripleUnfoldingParameters) : ℂ := 2 * X.P.s + X.Q.s - 1

/-- Fourth canonical channel before functional-equation reflection. -/
def C (X : D4BMStrictTripleUnfoldingParameters) : ℂ := 2 * X.P.s - X.Q.s

lemma a_re_neg (X : D4BMStrictTripleUnfoldingParameters) : X.a.re < 0 := by
  simp [a]
  linarith [X.P.re_gt_one]

lemma w_re_gt_one (X : D4BMStrictTripleUnfoldingParameters) : 1 < X.w.re := by
  simp [w]
  linarith [X.two_P_re_lt_Q_re]

lemma A_re_gt_one (X : D4BMStrictTripleUnfoldingParameters) : 1 < X.A.re := by
  simp [A]
  linarith [X.P.re_gt_one, X.Q.re_gt_one]

/-- The strict unfolding chamber implies the sharp two-K Mellin chamber. -/
lemma bessel_chamber (X : D4BMStrictTripleUnfoldingParameters) :
    |X.u.re| + |X.u.re| < X.Q.s.re := by
  have hu : 0 < X.u.re := by
    simp [u]
    linarith [X.P.re_gt_one]
  simp only [abs_of_pos hu]
  simp [u]
  linarith [X.two_P_re_lt_Q_re]

def negativeShift (X : D4BMStrictTripleUnfoldingParameters) : D4BMNegativeDivisorShift :=
  ⟨X.a, X.a_re_neg⟩

def ramanujanChamber (X : D4BMStrictTripleUnfoldingParameters) :
    D4BMRamanujanProductChamber where
  a := X.negativeShift
  b := X.negativeShift
  w := X.w
  w_re_gt_one := X.w_re_gt_one

/-- The two-shift Ramanujan product at the exact generic Whittaker parameters. -/
lemma ramanujan_value_eq (X : D4BMStrictTripleUnfoldingParameters) :
    LSeries (d4BMDivisorProductArithmetic X.a X.a) X.w =
      riemannZeta X.w * riemannZeta X.Q.s ^ 2 * riemannZeta X.A /
        riemannZeta (2 * X.Q.s) := by
  have h := LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient X.ramanujanChamber
  simp only [ramanujanChamber, negativeShift, d4BMRamanujanFourZetaValue,
    d4BMRamanujanPolarZetaValue] at h
  convert h using 1
  all_goals simp only [a, w, A]
  all_goals ring_nf

/-- The two-K Mellin product at the exact generic Bessel parameters. -/
lemma bessel_value_eq (X : D4BMStrictTripleUnfoldingParameters) :
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (X.Q.s - 1) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x X.u *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x X.u) =
      (2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
        (Complex.Gamma (X.A / 2) *
          Complex.Gamma (X.Q.s / 2) *
          Complex.Gamma (X.Q.s / 2) *
          Complex.Gamma (X.w / 2)) := by
  have h :=
    _root_.GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
      (s := X.Q.s) (mu := X.u) (nu := X.u) X.bessel_chamber
  convert h using 1
  all_goals simp only [u, A, w]
  all_goals ring_nf

/-- Exact generic cancellation of all archimedean factors in the unfolded source. -/
private lemma archimedean_source_eq (X : D4BMStrictTripleUnfoldingParameters) :
    8 * Complex.Gammaℝ (2 * X.Q.s) *
        ((((2 * Real.pi : ℝ) : ℂ) ^ (-X.Q.s))) *
        ((2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
          (Complex.Gamma (X.A / 2) *
            Complex.Gamma (X.Q.s / 2) *
            Complex.Gamma (X.Q.s / 2) *
            Complex.Gamma (X.w / 2))) =
      Complex.Gammaℝ X.A * Complex.Gammaℝ X.Q.s ^ 2 *
        Complex.Gammaℝ X.w := by
  rw [Complex.Gammaℝ, Complex.Gammaℝ, Complex.Gammaℝ, Complex.Gammaℝ]
  norm_num
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-X.Q.s) =
      (2 : ℂ) ^ (-X.Q.s) * (Real.pi : ℂ) ^ (-X.Q.s) := by
    simpa using Complex.mul_cpow_ofReal_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le (-X.Q.s)
  rw [h2pi]
  have hpow2 : (2 : ℂ) ^ (-X.Q.s) * (2 : ℂ) ^ (X.Q.s - 3) = 1 / 8 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    have hexp : -X.Q.s + (X.Q.s - 3) = (-3 : ℂ) := by ring
    rw [hexp]
    have h := Complex.cpow_neg_eq_inv_pow_ofReal_pos
      (a := 2) (by norm_num : (0 : ℝ) < 2) (3 : ℂ)
    norm_num at h ⊢
    exact h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpowers :
      (Real.pi : ℂ) ^ (-(2 * X.Q.s) / 2) *
          (Real.pi : ℂ) ^ (-X.Q.s) =
        (Real.pi : ℂ) ^ (-X.A / 2) *
          ((Real.pi : ℂ) ^ (-X.Q.s / 2)) ^ 2 *
          (Real.pi : ℂ) ^ (-X.w / 2) := by
    rw [pow_two]
    repeat' rw [← Complex.cpow_add _ _ hpi]
    congr 1
    simp only [A, w]
    ring
  have hgamma : Complex.Gamma X.Q.s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by linarith [X.Q.re_gt_one])
  have hpowers' :
      (Real.pi : ℂ) ^ (-X.Q.s) * (Real.pi : ℂ) ^ (-X.Q.s) =
        (Real.pi : ℂ) ^ (-X.A / 2) *
          ((Real.pi : ℂ) ^ (-X.Q.s / 2)) ^ 2 *
          (Real.pi : ℂ) ^ (-X.w / 2) := by
    simpa only [show -(2 * X.Q.s) / 2 = -X.Q.s by ring] using hpowers
  rw [show -(2 * X.Q.s) / 2 = -X.Q.s by ring]
  calc
    8 * ((Real.pi : ℂ) ^ (-X.Q.s) * Complex.Gamma X.Q.s) *
          ((2 : ℂ) ^ (-X.Q.s) * (Real.pi : ℂ) ^ (-X.Q.s)) *
          ((2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
            (Complex.Gamma (X.A / 2) *
              Complex.Gamma (X.Q.s / 2) *
              Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2))) =
        (8 * ((2 : ℂ) ^ (-X.Q.s) * (2 : ℂ) ^ (X.Q.s - 3))) *
          (((Real.pi : ℂ) ^ (-X.Q.s) * (Real.pi : ℂ) ^ (-X.Q.s)) *
            (Complex.Gamma (X.A / 2) *
              Complex.Gamma (X.Q.s / 2) *
              Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2))) := by
      field_simp [hgamma]
    _ = ((Real.pi : ℂ) ^ (-X.Q.s) * (Real.pi : ℂ) ^ (-X.Q.s)) *
          (Complex.Gamma (X.A / 2) *
            Complex.Gamma (X.Q.s / 2) *
            Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2)) := by
      rw [hpow2]
      norm_num
    _ = (Real.pi : ℂ) ^ (-X.A / 2) * Complex.Gamma (X.A / 2) *
          ((Real.pi : ℂ) ^ (-X.Q.s / 2) * Complex.Gamma (X.Q.s / 2)) ^ 2 *
          ((Real.pi : ℂ) ^ (-X.w / 2) * Complex.Gamma (X.w / 2)) := by
      rw [hpowers']
      ring

/-- Literal nonconstant Whittaker source on the full strict unfolding chamber. -/
def actualUnfoldedScalarSource (X : D4BMStrictTripleUnfoldingParameters) : ℂ :=
  8 * reflectedCompletedLambda (2 * X.Q.s) *
    ((((2 * Real.pi : ℝ) : ℂ) ^ (-X.Q.s)) *
      (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (X.Q.s - 1) *
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x X.u *
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x X.u) *
      LSeries (d4BMDivisorProductArithmetic X.a X.a) X.w)

/-- Positive-half-plane completed-zeta product forced by the literal generic source. -/
def positiveLambdaProduct (X : D4BMStrictTripleUnfoldingParameters) : ℂ :=
  reflectedCompletedLambda X.A * reflectedCompletedLambda X.Q.s ^ 2 *
    reflectedCompletedLambda X.w

/-- Full-chamber evaluation of the literal nonconstant Whittaker source. -/
theorem actualUnfoldedScalarSource_eq_positiveLambdaProduct
    (X : D4BMStrictTripleUnfoldingParameters) :
    X.actualUnfoldedScalarSource = X.positiveLambdaProduct := by
  rw [actualUnfoldedScalarSource, positiveLambdaProduct,
    X.bessel_value_eq, X.ramanujan_value_eq]
  simp only [reflectedCompletedLambda]
  have hzeta : riemannZeta (2 * X.Q.s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp only [Complex.mul_re]
      norm_num
      linarith [X.Q.re_gt_one])
  let G : ℂ :=
    8 * Complex.Gammaℝ (2 * X.Q.s) *
      ((((2 * Real.pi : ℝ) : ℂ) ^ (-X.Q.s))) *
      ((2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
        (Complex.Gamma (X.A / 2) *
          Complex.Gamma (X.Q.s / 2) *
          Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2)))
  have hG : G = Complex.Gammaℝ X.A * Complex.Gammaℝ X.Q.s ^ 2 *
      Complex.Gammaℝ X.w := by
    exact X.archimedean_source_eq
  calc
    8 * (Complex.Gammaℝ (2 * X.Q.s) * riemannZeta (2 * X.Q.s)) *
        ((((2 * Real.pi : ℝ) : ℂ) ^ (-X.Q.s)) *
          ((2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
            (Complex.Gamma (X.A / 2) *
              Complex.Gamma (X.Q.s / 2) *
              Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2))) *
          (riemannZeta X.w * riemannZeta X.Q.s ^ 2 * riemannZeta X.A /
            riemannZeta (2 * X.Q.s))) =
      8 * (Complex.Gammaℝ (2 * X.Q.s) * riemannZeta (2 * X.Q.s)) *
          (((2 * Real.pi : ℝ) : ℂ) ^ (-X.Q.s)) *
          ((2 : ℂ) ^ (X.Q.s - 3) / Complex.Gamma X.Q.s *
            (Complex.Gamma (X.A / 2) *
              Complex.Gamma (X.Q.s / 2) *
              Complex.Gamma (X.Q.s / 2) * Complex.Gamma (X.w / 2))) *
          (riemannZeta X.w * riemannZeta X.Q.s ^ 2 * riemannZeta X.A /
            riemannZeta (2 * X.Q.s)) := by ring
    _ = G * riemannZeta (2 * X.Q.s) *
          (riemannZeta X.w * riemannZeta X.Q.s ^ 2 * riemannZeta X.A /
            riemannZeta (2 * X.Q.s)) := by
      dsimp [G]
      ring
    _ = G * (riemannZeta X.A * riemannZeta X.Q.s ^ 2 * riemannZeta X.w) := by
      field_simp [hzeta]
    _ = (Complex.Gammaℝ X.A * Complex.Gammaℝ X.Q.s ^ 2 *
          Complex.Gammaℝ X.w) *
        (riemannZeta X.A * riemannZeta X.Q.s ^ 2 * riemannZeta X.w) := by
      rw [hG]
    _ = (Complex.Gammaℝ X.A * riemannZeta X.A) *
          (Complex.Gammaℝ X.Q.s * riemannZeta X.Q.s) ^ 2 *
          (Complex.Gammaℝ X.w * riemannZeta X.w) := by
      ring

/-- In the right half-plane, one centered entire Xi channel is the completed-Lambda channel
multiplied by its forced half-Casimir pole-fill weight. -/
lemma completedXiFactor_centered_eq_poleFill_mul_lambda
    (s : ℂ) (hs : 1 < s.re) :
    thetaCuspHawkingCompletedEisensteinXiFactor (s - 1 / 2) =
      d4BMPoleFillCasimirWeight s * reflectedCompletedLambda s := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (s - 1 / 2)) * Complex.I = s := by
    apply Complex.ext <;> simp
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [harg, xi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_Gammaℝ_mul (by linarith [hs])]
  unfold d4BMPoleFillCasimirWeight reflectedCompletedLambda
  ring

/-- The negative fourth canonical channel is the functional-equation reflection of the positive
source channel. -/
lemma completedXiFactor_C_eq_w (X : D4BMStrictTripleUnfoldingParameters) :
    thetaCuspHawkingCompletedEisensteinXiFactor (X.C - 1 / 2) =
      thetaCuspHawkingCompletedEisensteinXiFactor (X.w - 1 / 2) := by
  rw [show X.C - 1 / 2 = -(X.w - 1 / 2) by
    simp only [C, w]
    ring, thetaCuspHawkingCompletedEisensteinXiFactor_neg]

/-- Full-chamber canonical four-Xi vertex is exactly the forced mixed-Casimir dressing of the
positive-half-plane source product. -/
theorem canonicalScalarVertex_eq_mixedCasimir_mul_positiveLambdaProduct
    (X : D4BMStrictTripleUnfoldingParameters) :
    d4BMActualCanonicalScalarTripleVertex X.P X.Q =
      d4BMMixedCasimirPoleFillMultiplier X.P.s X.Q.s * X.positiveLambdaProduct := by
  rw [d4BMActualCanonicalScalarTripleVertex,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization]
  simp only [d4BMActualCenteredEisensteinParameter]
  rw [show 2 * (X.P.s - 1 / 2) + (X.Q.s - 1 / 2) = X.A - 1 / 2 by
      simp only [A]
      ring,
    show 2 * (X.P.s - 1 / 2) - (X.Q.s - 1 / 2) = X.C - 1 / 2 by
      simp only [C]
      ring,
    X.completedXiFactor_C_eq_w,
    completedXiFactor_centered_eq_poleFill_mul_lambda X.A X.A_re_gt_one,
    completedXiFactor_centered_eq_poleFill_mul_lambda X.Q.s X.Q.re_gt_one,
    completedXiFactor_centered_eq_poleFill_mul_lambda X.w X.w_re_gt_one]
  have hweight : d4BMPoleFillCasimirWeight X.C = d4BMPoleFillCasimirWeight X.w := by
    simp only [d4BMPoleFillCasimirWeight, C, w]
    ring
  rw [d4BMMixedCasimirPoleFillMultiplier, positiveLambdaProduct,
    show 2 * X.P.s + X.Q.s - 1 = X.A by rfl,
    show 2 * X.P.s - X.Q.s = X.C by rfl,
    hweight]
  ring

/-- **Full-family corrected scalar landing.**  Source-derived rank-three mixed-Casimir dressing
of the literal generic unfolding equals the canonical entire four-Xi vertex. -/
theorem mixedCasimir_mul_actualUnfoldedScalarSource_eq_canonical
    (X : D4BMStrictTripleUnfoldingParameters) :
    d4BMMixedCasimirPoleFillMultiplier X.P.s X.Q.s * X.actualUnfoldedScalarSource =
      d4BMActualCanonicalScalarTripleVertex X.P X.Q := by
  rw [X.actualUnfoldedScalarSource_eq_positiveLambdaProduct]
  exact X.canonicalScalarVertex_eq_mixedCasimir_mul_positiveLambdaProduct.symm

/-- Full-family corrected source closes the boundary-free balanced C-A.9u landing. -/
theorem mixedCasimirCorrectedActualUnfoldedSource_balanced_eq_canonical
    (X : D4BMStrictTripleUnfoldingParameters) :
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (X.P.s * (X.P.s - 1)) (X.Q.s * (X.Q.s - 1)) *
        (d4BMMixedCasimirPoleFillMultiplier X.P.s X.Q.s *
          X.actualUnfoldedScalarSource) =
      d4BMActualCanonicalBalancedSpinTwoVertex X.P X.Q := by
  rw [X.mixedCasimir_mul_actualUnfoldedScalarSource_eq_canonical]
  exact (d4BM_actualCanonicalBalancedSpinTwoVertex_eq X.P X.Q).symm

/-- The former isolated calibration point belongs to the full strict chamber. -/
def twoFive : D4BMStrictTripleUnfoldingParameters where
  P := d4BMEisensteinAbsoluteConvergenceParameterTwo
  Q := d4BMEisensteinAbsoluteConvergenceParameterFive
  two_P_re_lt_Q_re := by
    norm_num [d4BMEisensteinAbsoluteConvergenceParameterTwo,
      d4BMEisensteinAbsoluteConvergenceParameterFive]

/-- Generic literal source specializes to the independently audited `(2,5)` source. -/
theorem actualUnfoldedScalarSource_twoFive_eq :
    twoFive.actualUnfoldedScalarSource = d4BMActualTwoFiveUnfoldedScalarSource := by
  norm_num [actualUnfoldedScalarSource, twoFive, u, a, w,
    d4BMActualTwoFiveUnfoldedScalarSource,
    d4BMEisensteinAbsoluteConvergenceParameterTwo,
    d4BMEisensteinAbsoluteConvergenceParameterFive]
  ring

end D4BMStrictTripleUnfoldingParameters

end RHTower
