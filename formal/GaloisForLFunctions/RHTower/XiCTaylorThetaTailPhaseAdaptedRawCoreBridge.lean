import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteArithmeticEndpoint
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetFiniteEdge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetTopRow

/-!
# Exact phase-adapted bookkeeping for the raw finite theta-tail core

This module records the exact identity that survives a factor-by-factor audit of the proposed
raw-to-reflected bridge.  Write `J_d(z)` for the raw finite-core current, `H_K` for the integrated
raw Haar prefix through depth `K`, and `T_K` for its dyadic top row.  The existing polarization is

```text
J_d(z) = 1/4 (H_K(d,z) + T_K(d,z)).
```

For `c_j = P_j q^j` and `P(q)=1`, coefficient weighting therefore gives the paper identity

```text
J_d(z) = 1/4 (sum_j c_j H_(N+j)(d,z) + sum_j c_j T_(N+j)(d,z)).       (1)
```

Let `I_fin` be the same reflected Haar source paired with the finite core kernel and let `I_inf`
be the existing untruncated phase current.  There are two distinct changes between the first term
of `(1)` and `I_inf`:

```text
Delta_refl = sum_j c_j H_(N+j) - I_fin,
Delta_ker  = I_fin - I_inf.
```

Consequently the exact corrected bridge is

```text
J_d(z) = 1/4 I_inf + 1/4 sum_j c_j T_(N+j)
           + 1/4 Delta_refl + 1/4 Delta_ker.                            (2)
```

The hoped-for two-term identity is equivalent to `Delta_refl + Delta_ker = 0`; normalization at
`q` alone does not prove that equation.  In particular, the finite Prouhet lemmas cancel the
positive affine phase value and derivative, and the negative channel below is obtained by exact
reflection with its derivative chain-rule sign.  Those are linear Hermitian-cross cancellations;
they do not silently identify the two integrated kernels in `(2)`.

The theta-tail core uses phase depth `d+1`, so the exact linear cancellation hypothesis is
`2 * (d + 1) < m`.  No self-consistent endpoint and no Xi-zero information occur here.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## The reflected negative finite phase -/

/-- Value cancellation in the negative finite phase.  It is the positive cancellation at `-z`;
there is no additional hypothesis or unrecorded phase convention. -/
theorem phaseAdaptedProuhet_finiteNegativePhaseAffineDepthValue_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  have h := phaseAdaptedProuhet_finitePositivePhaseAffineDepthValue_sum_eq_zero
    d m N u q r tau a L (-z) hm
  dsimp only at h
  change ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (finiteNegativePhasePolynomial d
        (a + ((N + j : ℕ) : ℝ) * L)).eval z = 0
  rw [show (∑ j ∈ P.support, (P.coeff j : ℂ) *
      (finiteNegativePhasePolynomial d
        (a + ((N + j : ℕ) : ℝ) * L)).eval z) =
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval (-z) by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteNegativePhasePolynomial_eval_eq_positive_eval_neg]]
  exact h

/-- Derivative cancellation in the negative finite phase.  The minus sign is exactly the chain
rule for composition with `-X`. -/
theorem phaseAdaptedProuhet_finiteNegativePhaseAffineDepthDerivative_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  have h := phaseAdaptedProuhet_finitePositivePhaseAffineDepthDerivative_sum_eq_zero
    d m N u q r tau a L (-z) hm
  dsimp only at h
  change ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (finiteNegativePhasePolynomial d
        (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z = 0
  rw [show (∑ j ∈ P.support, (P.coeff j : ℂ) *
      (finiteNegativePhasePolynomial d
        (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z) =
      -(∑ j ∈ P.support, (P.coeff j : ℂ) *
        (finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval (-z)) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteNegativePhasePolynomial_derivative_eval_eq_neg_positive_derivative_eval_neg]
    ring]
  rw [h, neg_zero]

/-- Hermitian-cross cancellation in the negative finite phase.  Reflection changes `D` to `-D`
and hence transports the positive theorem with seam derivative `-E'`; the outer sign then
vanishes with the positive sum. -/
theorem phaseAdaptedProuhet_finiteNegativePhaseAffineDepthHermitianCross_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z E E' : ℂ)
    (hm : 2 * d < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E' = 0 := by
  dsimp only
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  have h :=
    phaseAdaptedProuhet_finitePositivePhaseAffineDepthHermitianCross_sum_eq_zero
      d m N u q r tau a L (-z) E (-E') hm
  dsimp only at h
  change ∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E' = 0
  rw [show (∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finiteNegativePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E') =
      -(∑ j ∈ P.support, P.coeff j *
        symmetricHermitianCrossCurrentData
          ((finitePositivePhasePolynomial d
            (a + ((N + j : ℕ) : ℝ) * L)).eval (-z))
          ((finitePositivePhasePolynomial d
            (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval (-z))
          E (-E')) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteNegativePhasePolynomial_eval_eq_positive_eval_neg,
      finiteNegativePhasePolynomial_derivative_eval_eq_neg_positive_derivative_eval_neg]
    unfold symmetricHermitianCrossCurrentData
    rw [show
      -(finitePositivePhasePolynomial d
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval (-z) *
            (starRingEnd ℂ) E +
          E' * (starRingEnd ℂ)
            ((finitePositivePhasePolynomial d
              (a + ((N + j : ℕ) : ℝ) * L)).eval (-z)) =
        -((finitePositivePhasePolynomial d
            (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval (-z) *
              (starRingEnd ℂ) E -
            E' * (starRingEnd ℂ)
              ((finitePositivePhasePolynomial d
                (a + ((N + j : ℕ) : ℝ) * L)).eval (-z))) by ring]
    simp
    ring]
  rw [h, neg_zero]

/-- Both finite phase channels attached to the theta-tail core cancel against a fixed seam under
the shifted and sharp linear-degree hypothesis `2 * (d + 1) < m`. -/
theorem phaseAdaptedProuhet_coreShiftedTwoPhaseHermitianCross_sum_eq_zero
    (d m N : ℕ) (u : ℂ) (q r tau a L : ℝ) (z E E' : ℂ)
    (hm : 2 * (d + 1) < m) :
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    (∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finitePositivePhasePolynomial (d + 1)
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finitePositivePhasePolynomial (d + 1)
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E' = 0) ∧
    (∑ j ∈ P.support, P.coeff j *
      symmetricHermitianCrossCurrentData
        ((finiteNegativePhasePolynomial (d + 1)
          (a + ((N + j : ℕ) : ℝ) * L)).eval z)
        ((finiteNegativePhasePolynomial (d + 1)
          (a + ((N + j : ℕ) : ℝ) * L)).derivative.eval z)
        E E' = 0) := by
  dsimp only
  constructor
  · exact phaseAdaptedProuhet_finitePositivePhaseAffineDepthHermitianCross_sum_eq_zero
      (d + 1) m N u q r tau a L z E E' hm
  · exact phaseAdaptedProuhet_finiteNegativePhaseAffineDepthHermitianCross_sum_eq_zero
      (d + 1) m N u q r tau a L z E E' hm

/-! ## Normalized raw Haar packet -/

/-- The complete raw Haar integral at one finite depth, before separating its sole top row. -/
def xiCTaylorThetaTailCoreRawHaarTotalIntegratedCurrent
    (d : ℕ) (z : ℂ) (K : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ,
    ((∑ k ∈ Finset.range K,
        xiCTaylorThetaTailCoreDyadicHaarLayerKernel d z k p) +
      xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z K p)
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- The integrated raw Haar prefix.  Scalar subtraction keeps the top row exact without invoking
a second integral-distribution theorem. -/
def xiCTaylorThetaTailCoreRawHaarPrefixIntegratedCurrent
    (d : ℕ) (z : ℂ) (K : ℕ) : ℝ :=
  xiCTaylorThetaTailCoreRawHaarTotalIntegratedCurrent d z K -
    xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent d z K

/-- The coefficient-weighted raw prefixes at the phase-adapted depths `N+j`. -/
def phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent
    (P : ℝ[X]) (q : ℝ) (N d : ℕ) (z : ℂ) : ℝ :=
  P.sum fun j c =>
    (c * q ^ j) *
      xiCTaylorThetaTailCoreRawHaarPrefixIntegratedCurrent d z (N + j)

/-- The coefficient-weighted dyadic top rows.  The coefficient is exactly
`c_j = P_j q^j`; no extra factor `2`, `1/2`, or `1/4` is absorbed here. -/
def phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
    (P : ℝ[X]) (q : ℝ) (N d : ℕ) (z : ℂ) : ℝ :=
  P.sum fun j c =>
    (c * q ^ j) *
      xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent d z (N + j)

/-- The existing complex top-row pairing is the real weighted current above, embedded in `ℂ`. -/
theorem phaseAdaptedProuhetWeightedTopRowCurrent_eq_ofReal
    (P : ℝ[X]) (q : ℝ) (N d : ℕ) (z : ℂ) :
    phaseAdaptedProuhetWeightedTopRowCurrent P q N d z =
      (phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent P q N d z : ℂ) := by
  unfold phaseAdaptedProuhetWeightedTopRowCurrent
    realPolynomialComplexCoefficientPairing
    phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent Polynomial.sum
  push_cast
  congr 1
  funext j
  ring

/-- Coefficient weighting preserves exactly one raw current when `P(q)=1`.  This is equation
`(1)` in the module note and fixes the global factor `1/4`. -/
theorem xiCTaylorThetaTailCore_current_eq_weightedRawHaarPrefix_add_topRows
    (P : ℝ[X]) (q : ℝ) (N d : ℕ) (z : ℂ)
    (hq : P.eval q = 1) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        (phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent P q N d z +
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent P q N d z) := by
  have hmass : ∑ j ∈ P.support, P.coeff j * q ^ j = 1 := by
    rw [← hq, eval_eq_sum, Polynomial.sum]
  have htotal (j : ℕ) :
      orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
        (1 / 4 : ℝ) *
          xiCTaylorThetaTailCoreRawHaarTotalIntegratedCurrent d z (N + j) := by
    simpa only [xiCTaylorThetaTailCoreRawHaarTotalIntegratedCurrent] using
      xiCTaylorThetaTailCore_current_eq_dyadicHaarPolarization d z (N + j)
  calc
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
        (∑ j ∈ P.support, P.coeff j * q ^ j) *
          orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z := by
      rw [hmass, one_mul]
    _ = ∑ j ∈ P.support, (P.coeff j * q ^ j) *
        orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z := by
      rw [Finset.sum_mul]
    _ = ∑ j ∈ P.support, (P.coeff j * q ^ j) *
        ((1 / 4 : ℝ) *
          xiCTaylorThetaTailCoreRawHaarTotalIntegratedCurrent d z (N + j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [htotal]
    _ = (1 / 4 : ℝ) *
        (phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent P q N d z +
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent P q N d z) := by
      unfold phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent
        phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent Polynomial.sum
        xiCTaylorThetaTailCoreRawHaarPrefixIntegratedCurrent
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-! ## The two surviving changes of current -/

/-- The reflected phase-adapted source paired with the finite theta-tail core kernel. -/
def phaseAdaptedFiniteCoreReflectedHaarIntegratedCurrentAtEndpoint
    (d m N : ℕ) (z : ℂ) (tau : ℝ) : ℝ :=
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  ∫ p : ℝ × ℝ,
    phaseAdaptedWeightedReflectedHaarPrefixSource
        P dyadicProuhetDecayCharacter N p *
      xiCTaylorThetaTailCorePairCurrent d z p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- Exact current left when the coefficient-weighted raw prefix is transported to the reflected
finite-core prefix.  No assertion that this fixed-half-line translation current vanishes is built
into its definition. -/
def phaseAdaptedRawCoreReflectionTranslationCurrent
    (d m N : ℕ) (z : ℂ) (tau : ℝ) : ℝ :=
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent
      P dyadicProuhetDecayCharacter N d z -
    phaseAdaptedFiniteCoreReflectedHaarIntegratedCurrentAtEndpoint d m N z tau

/-- Exact current left when the finite core kernel on the reflected prefix is replaced by the
untruncated spectral phase kernel.  This is a finite-to-untruncated kernel defect, not a dyadic top
row. -/
def phaseAdaptedRawCoreFiniteToUntruncatedCurrent
    (d m N : ℕ) (z : ℂ) (tau : ℝ) : ℝ :=
  phaseAdaptedFiniteCoreReflectedHaarIntegratedCurrentAtEndpoint d m N z tau -
    phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau

/-- The complete surviving finite-translation current is the sum of the reflection-transport and
finite-to-untruncated defects. -/
def phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent
    (d m N : ℕ) (z : ℂ) (tau : ℝ) : ℝ :=
  phaseAdaptedRawCoreReflectionTranslationCurrent d m N z tau +
    phaseAdaptedRawCoreFiniteToUntruncatedCurrent d m N z tau

theorem phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent_eq
    (d m N : ℕ) (z : ℂ) (tau : ℝ) :
    phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent d m N z tau =
      phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent
          (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau)
          dyadicProuhetDecayCharacter N d z -
        phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau := by
  unfold phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent
    phaseAdaptedRawCoreReflectionTranslationCurrent
    phaseAdaptedRawCoreFiniteToUntruncatedCurrent
  dsimp only
  ring

/-! ## Corrected raw-to-untruncated bridge -/

/-- **Exact corrected bridge, fully displayed.**  The endpoint `tau` is arbitrary.  The raw
current is one quarter of the untruncated reflected-prefix current, one quarter of the
coefficient-weighted top rows, and one quarter of each of the two current changes above. -/
theorem xiCTaylorThetaTailCore_current_eq_phaseAdaptedReflected_add_topRows_add_defects
    (d m N : ℕ) {z : ℂ} (hzHalf : z.im < 1 / 2) (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
          phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
            P dyadicProuhetDecayCharacter N d z +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreReflectionTranslationCurrent d m N z tau +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreFiniteToUntruncatedCurrent d m N z tau := by
  dsimp only
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  have hq : P.eval dyadicProuhetDecayCharacter = 1 := by
    exact canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay m hzHalf tau
  have hraw :=
    xiCTaylorThetaTailCore_current_eq_weightedRawHaarPrefix_add_topRows
      P dyadicProuhetDecayCharacter N d z hq
  calc
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
        (1 / 4 : ℝ) *
          (phaseAdaptedRawCoreWeightedHaarPrefixIntegratedCurrent
              P dyadicProuhetDecayCharacter N d z +
            phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
              P dyadicProuhetDecayCharacter N d z) := hraw
    _ = _ := by
      unfold phaseAdaptedRawCoreReflectionTranslationCurrent
        phaseAdaptedRawCoreFiniteToUntruncatedCurrent
      dsimp only [P]
      ring

/-- Three-term form of the corrected bridge, with the two exact defects collected but not erased. -/
theorem xiCTaylorThetaTailCore_current_eq_phaseAdaptedReflected_add_topRows_add_survivor
    (d m N : ℕ) {z : ℂ} (hzHalf : z.im < 1 / 2) (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
          phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
            P dyadicProuhetDecayCharacter N d z +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent d m N z tau := by
  dsimp only
  rw [xiCTaylorThetaTailCore_current_eq_phaseAdaptedReflected_add_topRows_add_defects
    d m N hzHalf tau]
  unfold phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent
  ring

/-- The untruncated prefix is one half of the returned-source current, so its coefficient in the
raw bridge is `1/8`.  The endpoint remains arbitrary. -/
theorem xiCTaylorThetaTailCore_current_eq_returnedSource_add_topRows_add_survivor
    (d m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 8 : ℝ) *
          phaseAdaptedCriticalReturnedSourceCurrent m N
            (spectralTranslationPhase (Real.log 2) z)
            dyadicProuhetGrowthCharacter tau z
            (thetaCuspTailSecondDensityPhaseValue z)
            (thetaCuspTailSecondDensityPhaseDerivative z)
            (thetaHalfExponentialPhaseValue z)
            (thetaHalfExponentialPhaseDerivative z) +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
            P dyadicProuhetDecayCharacter N d z +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent d m N z tau := by
  dsimp only
  rw [xiCTaylorThetaTailCore_current_eq_phaseAdaptedReflected_add_topRows_add_survivor
    d m N hzHalf tau,
    phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint_eq
      m N hz0 hzHalf tau]
  ring

/-- The proposed two-term identity is valid exactly when the displayed surviving translation
current vanishes.  Neither `P(q)=1` nor the two finite phase cross cancellations prove this extra
equation. -/
theorem xiCTaylorThetaTailCore_twoTermBridge_iff_survivingTranslation_eq_zero
    (d m N : ℕ) {z : ℂ} (hzHalf : z.im < 1 / 2) (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    (orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
          phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau +
        (1 / 4 : ℝ) *
          phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
            P dyadicProuhetDecayCharacter N d z) ↔
      phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent d m N z tau = 0 := by
  dsimp only
  have hcorrected :=
    xiCTaylorThetaTailCore_current_eq_phaseAdaptedReflected_add_topRows_add_survivor
      d m N hzHalf tau
  dsimp only at hcorrected
  constructor <;> intro h <;> linarith

end

end RHTower
