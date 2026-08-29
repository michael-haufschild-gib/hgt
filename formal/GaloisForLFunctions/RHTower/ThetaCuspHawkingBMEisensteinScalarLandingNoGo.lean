import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualBalancedSpinTwoCoefficientExtraction

/-!
# Scalar-landing necessity after actual balanced Eisenstein coefficient extraction

C-A.9u proves the literal finite-height identity

```text
balanced - B * scalar = secondCusp + (d+1) * firstCusp.
```

It does not evaluate the scalar triple moment.  This module closes a hostile audit of the tempting
shortcut from zero cusp finite parts directly to the canonical four-Xi balanced vertex.

Every complex-linear finite-part reporter preserves C-A.9u.  Subtracting the canonical Stokes
completion gives the exact residual law

```text
balancedCanonicalResidual = B * scalarCanonicalResidual + cuspResidual.
```

Consequently, on every boundary-free source with `B != 0`, canonical balanced landing is equivalent
to the missing scalar Rankin--Selberg--Zagier landing.  An explicit boundary-free extraction datum
at the actual chamber point `s=t=2` proves that the extraction law itself does not force landing.

There is also a genuine normalization obstruction.  The classical completed RSZ value for the
diagonal triple is a product of four meromorphic `Lambda` factors.  The corpus canonical vertex is
the pole-filled product of four `xi(w)=w(w-1)Lambda(w)/2` factors.  At `s=t=2`, Lean proves

```text
canonicalXiVertex = 10 * classicalCompletedLambdaRSZValue,
```

and proves the Lambda value nonzero.  Thus direct equality is false even away from every pole; the
elementary pole-fill factor cannot be silently discarded.

This kills the direct route

```text
C-A.9u + zero cusp finite parts -> canonical balanced ++- vertex.
```

The strongest positive survivor is exact: HB can continue only through a genuine pole-filled scalar
RSZ theorem, followed by C-A.9u, the negative BM leg, conserved left-QNM projection, HC94
source/clock factorization, and the horizon-boundary relative cocycle.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [NO-GO] [HB] [HC94]`
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Heights of the literal truncated modular domains used by C-A.9u. -/
abbrev D4BMActualTruncationHeight := {Y : ℝ // 1 ≤ Y}

/-- Any complex-linear finite-part reporter on literal height-dependent moments. -/
abbrev D4BMActualHeightFinitePart :=
  (D4BMActualTruncationHeight → ℂ) →ₗ[ℂ] ℂ

/-- Reported finite part of the literal scalar triple moment. -/
def d4BMActualScalarTripleFinitePart
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  finitePart fun Y => d4BMActualScalarTripleTruncatedMoment P Q Y

/-- Reported finite part of the literal balanced spin-two moment. -/
def d4BMActualBalancedSpinTwoFinitePart
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  finitePart fun Y => d4BMActualBalancedSpinTwoTruncatedMoment P Q Y

/-- Reported finite part of the literal first paired cusp-top current. -/
def d4BMActualFirstStokesCuspFinitePart
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  finitePart fun Y => d4BMActualFirstStokesPairedCuspTop P Q Y

/-- Reported finite part of the literal second paired cusp-top current. -/
def d4BMActualSecondStokesCuspFinitePart
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  finitePart fun Y => d4BMActualSecondStokesPairedCuspTop P Q Y

/-- Every complex-linear finite-part reporter preserves the literal C-A.9u extraction law. -/
theorem d4BM_actualFinitePart_extraction
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualBalancedSpinTwoFinitePart finitePart P Q -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
          d4BMActualScalarTripleFinitePart finitePart P Q =
      d4BMActualSecondStokesCuspFinitePart finitePart P Q +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
          d4BMActualFirstStokesCuspFinitePart finitePart P Q := by
  let b := d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
  let d := d4BMHyperbolicDiagonalGradientShift
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
  have hfun :
      (fun Y : D4BMActualTruncationHeight =>
          d4BMActualBalancedSpinTwoTruncatedMoment P Q Y) -
          b • (fun Y : D4BMActualTruncationHeight =>
            d4BMActualScalarTripleTruncatedMoment P Q Y) =
        (fun Y : D4BMActualTruncationHeight =>
          d4BMActualSecondStokesPairedCuspTop P Q Y) +
          (d + 1) • (fun Y : D4BMActualTruncationHeight =>
            d4BMActualFirstStokesPairedCuspTop P Q Y) := by
    funext Y
    simpa [b, d, smul_eq_mul] using
      d4BM_actualBalancedSpinTwoTruncatedMoment_eq_pairedCuspTop P Q Y
  have hmap := congrArg (fun f : D4BMActualTruncationHeight → ℂ => finitePart f) hfun
  simpa [d4BMActualBalancedSpinTwoFinitePart,
    d4BMActualScalarTripleFinitePart, d4BMActualFirstStokesCuspFinitePart,
    d4BMActualSecondStokesCuspFinitePart, b, d, smul_eq_mul] using hmap

/-- Centered spectral parameter `u=s-1/2` of one actual Poincare leg. -/
def d4BMActualCenteredEisensteinParameter
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ := P.s - 1 / 2

/-- Centering converts the geometric eigenvalue back to the actual `s(s-1)` convention. -/
theorem thetaCuspHawkingEisensteinGeometricEigenvalue_centered (s : ℂ) :
    thetaCuspHawkingEisensteinGeometricEigenvalue (s - 1 / 2) = s * (s - 1) := by
  simp [thetaCuspHawkingEisensteinGeometricEigenvalue]
  ring

/-- Canonical pole-filled scalar vertex at the parameters of two actual Poincare legs. -/
def d4BMActualCanonicalScalarTripleVertex
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex
    (d4BMActualCenteredEisensteinParameter P)
    (d4BMActualCenteredEisensteinParameter Q)

/-- Canonical pole-filled balanced spin-two vertex at the actual parameters. -/
def d4BMActualCanonicalBalancedSpinTwoVertex
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
    (d4BMActualCenteredEisensteinParameter P)
    (d4BMActualCenteredEisensteinParameter Q)

/-- The canonical balanced vertex uses the same literal Bochner coefficient as C-A.9u. -/
theorem d4BM_actualCanonicalBalancedSpinTwoVertex_eq
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCanonicalBalancedSpinTwoVertex P Q =
      d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
        d4BMActualCanonicalScalarTripleVertex P Q := by
  rw [d4BMActualCanonicalBalancedSpinTwoVertex,
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq]
  simp only [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient,
    d4BMActualCenteredEisensteinParameter, d4BMActualCanonicalScalarTripleVertex,
    thetaCuspHawkingEisensteinGeometricEigenvalue_centered]

/-- Failure of the actual scalar finite part to land on the canonical pole-filled vertex. -/
def d4BMActualScalarCanonicalLandingResidual
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualScalarTripleFinitePart finitePart P Q -
    d4BMActualCanonicalScalarTripleVertex P Q

/-- Failure of the actual balanced finite part to land on the canonical balanced vertex. -/
def d4BMActualBalancedCanonicalLandingResidual
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualBalancedSpinTwoFinitePart finitePart P Q -
    d4BMActualCanonicalBalancedSpinTwoVertex P Q

/-- Complete first-plus-second cusp finite-part residual. -/
def d4BMActualCuspFinitePartResidual
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualSecondStokesCuspFinitePart finitePart P Q +
    (d4BMHyperbolicDiagonalGradientShift
      (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) *
      d4BMActualFirstStokesCuspFinitePart finitePart P Q

/-- **C-A.9v survivor.** After every tensor and boundary reduction, the balanced canonical-landing
error is exactly the scalar RSZ error multiplied by the Bochner coefficient, plus the complete
cusp finite-part error. -/
theorem d4BM_actualBalancedCanonicalLandingResidual_eq
    (finitePart : D4BMActualHeightFinitePart)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualBalancedCanonicalLandingResidual finitePart P Q =
      d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) *
        d4BMActualScalarCanonicalLandingResidual finitePart P Q +
      d4BMActualCuspFinitePartResidual finitePart P Q := by
  have hextract := d4BM_actualFinitePart_extraction finitePart P Q
  have hcanonical := d4BM_actualCanonicalBalancedSpinTwoVertex_eq P Q
  unfold d4BMActualBalancedCanonicalLandingResidual
    d4BMActualScalarCanonicalLandingResidual d4BMActualCuspFinitePartResidual
  rw [hcanonical]
  linear_combination hextract

/-- Abstract finite-part values satisfying exactly the literal C-A.9u extraction law. -/
structure D4BMFinitePartExtractionData
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) where
  scalarFinitePart : ℂ
  balancedFinitePart : ℂ
  firstCuspFinitePart : ℂ
  secondCuspFinitePart : ℂ
  extraction :
    balancedFinitePart -
        d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) * scalarFinitePart =
      secondCuspFinitePart +
        (d4BMHyperbolicDiagonalGradientShift
          (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) + 1) * firstCuspFinitePart

/-- Boundary-free extraction data at which the Bochner source multiplier is nonzero. -/
def D4BMNondegenerateBoundaryFreeExtractionData
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :=
  {D : D4BMFinitePartExtractionData P Q //
    D.firstCuspFinitePart = 0 ∧ D.secondCuspFinitePart = 0 ∧
      d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
        (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) ≠ 0}

/-- **C-A.9v positive survivor.** On every boundary-free nondegenerate source, canonical balanced
landing is equivalent to the missing canonical scalar RSZ landing. -/
theorem d4BM_boundaryFreeCanonicalBalancedLanding_iff_scalarLanding
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (D : D4BMNondegenerateBoundaryFreeExtractionData P Q) :
    D.1.balancedFinitePart = d4BMActualCanonicalBalancedSpinTwoVertex P Q ↔
      D.1.scalarFinitePart = d4BMActualCanonicalScalarTripleVertex P Q := by
  rcases D.2 with ⟨hfirst, hsecond, hb⟩
  have hextract := D.1.extraction
  rw [hfirst, hsecond] at hextract
  simp only [mul_zero, zero_add] at hextract
  have hcanonical := d4BM_actualCanonicalBalancedSpinTwoVertex_eq P Q
  let b := d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
  have hextract' : D.1.balancedFinitePart = b * D.1.scalarFinitePart := by
    dsimp [b]
    linear_combination hextract
  constructor
  · intro hbalanced
    have hmul : b * D.1.scalarFinitePart =
        b * d4BMActualCanonicalScalarTripleVertex P Q := by
      rw [← hextract', hbalanced, hcanonical]
    exact mul_left_cancel₀ hb hmul
  · intro hscalar
    rw [hextract', hscalar]
    exact hcanonical.symm

/-- Actual linear reporters with zero first/second cusp values and nonzero source multiplier. -/
def D4BMNondegenerateBoundaryFreeActualFinitePart
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :=
  {finitePart : D4BMActualHeightFinitePart //
    d4BMActualFirstStokesCuspFinitePart finitePart P Q = 0 ∧
      d4BMActualSecondStokesCuspFinitePart finitePart P Q = 0 ∧
      d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
        (P.s * (P.s - 1)) (Q.s * (Q.s - 1)) ≠ 0}

/-- Route-level necessity for the literal moments: after actual cusp annihilation, balanced landing
occurs exactly when the actual scalar finite part satisfies the pole-filled RSZ identity. -/
theorem d4BM_actualBoundaryFreeCanonicalBalancedLanding_iff_scalarRSZ
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (A : D4BMNondegenerateBoundaryFreeActualFinitePart P Q) :
    d4BMActualBalancedSpinTwoFinitePart A.1 P Q =
        d4BMActualCanonicalBalancedSpinTwoVertex P Q ↔
      d4BMActualScalarTripleFinitePart A.1 P Q =
        d4BMActualCanonicalScalarTripleVertex P Q := by
  let D : D4BMFinitePartExtractionData P Q :=
    { scalarFinitePart := d4BMActualScalarTripleFinitePart A.1 P Q
      balancedFinitePart := d4BMActualBalancedSpinTwoFinitePart A.1 P Q
      firstCuspFinitePart := d4BMActualFirstStokesCuspFinitePart A.1 P Q
      secondCuspFinitePart := d4BMActualSecondStokesCuspFinitePart A.1 P Q
      extraction := d4BM_actualFinitePart_extraction A.1 P Q }
  let B : D4BMNondegenerateBoundaryFreeExtractionData P Q :=
    ⟨D, A.2⟩
  exact d4BM_boundaryFreeCanonicalBalancedLanding_iff_scalarLanding P Q B

/-- Explicit point `s=2` in the actual Eisenstein absolute-convergence chamber. -/
def d4BMEisensteinAbsoluteConvergenceParameterTwo :
    D4BMEisensteinAbsoluteConvergenceParameter :=
  ⟨2, by norm_num⟩

/-- The literal balanced Bochner source is nondegenerate at `s=t=2`. -/
theorem d4BM_bochnerCoefficient_at_two_eq_neg_four :
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
      (d4BMEisensteinAbsoluteConvergenceParameterTwo.s *
        (d4BMEisensteinAbsoluteConvergenceParameterTwo.s - 1))
      (d4BMEisensteinAbsoluteConvergenceParameterTwo.s *
        (d4BMEisensteinAbsoluteConvergenceParameterTwo.s - 1)) = -4 := by
  norm_num [d4BMEisensteinAbsoluteConvergenceParameterTwo,
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicDiagonalGradientShift]

/-- Boundary-free extraction witness with a unit scalar residual at `s=t=2`. -/
def d4BMDirectScalarLandingNoGoData :
    D4BMFinitePartExtractionData
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterTwo where
  scalarFinitePart :=
    d4BMActualCanonicalScalarTripleVertex
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterTwo + 1
  balancedFinitePart :=
    d4BMActualCanonicalBalancedSpinTwoVertex
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterTwo - 4
  firstCuspFinitePart := 0
  secondCuspFinitePart := 0
  extraction := by
    rw [d4BM_bochnerCoefficient_at_two_eq_neg_four,
      d4BM_actualCanonicalBalancedSpinTwoVertex_eq,
      d4BM_bochnerCoefficient_at_two_eq_neg_four]
    norm_num
    ring

/-- **Logical route kill.** C-A.9u's extraction law plus zero cusp finite parts does not force the
canonical balanced vertex, even with actual absolute-convergence parameters. -/
theorem d4BM_directScalarLanding_from_zeroCusp_not_forced :
    ∃ D : D4BMFinitePartExtractionData
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo,
      D.firstCuspFinitePart = 0 ∧ D.secondCuspFinitePart = 0 ∧
        D.balancedFinitePart ≠
          d4BMActualCanonicalBalancedSpinTwoVertex
            d4BMEisensteinAbsoluteConvergenceParameterTwo
            d4BMEisensteinAbsoluteConvergenceParameterTwo := by
  refine ⟨d4BMDirectScalarLandingNoGoData, rfl, rfl, ?_⟩
  simp [d4BMDirectScalarLandingNoGoData]

/-- Classical diagonal completed-Eisenstein RSZ numerator in actual `s,t` coordinates. -/
def d4BMClassicalCompletedDiagonalRSZValue
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s + Q.s - 1) *
    reflectedCompletedLambda Q.s ^ 2 *
    reflectedCompletedLambda (2 * P.s - Q.s)

private theorem d4BM_completedXiFactor_nine_halves_eq :
    thetaCuspHawkingCompletedEisensteinXiFactor (9 / 2 : ℂ) =
      10 * reflectedCompletedLambda 5 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (9 / 2 : ℂ)) * Complex.I = 5 := by
    apply Complex.ext <;> norm_num
  rw [harg, xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    completedRiemannZeta_eq_Gammaℝ_mul (by norm_num)]
  unfold reflectedCompletedLambda
  ring

private theorem d4BM_completedXiFactor_three_halves_eq :
    thetaCuspHawkingCompletedEisensteinXiFactor (3 / 2 : ℂ) =
      reflectedCompletedLambda 2 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (3 / 2 : ℂ)) * Complex.I = 2 := by
    apply Complex.ext <;> norm_num
  rw [harg, xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    completedRiemannZeta_eq_Gammaℝ_mul (by norm_num)]
  unfold reflectedCompletedLambda
  ring

/-- At the regular chamber point `s=t=2`, pole filling multiplies the classical completed-Lambda
RSZ value by exactly ten. -/
theorem d4BM_canonicalScalarVertex_eq_ten_mul_classicalRSZ_at_two :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo =
      10 * d4BMClassicalCompletedDiagonalRSZValue
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo := by
  rw [d4BMActualCanonicalScalarTripleVertex,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization]
  norm_num [d4BMActualCenteredEisensteinParameter,
    d4BMEisensteinAbsoluteConvergenceParameterTwo]
  rw [d4BM_completedXiFactor_nine_halves_eq,
    d4BM_completedXiFactor_three_halves_eq]
  norm_num [d4BMClassicalCompletedDiagonalRSZValue,
    d4BMEisensteinAbsoluteConvergenceParameterTwo]
  ring

/-- The classical completed-Lambda RSZ value at `s=t=2` is nonzero. -/
theorem d4BM_classicalCompletedDiagonalRSZValue_at_two_ne_zero :
    d4BMClassicalCompletedDiagonalRSZValue
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterTwo ≠ 0 := by
  have hLambda (s : ℂ) (hs : 1 < s.re) : reflectedCompletedLambda s ≠ 0 := by
    unfold reflectedCompletedLambda
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
      (riemannZeta_ne_zero_of_one_lt_re hs)
  norm_num [d4BMClassicalCompletedDiagonalRSZValue,
    d4BMEisensteinAbsoluteConvergenceParameterTwo]
  exact ⟨hLambda 5 (by norm_num), hLambda 2 (by norm_num)⟩

/-- **Exact normalization no-go.** The pole-filled four-Xi canonical vertex is not the classical
completed-Lambda RSZ value even at a regular absolute-convergence point. -/
theorem d4BM_canonicalScalarVertex_ne_classicalCompletedRSZ_at_two :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo ≠
      d4BMClassicalCompletedDiagonalRSZValue
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo := by
  rw [d4BM_canonicalScalarVertex_eq_ten_mul_classicalRSZ_at_two]
  intro h
  have hzero :
      d4BMClassicalCompletedDiagonalRSZValue
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterTwo = 0 := by
    linear_combination (1 / 9 : ℂ) * h
  exact d4BM_classicalCompletedDiagonalRSZValue_at_two_ne_zero hzero

end RHTower
