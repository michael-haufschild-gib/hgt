# Boundary-everywhere Helson continuation seam and universal HT field type — formalized

- **ID:** `helson-universal-ht-arbitrary-divisor-orthogonality-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `helson-universal-ht-arbitrary-divisor-orthogonality.md`
- **Type:** FORMALIZATION CERTIFICATE

Every statement of the card is a Lean theorem in this tree, unconditionally: no `sorry`, no added
axiom, no unproved analytic input.  All capstones below were checked with `#print axioms` and depend
only on `propext, Classical.choice, Quot.sound`.

## The card's three claims and their Lean witnesses

### 1. Universal labelled differential-field type

```text
GaloisForLFunctions/HTGeometry/HelsonZetaJetIndependence.lean
    algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeCoefficientField
    algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeRationalCoefficientField
    algebraicIndependent_helsonZetaShiftedUpperEndGerms
GaloisForLFunctions/HTGeometry/HelsonZetaShiftedJetIndependence.lean
    helsonLabelledAlgEquiv, helsonLabelledAlgEquiv_jet
GaloisForLFunctions/HTGeometry/DifferentialIndependentFieldUniversality.lean
    differentialIndependentAdjoinAlgEquiv_unique, differentialIndependentAdjoinAlgEquiv_unique_of_jet
GaloisForLFunctions/HTGeometry/PrimeValueJacobianCoefficientField.lean
    algebraicIndependent_over_finitePrimeCoefficientField_of_tailIndependent
```

Every finite family of distinct shifted derivatives of `Z_chi` is algebraically independent over the
finite-prime coefficient field, for every unimodular phase; the labelled isomorphism `Phi_(chi,psi)`
exists, carries jets to jets, and is unique.

### 2. Arbitrary continued divisor (Andersson's Theorem 5 for `U = C`)

```text
GaloisForLFunctions/RHTower/Sieve/CharacterStacking.lean
    exists_andersson_character                     Lemma 7 for the full remainder chain
GaloisForLFunctions/RHTower/AnderssonTheoremOne.lean
    exists_character_entire_remainder              Theorem 1
GaloisForLFunctions/HTGeometry/HelsonCharacterLSeries.lean
    helsonZetaValue_eq_LSeries, logDeriv_helsonZetaValue
GaloisForLFunctions/RHTower/AnderssonTheoremTwo.lean
    helson_factorization_of_mellin_logDeriv        Theorem 2
    helson_factorization_divisorFunction
    exists_continuable_phase_of_mellin_logDeriv
    exists_continuable_phase_with_prescribed_divisor
    exists_continuable_phase_with_prescribed_multiplicities
GaloisForLFunctions/HTGeometry/WeierstrassProductMultiplicity.lean
    analyticOrderAt_weierstrassGenusProduct        exact multiplicities
    meromorphicOrderAt_divisorFunction_eq_multiplicity
GaloisForLFunctions/RHTower/AnderssonDivisorAtOrigin.lean
    exists_continuable_phase_with_divisor_at_origin
GaloisForLFunctions/RHTower/LocallyFiniteDivisorPresentation.lean
    exists_presentation_of_locallyFiniteDivisor
    exists_continuable_phase_with_prescribed_locallyFinite_divisor
```

The last statement is the card's divisor claim verbatim: for every locally finite signed divisor
`D` supported in `Re s < 1` there is a phase `chi` in the continuable stratum whose Euler product
continues meromorphically to the whole plane with `ord_z = D z` at every point.

Supporting layers built for it, all reusable:

```text
HTGeometry/MellinAntiderivativeStep.lean          Fubini form of the Mellin step
HTGeometry/StepProfileMellinTransform.lean        step profiles and their transforms
HTGeometry/TruncatedPowerAntiderivative.lean      the jump calculus
HTGeometry/JumpProfileLevels.lean                 the remainder chain and its window laws
HTGeometry/WindowAssignmentStep.lean              Lemma 6, full-chain form
HTGeometry/DatumNormalization.lean                normalizing Lemma 1's datum
HTGeometry/HalfPlaneMellinAnalytic.lean           convergence and holomorphy on Re w > rho + 1
HTGeometry/HalfPlaneSequenceGluing.lean           gluing an exhausting family of half planes
RHTower/StepProfileMellinLSeries.lean             the Mellin form of Abel summation
RHTower/AnderssonRemainderRepresentation.lean     Theorem 1's iterated identity
RHTower/Sieve/PrimeWindowRayleighFloor.lean       Lemma 4's arithmetic side
RHTower/Sieve/CharacterWindowMass.lean            the forced prime-power mass
RHTower/Sieve/CharacterWindowStep.lean            one window step, arbitrary length
RHTower/Sieve/LadderCharacterRecursion.lean       the ladder at a fixed order
RHTower/Sieve/StageWindowRecursion.lean           the stage with a transition window
RHTower/Sieve/CharacterStacking.lean              stacking the orders
```

### 3. Dense-null continuation seam

```text
GaloisForLFunctions/HTGeometry/HelsonZetaEulerProduct.lean
    dense_continuableStratum
GaloisForLFunctions/HTGeometry/HelsonCubeRootNonContinuation.lean
    dense_compl_continuableStratum
    frontier_continuableStratum_eq_univ
    nowhereContinuous_continuationIndicator
    no_continuous_factorization_continuationIndicator
GaloisForLFunctions/HTGeometry/HelsonStratumZeroOne.lean
    continuableStratum_dense_codense_measurable_zeroOne
GaloisForLFunctions/RHTower/HelsonStratumNull.lean
    measure_contEvent_eq_zero, measure_continuableStratum_eq_zero
```

`M` is dense, its complement is dense, its frontier is the whole torus, its indicator is continuous
at no point and factors through no continuous readout, and it is Haar-null — the last proved from
scratch here (Kolmogorov maximal inequality, uniform Abel summation, a one-sided anti-concentration
bound and two measure-preserving phase rotations), not imported from Saksman–Webb.

## What the formalization adds to the paper card

* Lemma 7 is proved for the **full** remainder chain, datum included; the datum's decay is what
  makes it absorbable, and the size condition is split into four quarters rather than two halves.
* Theorem 1's entire function is obtained by gluing the representations of all orders over half
  planes whose abscissas `(j+1)(theta + (1-theta)/3) + 2 theta - j` decrease to `-infinity`.
* The logarithmic derivative of a Helson zeta function is identified with `-L(chi·Lambda, s)` from
  the completely multiplicative extension of the phases and the twisted convolution `Lambda * 1 = log`.
* The realized divisor is exact: the order of a Weierstrass product at a point is the multiplicity
  of that point in the zero sequence, and an integer power of `z` supplies an order at the origin.
* An arbitrary locally finite signed divisor is presented by two sequences whose auxiliary points
  cancel, so the divisor map is surjective in the literal sense.
