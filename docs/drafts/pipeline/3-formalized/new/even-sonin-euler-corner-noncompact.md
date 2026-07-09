# Even Sonin Euler corner is noncompact

- **ID:** even-sonin-euler-corner-noncompact
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** `../../2-fully-proven/new/sonin-euler-metric-corner-noncompact.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninEvenCarrier.lean`

## Statement

Let `a > 0` and `p > 1`. On `L²(ℝ)^ev`, let `A_a` be the central-interval indicator
projection, let `R_a = F⁻¹ A_a F`, and let `Q_a` be the orthogonal projection onto

`ker(A_a) ∩ ker(R_a)`.

For the normalized dilation `U_p f(x) = sqrt(p) f(px)`, the restricted lower corner

`(1 - Q_a) (U_p + U_p⁻¹) Q_a`

is not compact. The positive Euler corner is exactly its nonzero scalar multiple

`-(sqrt(p))⁻¹ (1 - Q_a) (U_p + U_p⁻¹) Q_a`,

and is therefore noncompact. This holds for every real scale `p > 1`; the Lean theorem also
exports the specialization to every prime natural number.

## Formal surface

The endpoint module proves:

- `evenCentralSoninProjection_eq_starProjection`
- `evenCentralSoninDilationCorner_eq_crossBoundary`
- `evenCentralSoninDilationCorner_not_isCompactOperator`
- `evenCentralPositiveEulerCorner_eq_smul`
- `evenCentralPositiveEulerCorner_not_isCompactOperator`
- `evenCentralPrimePositiveEulerCorner_not_isCompactOperator`

The proof is internal to the even carrier. It constructs an orthonormal sequence of symmetric
shell indicators, projects it into the two-constraint Sonin carrier, proves that the correction
tends to zero, and obtains a uniform lower bound on the crossed image of the resulting bounded
weakly-null sequence. It does not infer restricted noncompactness from the ambient full-`L²`
theorem.

The imported analytic chain supplies every premise:

- `L2FourierIntegralBridge.lean` identifies the unitary `L²` Fourier transform with the classical
  Fourier integral on integrable representatives.
- `BoundedSupportFourierUncertainty.lean` and `L2FourierUncertainty.lean` prove that simultaneous
  bounded physical and Fourier support forces an `L²` function to vanish.
- `FiniteTimeBandFourierCompact.lean` proves compactness of the finite time-band block by finite-rank
  approximation of its `L²` functional field.
- `SoninAlternatingBlockStrict.lean` converts compactness and absence of a `1`-eigenvector into the
  strict norm bound needed by `SoninProjectionCorrection.lean`.
- `SoninL2Model.lean` and `SoninL2ShellNull.lean` construct the cutoffs, normalized dilations,
  symmetric shell sequence, and asymptotically null Fourier constraint.
- `L2FourierReflection.lean` proves Fourier/reflection compatibility, allowing every operator and
  witness to be restricted to `L²(ℝ)^ev`.

## Verification

- The endpoint module passes a targeted Lean build.
- `#print axioms` for the projection identity, both noncompactness theorems, the scalar identity,
  and the prime specialization reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The endpoint contains no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- No full project build is part of this card's verification.

## Exact boundary

This card formalizes the unconditional analytic theorem on the exact even Sonin carrier. It does
not encode the Connes--Consani--Moscovici dual Hardy--Titchmarsh unitary, the identification with
their entire-function carrier `B_lambda`, or the multiplication-operator transport for the local
Euler weight. Those source identifications remain in the fully-proven paper card. General Schatten
ideals are also not represented in the current Lean layer, so the consequence that a noncompact
operator lies in no finite Schatten class remains a paper-level corollary.

## Dual gate

- **NOVEL:** The common Sonin constraint does not regularize the prime-dilation shell crossing.
  This is stronger than ambient support crossing and is proved for every real scale `p > 1`, with
  primes as a specialization.
- **SIGNIFICANT:** The result closes the unsmoothed positive Euler corner as a compact or trace-ideal
  seam on the fixed-cutoff even carrier. Any viable determinant construction needs additional
  smoothing or a different relative operator.

## Gates

- [x] 0 -> 1: fixed-cutoff even carrier, operator normalization, and degenerate parameters isolated.
- [x] 1 -> 2: corrected-shell proof completed on paper.
- [x] 2 -> 3: analytic theorem and prime specialization formalized unconditionally in Lean.
- [ ] 3 -> 4: requires source-unitary formalization and independent publication audit.
