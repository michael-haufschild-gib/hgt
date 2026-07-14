# Prime--archimedean endpoint-calibrated Hausdorff law for RH

- **ID:** `prime-arch-endpoint-calibrated-hausdorff-rh`
- **Stage:** 3-formalized
- **Type:** FORMALIZED REDUCTION (not new scientific knowledge)
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean`

## Parameterized law

For a radius `R > 0` and a real sequence `m`, define

```text
D_R(k,0) = m_k,
D_R(k,r+1) = R * D_R(k,r) - D_R(k+1,r).
```

Suppose every reciprocal-square Xi thermal node is at most `R`.  Lean proves

```text
(forall k r, 0 <= D_R(k,r)) <-> RiemannHypothesis
```

for `m = normalizedPrimeArchMoment`.

The forward direction is generic.  Radius normalization

```text
s_n = m_n / R^n
```

gives the exact identity

```text
D_1^s(k,r) = D_R^m(k,r) / R^(k+r).
```

Thus calibrated positivity makes `s` a unit-interval Hausdorff sequence.  The canonical
Hausdorff--Bernstein finite systems for `s` are rescaled by multiplying every node by `R`; they
then converge pointwise to `m`.  The finite-positive-atomic closure theorem feeds the existing RH
consumer.

Under RH, the finite Xi thermal truncations converge pointwise to `m`, and their calibrated
differences are

```text
sum_(j<N) lambda_j^(k+1) (R-lambda_j)^r >= 0.
```

Closedness under pointwise convergence proves the reverse direction.

## Source-calibrated radius

Let

```text
C = xiEndpointCompletedCurvature,
R_C = C / (1-C).
```

The formal endpoint height law gives

```text
1/C - 1 <= (Im rho)^2.
```

Consequently every reciprocal-square Xi coordinate has norm at most `R_C`, hence every thermal
node is at most `R_C`.  The established source bounds give

```text
0 < R_C < 1,
R_C < 2/41.
```

Therefore Lean proves the exact source-native equivalence

```text
ScaledHausdorffMomentDifferencesNonnegative R_C normalizedPrimeArchMoment
  <-> RiemannHypothesis.
```

For every admissible rectangular prime--polar source, it also proves equivalence with

```text
abscissaOfAbsConv
  (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) <= 1.
```

## Proof impact

The former interval `[0,1]` is not intrinsic.  The entire complete-monotonicity criterion can be
calibrated to any proved reciprocal-square radius, and the endpoint source itself supplies the
exact radius `C/(1-C)`.  Future source estimates can therefore work with a freely chosen valid
scale or with the tight source-native scale.  No measure, Hamiltonian, observable, or
thermodynamic family appears in the hypothesis.

This does not prove RH.  Positively stated, proving the calibrated linear inequalities at the
endpoint radius completes RH and the critical prime--polar negative-abscissa bound.

## Lean surface

- `scaledHausdorffMomentDifference`
- `ScaledHausdorffMomentDifferencesNonnegative`
- `hausdorffMomentDifference_radiusNormalizedMoment`
- `finitePositiveAtomicMomentSequence_radiusRescale`
- `finitePositiveAtomicLocalMomentClosure_of_scaledHausdorffMomentDifferencesNonnegative`
- `riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative`
- `primeArchEndpointHausdorffRadius`
- `xiThermalNode_le_primeArchEndpointHausdorffRadius`
- `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis_of_node_le`
- `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative`

## Verification

- Direct Lean check: passed without warnings.
- Narrow Lake build: passed.
- Umbrella import: added to `formal/GaloisForLFunctions/RHTower.lean`.
- Axiom audit of the generic closure theorem, parameterized RH equivalence, endpoint-calibrated
  equivalence, and abscissa equivalence: only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration occurs in the module.
