# Bounded-relation log-magnitude hypertranscendence — formalization certificate

- **ID:** `bounded-relation-log-magnitude-hypertranscendence`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/bounded-relation-log-magnitude-hypertranscendence.md`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH]`

## Formalized theorem

Lean proves the complete bounded-relation confinement and balanced exponential-survival chain,
then constructs literal entire functions whose positive logarithmic magnitudes realize arbitrary
superlinear profiles while every algebraic unit-modulus phase specialization remains
hypertranscendental.  The shifted-polynomial specialization includes exact value, first-difference,
and second-difference asymptotics and full Taylor support.

## Source modules and capstones

```text
formal/GaloisForLFunctions/HTGeometry/BoundedRelationConfinement.lean
formal/GaloisForLFunctions/HTGeometry/BoundedRelationExponentialSurvival.lean
formal/GaloisForLFunctions/HTGeometry/BoundedRelationLogMagnitudeHypertranscendence.lean
formal/GaloisForLFunctions/HTGeometry/PrivatePrimeApproximation.lean
formal/GaloisForLFunctions/HTGeometry/BoundedRelationProfileRealization.lean

hypertranscendental_boundedRelationExponentialFunction
exists_privatePrime_superlinear_profile_realization
exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental
exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental
exists_privatePrime_shiftedPolynomial_positive_entire_fullSupport_hypertranscendental
```

## Verification and boundary

Serialized direct checks and the `HTGeometry` umbrella build pass.  Combined scratch
`#print axioms` audits use only `propext`, `Classical.choice`, and `Quot.sound`.  No analytic or
arithmetic parent is supplied as a theorem hypothesis.  The theorem is an HT obstruction for the
specified coefficient-log architecture; it proves no zero-location, positivity, spectral, or RH
statement.
