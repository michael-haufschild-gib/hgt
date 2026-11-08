# Endpoint-singular atom profiles

- **ID:** aal-endpoint-singular-atom-profiles
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Question:** Can an endpoint-singular, square-integrable atom profile produce an arithmetic Weil floor with exponential weight exponent below `1`?

## Candidate

A profile behaving as `t^(α−1)` near one endpoint, with `1/2<α<1`, has the candidate Fourier magnitude `|ξ|^(−α)`. The exponent `2α−1` describes the integrated squared spectral tail; it cannot be substituted for the aliasing weight exponent. The pointwise squared Fourier factor instead scales with `2α`. The existing tilted-spline window uses `exp(-8u)` alongside fourth-power Fourier decay (`integral_normalized_synthesis_exponential_mass_eq`). A new window-limit calculation is required before claiming any exponent below `1`.

## Constraints

Current critical whole-matrix positivity uses the smooth `tiltedUnitSpline`; its proof does not apply directly to these profiles. Square integrability alone does not control the Gamma form, prime cross terms, discretization errors, or the full zero sum. A smooth approximation must retain quantitative control of all these terms. No positivity premise may be added to replace this work.

## Status

No subunit aliasing exponent, arithmetic floor, or AAL conclusion is established. The reflected-pair threshold is formalized separately in `3-formalized/reflected-zero-pair-weighted-spectrum.md`.
