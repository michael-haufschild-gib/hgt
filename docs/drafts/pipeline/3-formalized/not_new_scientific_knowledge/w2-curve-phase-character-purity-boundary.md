# Curve phase characters and exact endpoint purity

- **ID:** w2-curve-phase-character-purity-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W2 construction](../../1-in-progress/w2-representation-construction.md).
- **Statement:** Every nonempty curve datum has a positive coherent character from its periodic phase alphabet; coordinatewise equality with its actual endpoint alphabet holds exactly under Frobenius purity.

## Exact construction

For periodic zeros `ρ_(i,k)` and period `P>0`, put

`b_(i,k)=1/(1/4+(Im ρ_(i,k))²)`, `M=Σb`, `w_(i,k)=b_(i,k)/M`.

All weights are positive. The periodic-height bound gives

`b_(i,k) ≤ [2/min(1/4,(P/2)²)]/(1+|k|)²`.

Thus `M` is finite and positive, and `Σw=1`. Independent coloring gives a normalized,
central, restriction-coherent character whose length-`r` cycle value is `Σw^r`.

The coordinatewise equality

`w_(i,k) = [1/(ρ_(i,k)(1−ρ_(i,k)))]/M`

holds for every `i,k` iff every Frobenius eigenvalue has norm one. Indeed, equality
makes every endpoint coordinate real. The first positive period has nonzero imaginary
part, so endpoint reality forces `Re ρ=1/2`, hence purity. Conversely, on that line the
endpoint denominator is exactly `1/4+(Im ρ)²`.

## Fake-model boundary

The golden fake has this positive phase character but fails the exact endpoint equality.
It also has positive real endpoint weights at every principal zero, while the first-period
reality test fails. Neither phase positivity nor principal-branch positivity detects purity.

These are construction and identification boundaries, not an arithmetic purity producer
or a claim of a new character classification.

## Formal certificate

Under `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Representation/`:

- `EndpointCalibration.lean`: `endpoint_firstPeriod_real_iff`,
  `endpoint_alphabet_positive_iff_unitary`, `golden_endpoint_period_test`.
- `CurvePhaseAlphabet.lean`: `summable_phaseEndpointWeight`, `tsum_phaseEndpointColor`,
  `phaseEndpoint_positiveCycleFamily`, `phaseEndpointColor_eq_endpoint_iff`,
  `golden_phase_character_boundary`.

The independent-color character is supplied by `CountableColoring.lean` and
`CycleCharacterIdentification.lean`. Both curve modules pass direct Lean leaf checking
and are wired into their umbrella.
