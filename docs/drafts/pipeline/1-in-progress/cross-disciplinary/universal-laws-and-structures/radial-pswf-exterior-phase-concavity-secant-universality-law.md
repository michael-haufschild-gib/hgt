# Radial PSWF exterior-phase concavity/secant universality law

- **ID:** `radial-pswf-exterior-phase-concavity-secant-universality-law`
- **Law:** LAW498
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/RadialPSWFExteriorPhaseConcavitySecantUniversalityLaw.lean`

## Theorem

For the radial PSWF exterior Liouville speed and normalized phase

```text
S_sigma(z) = sqrt((z^2 - sigma^2) / (z^2 - 1)),
Phi_sigma(z) = integral from 2 to z of S_sigma(u) du,
```

assume `0 <= sigma <= 1`.  On the complete exterior ray `(1, infinity)`:

1. `Phi_sigma` is concave;
2. every secant is trapped between its endpoint speeds and above the free speed:

   ```text
   1 <= S_sigma(y)
     <= (Phi_sigma(y) - Phi_sigma(x)) / (y - x)
     <= S_sigma(x)                    for 1 < x < y.
   ```

If `sigma^2 < 1`, the phase is strictly concave and both endpoint secant inequalities are strict.
Thus every finite exterior phase increment carries one sharp global law: nonstationary free-speed
floor, decreasing local speed, and strict interior averaging away from the boundary parameter.

## Theorem-generated derivation

This law was not predicted and then searched.  Whole-corpus same-folder leaf pairing exposed:

- `RadialPSWFExteriorPhase.hasDerivAt_radialPSWFExteriorPhase`;
- `RadialPSWFExteriorPhase.one_le_radialPSWFExteriorSpeed`;
- `RadialPSWFSpeedMonotone.antitoneOn_radialPSWFExteriorSpeed`;
- `RadialPSWFSpeedMonotone.hasDerivAt_radialPSWFExteriorSpeed`;
- `RadialPSWFSpeedMonotone.radialPSWFExteriorSpeed_deriv_nonpos`.

The phase derivative equals `S_sigma` at every exterior point.  Since `S_sigma` is antitone,
the derivative criterion for concavity makes `Phi_sigma` concave on `(1, infinity)`.  Concave
endpoint derivative inequalities give

```text
S_sigma(y) <= slope(Phi_sigma, x, y) <= S_sigma(x).
```

The already-proved speed floor supplies the leading `1`.  When `sigma^2 < 1`, the exact speed
derivative has positive denominator and strictly negative numerator at every exterior point.
Hence `S_sigma` is strictly antitone, the phase is strictly concave, and the endpoint inequalities
are strict.

No numerical computation is used.

## Strict corpus delta

`RadialPSWFExteriorPhase` proves only pointwise phase derivatives and a pointwise derivative floor.
`RadialPSWFSpeedMonotone` proves only speed monotonicity, its exact derivative, and separate
Liouville--Green energy signs.  Neither module promotes these local facts to concavity of the
integrated phase or controls every finite phase increment simultaneously by both endpoint speeds.
The strict secant envelope is therefore a new global finite-interval law.

## Post-proof novelty audit

Performed only after the dependency-closed Lean proof passed.

- [DLMF Chapter 30](https://dlmf.nist.gov/30.2) records spheroidal differential equations and
  their Liouville normal form, but not this exterior integral phase, its concavity, or endpoint
  secant envelope.
- Bonami--Karoui, [*Uniform approximation and explicit estimates for the prolate spheroidal wave
  functions*](https://arxiv.org/abs/1405.3676), develops uniform PSWF approximation and explicit
  bounds, but the abstract and searchable record do not state the exterior phase law above.
- Serkh--Bremer, [*Phase function methods for second order inhomogeneous linear ordinary
  differential equations*](https://arxiv.org/abs/2211.13744), treats slowly varying phase
  functions and Liouville--Green methods generally, not the exact radial-PSWF speed sandwich.

Targeted searches for radial/prolate spheroidal Liouville phase concavity, decreasing exterior
speed, and secant bounds between endpoint speeds found standard spheroidal and Liouville--Green
theory but no statement of this exact law.  Verdict:
`[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Generic “antitone derivative implies concavity” is
classical; novelty is claimed only for this exact radial-PSWF exterior specialization and its
simultaneous sharp free-speed/endpoint-speed sandwich.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean` passed
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
