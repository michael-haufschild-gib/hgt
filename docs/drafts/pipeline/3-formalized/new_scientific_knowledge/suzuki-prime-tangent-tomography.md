# Suzuki prime-tangent tomography

- **ID:** `suzuki-prime-tangent-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / FINITE BOHR RECONSTRUCTION / SUZUKI SOURCE CONNECTOR
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [NOT AN RH PROOF]`
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-high-clock-prime-tangent-tomography.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeTangentTomography.lean`

## Statement

Suzuki's first weighted source tangent has finite arithmetic packet

```text
sum_m Lambda(m)(sqrt(m)+1/(m sqrt(m))) sin(pi n log(m)/a).
```

At a phase-nonresonant aperture, complex Cesaro demodulation at the target phase recovers its
coefficient. Dividing by the explicit positive reflected-step scale recovers exactly
`ArithmeticFunction.vonMangoldt m`. Thus the formal result retains values, not only prime-power
support.

## Formal dependency chain

The module proves:

```text
tendsto_natCast_inv_complex_zero
  -> tendsto_suzukiCesaroMean_geometric_zero
  -> tendsto_suzukiFinitePhaseCarrier_bohrCoefficient
  -> tendsto_suzukiFiniteSinePhaseCarrier_bohrCoefficient
  -> tendsto_suzukiPrimeTangentCarrier_bohrCoefficient
  -> tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient
  -> tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient_of_nonresonant.
```

Source-specific declarations include:

```text
suzukiPrimeTangentPhase
suzukiPrimeTangentScale
suzukiPrimeTangentScale_eq_reflected
suzukiPrimeTangentWeight
suzukiPrimeTangentCarrier
SuzukiPrimeTangentNonresonant
suzukiPrimeTangentNormalize
suzukiPrimeTangentWeight_ne_zero_iff_primePow.
```

The exact phase has norm one. For `m>=2`, its scale is strictly positive and its unnormalized
weight is nonzero exactly when `m` is a prime power. One finite nonresonance certificate supplies
all target hypotheses in the packet.

## Scope boundary

Lean formalizes the finite harmonic-analysis and arithmetic reconstruction core. Paper theorem
derives the packet from Suzuki's distributional formula (2.11), proves exact endpoint `Si` term,
proves residual is `C^1`, and constructs cofinal nonresonant apertures. Construction of Suzuki's
unbounded Friedrichs operator and that analytic distribution-to-packet passage remain outside
current source layer.

No RH assumption, computation, project axiom, `sorry`, or finite-dimensional approximation is
used. The theorem does not assert uniformity as aperture grows or identify a Xi divisor.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeTangentTomography.lean
lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeTangentTomography
lake env lean /tmp/SuzukiPrimeTangentAxioms.lean
```

passed. The exact build completed successfully. Every audited capstone reports only Lean/mathlib
foundations `propext`, `Classical.choice`, and `Quot.sound`.

Repository-wide `scripts/formal_tools.py lint` also passed after concurrent umbrella state settled.

## Gates

- [x] 0 -> 1: source packet and exact recovery target isolated
- [x] 1 -> 2: full paper proof complete
- [x] 2 -> 3: source check, exact module build, and axiom audit complete
- [ ] 3 -> 4: external novelty audit and publication treatment pending
