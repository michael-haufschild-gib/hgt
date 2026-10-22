# Sonin fidelity-orientation physical-sector universality law

- **ID:** `sonin-fidelity-orientation-physical-sector-universality-law`
- **Law:** LAW504
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninFidelityOrientationPhysicalSectorUniversalityLaw.lean`

## Theorem

A logarithmic Sonin state `psi` lies in the physical kernel of the static scattering constraint
`S - 1` exactly when:

```text
||psi||^4 - ||<psi,S psi>||^2 = 0
and
0 <= Re <psi,S psi>.
```

Equivalently, zero projective fidelity loss selects one of the two real scattering rays, and the
orientation sign selects precisely the physical `+1` ray.

## Theorem-generated derivation

Whole-corpus same-folder theorem-leaf pairing exposed:

- `soninLogFourierScattering_homogeneousFidelityDeficit_eq_four_mul_sectorWeights`;
- `inner_soninLogFourierScattering_eq_sectorNormSq_sub`;
- `physicalState_soninLogFourierScattering_iff_invariantAverage_fixed`;
- `soninLogFourierInvariantAverage_range_eq_constraint_ker`.

The existing exact ray-distance law deliberately leaves the sign existential. The static
constraint module identifies only the `+1` sector. Reading the overlap orientation together with
the fidelity product removes that ambiguity.

## Dependency-closed paper proof

Let `a = ||P psi||^2` and `b = ||(1-P) psi||^2`, where `P = (1+S)/2`.
Existing identities give

```text
fidelity deficit = 4ab,
Re <psi,S psi> = a-b.
```

If the deficit vanishes, `a=0` or `b=0`. Under `a-b >= 0`, the first alternative forces
`b=0`; hence always `b=0`. Thus `(1-P)psi=0`, so `P psi=psi`, equivalent to
`(S-1)psi=0`. Conversely a physical state has `P psi=psi` and `(1-P)psi=0`, making the
deficit zero and overlap `||psi||^2 >= 0`. The zero vector is included. No numerical computation
is used.

## Strict corpus delta

Corpus classifies the two unsigned scattering rays and separately identifies the physical
constraint kernel. It does not state the minimal scalar sign condition that turns projective
fidelity saturation into exact physicality. New law supplies this missing iff.

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninFidelityOrientationPhysicalSectorUniversalityLaw.lean`
proves
`soninLogFourierScattering_physicalState_iff_fidelitySaturated_nonnegative`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninFidelityOrientationPhysicalSectorUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.

- Standard pure-state fidelity is squared overlap, and spectral theory identifies invariant
  subspaces of self-adjoint involutions.
- Fourier-transform literature studies eigenspace decompositions and quantum-information
  literature studies fidelity under unitary actions, but targeted searches found no theorem
  combining homogeneous fidelity saturation with overlap orientation to characterize this
  logarithmic Sonin physical constraint kernel.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`. Novelty is limited to exact Sonin
specialization and minimal two-scalar physical-sector iff; no novelty is claimed for elementary
spectral decomposition of an involution.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
