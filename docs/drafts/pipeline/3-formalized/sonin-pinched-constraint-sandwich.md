# Sonin pinched constraint sandwich

- **ID:** sonin-pinched-constraint-sandwich
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / PHYSICS BRIDGE / RHTOWER HYPOTHESIS DISCHARGE
- **Source:** nonselective Lüders measurement, reducing subspaces, and logarithmic Sonin scattering
- **Statement:** Pinching any Sonin observable by the invariant logarithmic-scattering projector makes its compressed adjoint insertion of the scattering constraint vanish, without an observable commutation or leakage hypothesis.

## Goal

Apply the general reducing-subspace theorem to a live analytic RHTower interface.  The consumer must
remove actual premises from the full constraint-sandwich surface rather than restate a general
identity with Sonin names.

## Gates

- [x] 0 → 1 in-progress: identified the invariant logarithmic Sonin average as an orthogonal code projector and `S-1` as a self-adjoint constraint
- [x] 1 → 2 fully-proven: proved general pinching transition cancellation, pinching commutation, the abstract sandwich discharge, and the concrete Sonin collapse
- [x] 2 → 3 formalized: scratch certification, serialized exact-module cache builds, direct checks of both touched Lean files, and axiom audit pass
- [ ] 3 → 4 publication-ready: identify a resolvent, Euler, or seam observable whose unpinched off-diagonal sector carries independent analytic information

## Physics source

- G. Lüders, *Über die Zustandsänderung durch den Meßprozeß*, Annalen der Physik 443 (1950), 322--328, introduced the nonselective projective state change represented here by two-outcome pinching.
- D. W. Kribs, R. Laflamme, D. Poulin, and M. Lesosky, *Operator quantum error correction*, arXiv:quant-ph/0504189, places code subspaces, decoherence-free subspaces, and noiseless subsystems in an operator framework.

The formal result is a bridge from these standard measurement/code principles to the existing
Sonin constraint interface.  It is not claimed as a novel theorem of quantum measurement theory.

## Exact relation

For an idempotent `P`, let

```text
Phi_P(X) = P X P + (1-P) X (1-P).
```

Direct block multiplication gives

```text
(1-P) Phi_P(X) P = 0,                                    (1)
P Phi_P(X) (1-P) = 0,                                    (2)
P Phi_P(X) = Phi_P(X) P.                                 (3)
```

Let `P=P_S` be the invariant logarithmic Sonin scattering average and `C=S-1`.  Existing Lean
theorems provide

```text
P_S^2 = P_S,
P_S† = P_S,
C† = C,
P_S C = 0.
```

The reducing-subspace discharge theorem combines these facts with `(1)` to give, for every bounded
Sonin observable `X`,

```text
P_S Phi_P_S(X)† (S-1) Phi_P_S(X) P_S = 0.                (4)
```

No premise on `X` remains.  In particular, neither `[P_S,X]=0`, a separately supplied no-return
condition, nor the redundant relation `(S-1)P_S=0` is assumed.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/ConstraintCodePinchingCompression.lean` proves:

- `twoOutcomeLowerTransition_pinching_eq_zero`;
- `twoOutcomeUpperTransition_pinching_eq_zero`;
- `twoOutcomePinching_commutes`;
- `selfAdjointConstraint_twoOutcomePinching_adjointSandwich_compression_eq_zero`.

`formal/GaloisForLFunctions/RHTower/SoninLogConstraintPinchingCompression.lean` proves:

- `soninLogConstraintAdjointSandwich_compression_eq_zero_of_noDeparture`;
- `soninLogConstraintPinchedAdjointSandwich_compression_eq_zero`.

## Direct corpus application

The Sonin theorem consumes the exact scattering constraint, invariant average, involution,
self-adjointness, and finite-group-average annihilation relations from
`SoninLogCoordinateScattering.lean` and `SoninLogConstraintCompression.lean`.  It upgrades the
existing complement-excursion factorization from a description of a possible survivor to an exact
vanishing theorem after the canonical static measurement.

The theorem uses the general `HTGeometry.twoOutcomePinching` implementation and therefore depends
only on the reusable measurement interface, not on an RHTower-specific copy of the same channel.

## Corpus value

Equation `(4)` is an actual RHTower premise elimination.  Any later Sonin theorem formulated with a
pinched observable can erase the full adjoint scattering-constraint insertion immediately, without
tracking two off-diagonal blocks or two constraint orientations.  The surviving research datum is
therefore not the pinched constraint sandwich; it must live in the measurement disturbance
`X-Phi_P_S(X)`, equivalently the two scattering-transition corners.

This localization opens a sharper route: test candidate Euler/resolvent/seam observables by whether
their unpinched disturbance carries the needed analytic boundary value.  The block-diagonal measured
part is now formally known to be constraint-invisible.

## Status

[PROVED IN LEAN] Both exact targets and both direct source checks pass.  The algebraic pinching
theorems use only `propext`; the Hilbert-space and Sonin consumers use Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.  No full project build, numerical experiment, or
concurrent Lean process was run.
