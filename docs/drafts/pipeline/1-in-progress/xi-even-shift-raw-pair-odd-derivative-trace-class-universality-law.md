# Xi even-shift raw-pair / odd-derivative trace-class universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Lean-derived statement

For a finite raw completed-Xi vertex packet with grade map `g`, define its canonical odd
derivative-order dictionary by

```text
o(v) = 2 g(v) - 1.
```

On the nonzero-grade phase forced by raw reconstruction, the positive successor aperture of `o`
is exactly the doubled raw aperture:

```text
o(v) + 1 = 2 g(v).
```

At independently chosen source, curvature, metric, and intrinsic primes, independently chosen jet
depths, and independently chosen nonnegative scales, the following are equivalent:

1. the complete arbitrary-edge/full-vertex raw Gaussian-curvature certificate for `g`;
2. the positive derivative-order trace-class/intrinsic-dimension certificate for `o`, together
   with independence of the selected raw edge family in the pointed collision-incidence matroid.

Thus one and the same doubled aperture carries raw/corrected edge reconstruction, Kirchhoff
rigidity, two valuation-base differential independence laws, trace-class response, zero
counterterm, strict Gaussian curvature, operator nonnormality, intrinsic affine dimension one,
and corrected-determinant convexity/concavity.

## Corpus inputs

- `xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le`
- `xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff`
- `xiDerivativeOrderSuccessorAperture`
- `XiEvenShiftRawPairIncidenceIndependent`

No numerical computation or external mathematical premise is used.

## Paper proof

The raw certificate is equivalent to

```text
((Injective g and forall v, g(v) != 0) and EdgeIncidenceIndependent) and 2 <= N.
```

For `o(v)=2g(v)-1`, elementary natural-number arithmetic gives:

- `Injective o` iff `Injective g`;
- `o(v) != 0` iff `g(v) != 0`;
- when `g(v) != 0`, `succ(o(v))=2g(v)`.

The positive trace-class/intrinsic certificate for `o` is equivalent to

```text
(Injective o and forall v, o(v) != 0) and 2 <= N.
```

Substitution leaves exactly the raw elementary stratum after adjoining
`EdgeIncidenceIndependent`. This proves both directions and shows that all stored primes, depths,
and nonnegative scales are spectators.

## Hostile subsumption audit

- Parent raw law reaches doubled-aperture intrinsic Gaussian geometry but contains no positive
  derivative-order trace-class response or zero counterterm.
- Parent positive-order law reaches trace-class/intrinsic geometry but contains no arbitrary raw
  edge family, pointed collision-incidence matroid, Kirchhoff rigidity, or raw/corrected
  differential pair phase.
- Existing successor-aperture connectors use `n -> n+1`; no corpus theorem identifies the
  doubled raw aperture with the successor of the odd predecessor `2g-1`.
- The result is not a conjunction wrapper: the arithmetic aperture identity identifies the
  geometric packet on both sides, and the equivalence isolates edge-incidence independence as the
  exact extra datum.

## Lean verification

Formal module:

```text
formal/GaloisForLFunctions/RHTower/XiEvenShiftRawPairOddDerivativeTraceClassUniversalityLaw.lean
```

The module defines the odd predecessor, proves its successor-aperture identity, collision
preservation, and positivity equivalence, then proves the cross-certificate iff. Required exact
check passed:

```text
lake env lean GaloisForLFunctions/RHTower/XiEvenShiftRawPairOddDerivativeTraceClassUniversalityLaw.lean
```

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Post-proof literature boundary

Searches were run only after the Lean theorem passed. Closest located sources were:

- Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*,
  arXiv:2206.03682, which develops zeta screw kernels, Weil-type positivity, and trace-class
  operators;
- Masatoshi Suzuki, *The screw line of the Riemann zeta-function and its applications*,
  arXiv:2209.04658, which gives Hilbert-space/norm formulations related to RH;
- Dong, Eriksson, Nickisch, Bindel, and Wilson, *Scalable Log Determinants for Gaussian Process
  Kernel Learning*, arXiv:1711.03481, which studies positive Gaussian kernel log determinants and
  their derivatives computationally.

No source located states the exact odd-predecessor identity `succ(2g-1)=2g` as a bridge from an
arbitrary raw completed-Xi edge incidence certificate to an independently parameterized positive
derivative-order trace-class/intrinsic Gaussian certificate. Negative search is not proof of
priority; specialist review remains required.

## Gates

- [x] whole-corpus source search
- [x] exact conjecture stated from theorem interfaces
- [x] dependency-closed paper proof
- [x] hostile corpus-subsumption audit
- [x] Lean exact check
- [x] umbrella wiring
- [x] post-proof literature audit
- [ ] final axiom/lint/build audit
