# Reflected bi-heat finite-part universal wall selectivity no-go

- **ID:** RBH-TFPK
- **Stage:** 5-failed
- **Type:** FALSIFIED CONJECTURE / KLEIN-FOUR ZERO-LOCUS CLASSIFICATION
- **Parent:** RBH-TFPW
- **Frontier-map policy:** read only

## Falsified conjecture

Canonical wall-odd channel is not universally selective:

`Im(reflectedBiHeatFinitePart P)=0 ↔ Re(P.z)=1/2`

is false.

## Exact killing theorem/mechanism

Complex conjugation fixes every real-order datum.  Exact finite-part conjugation
therefore forces canonical finite part real on entire real axis, including
off-wall points.  Lean constructs explicit admissible witness `z=1/4`, `x=1`
with off-wall real part and zero imaginary finite part, and proves closed
negation of universal classifier.

## Strongest positive survivor

Define mixed grade--phase coordinate

`M(z)=(Re z-1/2) Im z`.

It has same Klein-four character as canonical imaginary finite part:

- even under `z↦1-z`;
- odd under conjugation;
- odd under `z↦1-conj z`.

Its zero set is exactly critical wall union real axis, and entire cross is forced
into zero set of canonical odd finite-part channel.  On actual Xi divisor
support, unconditional nonzero height removes real-axis branch, so `M=0` is
again exactly critical wall.

## New insight

Canonical odd channel is mixed grade--phase object, not pure horizontal wall
coordinate.  Universal RBH source orientation is impossible on all strip data.
Viable producer must restrict to nonreal divisor locus and prove no additional
zeros there, or compare canonical finite-part imaginary part to exact mixed
coordinate with nonvanishing quotient.

## Corpus basis

- RBH-TFPW proves exact finite-part conjugation and wall Schwarz covariance.
- `xi_divisor_support_im_ne_zero` proves actual Xi divisor support avoids real
  axis.
- Mandatory corpus search found no Klein-four zero-cross classification for
  canonical RBH finite part.

## Formal theorem package

- `ReflectedBiHeatDatum.conjugate_eq_iff_im_eq_zero`
- `reflectedBiHeatFinitePart_im_eq_zero_of_z_im_eq_zero`
- `reflectedBiHeatMixedOrientationCoordinate_one_sub`
- `reflectedBiHeatMixedOrientationCoordinate_conj`
- `reflectedBiHeatMixedOrientationCoordinate_wallReflect`
- `reflectedBiHeatMixedOrientationCoordinate_eq_zero_iff`
- `reflectedBiHeatFinitePart_im_eq_zero_of_mixedOrientationCoordinate_eq_zero`
- `reflectedBiHeatOffWallRealWitness_finitePart_im_eq_zero`
- `not_forall_reflectedBiHeatFinitePart_im_eq_zero_iff_re_eq_half`
- `reflectedBiHeatMixedOrientationCoordinate_xiSupport_eq_zero_iff`

## Provisional literature audit

Search checked classical/general reflection and functional-equation sources;
no exact theorem found for this regularized additive-heat finite part or its
Klein-four forced zero cross.  Priority remains provisional.

## Status

- Module:
  `GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartKleinFourNoGo`
- Falsification and strongest positive survivor dependency-closed on paper.
- Exact no-go and survivor formalized in Lean.
- Direct `lake env lean` check passed.
- Targeted `lake build` passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired; full umbrella build intentionally not run.

## Log

- 2026-08-27 — universal selectivity conjecture frozen and falsified.
- 2026-08-27 — exact zero-cross survivor and Xi-support restriction formalized;
  route retired in universal form.
