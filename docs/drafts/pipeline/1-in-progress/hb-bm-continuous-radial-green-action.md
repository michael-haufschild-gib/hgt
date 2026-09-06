# HB continuous radial Green action

- **ID:** HB-BM-CONTINUOUS-RADIAL-GREEN
- **Stage:** 1-in-progress
- **Type:** exact source-action construction
- **Goal:** unconditional closed Lean RH proof/falsification through HB; not achieved here.

## Full chain

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → extinction on the fixed Hawking clock → RH.

## Corpus gap and intended advance

`ThetaCuspHawkingBMSecondHarmonicHorizonBasisGreenKrein` supplies exact regular/normalizable
and complementary/normalizable kernels, nonzero denominators, derivative jumps, and finite
packet actions. `ThetaCuspHawkingBMSecondHarmonicFiniteSourceGreenRadical` classifies the
finite packet moment. A continuous radial source still needs an actual integral response,
its forced differential equation, and its selected boundary branches. The time-support
audit prevents identifying radial basis exchange with reversal of causal time by assumption.

Corpus searches: `hawking physical causal`, `causal green reality`, `green conjugate`,
`causal inverse`, `hawking volterra`, `retarded resonance`, `exponential convolution`,
`Hawking source radial`, and `plebanski source`. The variable-oscillator Duhamel construction
in `HTGeometry.DuhamelVariableOscillator` supplies the separated-moment proof pattern.

## Dependency-closed paper construction

Fix overtone `n`, complex momentum `chi` with nonzero real part, and radial anchors
`0<a<b<1`. Let `R` be the actual regular BM horizon solution and `V` its actual normalizable
AdS solution. Their normalized Wronskian `D=p(R V'-R' V)` is the nonzero constant already
computed from the forbidden connection coefficient. Write `w=p/[z(1-z)]`.

For a continuous source `f` in the radial interior, define

`A(z)=integral_a^z R(t) w(t) f(t)/D dt`,
`B(z)=integral_z^b V(t) w(t) f(t)/D dt`,
`u(z)=V(z) A(z)+R(z) B(z)`.

All integrals are over compact intervals inside the radial domain. Differentiation gives
`u'=V' A+R' B` because the two moving-endpoint terms cancel. Differentiating again leaves
`u''=V'' A+R'' B+(V'R-R'V)wf/D`. The exact Wronskian turns this last term into
`f/[z(1-z)]`; the homogeneous equations for `R,V` then give the forced BM equation with
source exactly `f`. At the anchors, the solution jet lies on the selected regular and
normalizable lines. For a source supported in `[a,b]`, the same pure branches persist in
the exterior radial intervals. This constructs a fixed source-independent operator, without
fitting any Xi-copy profile.

Extending either cutoff outside the source support adds only zero integrals. Thus every
larger surrounding pair gives exactly the same response throughout the radial interior.
The separated formula equals the integral of the already formalized two sewn Green-kernel
pieces against the physical Sturm weight. Scalar multiplication of the source passes through
the response. If the response vanishes throughout the interior, both actual derivatives
vanish there; the forced equation then gives `f=0`. Conversely, a zero interior source has
zero moments and response. This is faithfulness of the full field, not cancellation of a
boundary moment. The Xi specialization obtains nondegeneracy from the existing angular
momentum theorem and adds no Wronskian premise.

## Scope

This is a reduced radial boundary-value action at the actual second-harmonic frequency. It does not
yet identify a time-retarded augmented Einstein operator, derive the complete nonlinear
source and left-QNM projection, or prove extinction. The canonical spin-two source must
still be shown to belong to the required radial domain; compact-support control is not
asserted for that physical source. No route is retired by this construction.

## Tracking

- [x] Whole-corpus and exact boundary-kernel audit.
- [x] Dependency-closed paper construction.
- [ ] Scratch and direct Lean proof of integral response and forced equation.
- [ ] Boundary branch verification and source-domain statement.
- [ ] Umbrella wiring, leaf-only final build, new-only axiom audit, lint snapshot.
- [ ] Current frontier and route-independent ledger update.
