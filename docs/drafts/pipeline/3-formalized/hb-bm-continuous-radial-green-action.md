# HB continuous radial Green action

- **ID:** HB-BM-CONTINUOUS-RADIAL-GREEN
- **Stage:** 3-formalized
- **Type:** exact source-action construction
- **Goal:** unconditional closed Lean RH proof/falsification through HB; not achieved here.

## Full chain

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → extinction on the fixed Hawking clock → RH.

## Exact advance over the prior kernel construction

`ThetaCuspHawkingBMSecondHarmonicHorizonBasisGreenKrein` supplies exact regular/normalizable
and complementary/normalizable kernels, nonzero denominators, derivative jumps, and finite
packet actions. `ThetaCuspHawkingBMSecondHarmonicFiniteSourceGreenRadical` classifies the
finite packet moment. `ThetaCuspHawkingBMSecondHarmonicContinuousGreenAction` supplies the
actual integral response for continuous radial sources, proves its forced differential
equation, and verifies its selected boundary branches. The time-support
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

## Lean result and verification

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicContinuousGreenAction.lean`
contains 15 new public theorems. Its only direct import is the existing horizon-basis
Green--Krein leaf. The central theorem `d4BMPlusPlusContinuousGreenResponse_forcedEquation`
uses actual first and second derivatives, not only declared formal jets. The last theorem
specializes it to every Xi fibre without a supplied nondegeneracy premise.

- Scratch and direct `lake env lean <file>` checks passed without warnings.
- Main-workspace build preflight stopped at the unrelated
  `XiCenteredOrderTwentyOneSourceBudgetClosure`, whose existing 82 MB olean lacked required
  build metadata. No dependency rebuild was started.
- Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicContinuousGreenAction`
  passed in **12 seconds** in an isolated leaf package using this exact source, the same
  toolchain, and existing corpus/mathlib oleans. The package declared only this module;
  local packages with no source targets supplied the cached import directories through
  `leanLibDir`. Preflight and build contained only the leaf and bookkeeping job. No
  umbrella or transitive rebuild ran; a fresh transitive source audit is not claimed.
- The audited source was byte-compared with the canonical file. Only this new leaf's
  `.olean` and `.ilean` artifacts were installed in the corpus build directory; no existing
  dependency traces or hashes were altered to suppress rebuilding.
- One scratch `#print axioms` audit of all 15 new public theorems passed from the main
  workspace. Each uses only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom
  or computational certificate is used. Previously audited declarations were not rechecked.
- The leaf is wired into `GaloisForLFunctions/RHTower.lean`. Corpus index refresh and
  `scripts/formal_tools.py lint --check-generated` passed; existing large-file warnings remain.
- All owned Lean processes exited. Temporary scratch sources and the isolated audit package
  are removed after recording these results.

The current frontier records the constructed radial action and its exact remaining producer.
Universal ledger F20i-d distinguishes full-field inversion from extinction of a boundary
coefficient. The full nonlinear source domain, time-causal identification, left-QNM boundary
projection, and fixed-clock extinction remain open. RH is not proved or falsified here.

## Tracking

- [x] Whole-corpus and exact boundary-kernel audit.
- [x] Dependency-closed paper construction.
- [x] Scratch and direct Lean proof of integral response and forced equation.
- [x] Boundary branches, cutoff independence, faithfulness, and source-domain statement.
- [x] Umbrella wiring, isolated leaf build, new-only axiom audit, and passing lint snapshot.
- [x] Current frontier and route-independent ledger update.
