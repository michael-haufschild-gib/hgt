# L-bit replica interaction-fracture law

- **ID:** `lbit-replica-interaction-fracture-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LBitReplicaInteractionFractureLaw.lean`

## Exact law

For a nonempty packet of \(N\) localized binary modes, define the alternating
integer character on its complete configuration cube by
\[
  \kappa(x)=\prod_{i=1}^{N}(-1)^{x_i}.
\]
Then \(\kappa\) is balanced, its exact minimum fidelity-replica height is
\[
  h(\kappa)=2^{N-1},
\]
and for every l-bit Hamiltonian
\[
  E_J(x)=\sum_{S\subseteq I}J_S\chi_S(x)
\]
its spectral detuning is
\[
  \boxed{
  \sum_x\kappa(x)E_J(x)=2^N J_I.}
\]

Consequently, the complete-cube recurrence relation survives exactly when
the interaction coupling all \(N\) modes is absent:
\[
  \operatorname{ResolvedReplicaDetects}
  \bigl(E_J,2^{N-1},\kappa\bigr)
  \iff J_I=0.
\]
Equivalently, \(J_I\ne0\) fractures that relation, and no lower replica order
can even realize its character.

This gives an exact operational bridge
\[
  \text{localized interaction order}
  \longleftrightarrow
  \text{Boolean-cube relation fracture}
  \longleftrightarrow
  \text{minimum replica depth}.
\]

## Exact finite-horizon law

For every averaging horizon \(A\), the same character has the exact response
\[
  \boxed{\mathcal W_I(A)=\operatorname{sinc}(A\,2^N J_I).}
\]
At every \(A\ne0\), \(\mathcal W_I(A)=1\) exactly when \(J_I=0\). If
\(J_I\ne0\), the calibrated positive horizon
\[
  A_*=\frac{\pi}{|2^N J_I|}
\]
makes the response exactly zero. A lower bound
\(\delta\le |2^N J_I|\) therefore guarantees
\[
  A_*\le \frac{\pi}{\delta}.
\]
The absent and present responses are separated by unit complex distance at
\(A_*\); consequently measurements with adversarial complex error strictly
below \(1/2\) cannot coincide.

This closes finite-horizon observability for the exact l-bit fixed point. It
does not establish novelty of inverse-coupling-time detection: that scaling,
noise-robust multi-spin detection, and experimental three-body Ramsey
estimation already occur in the literature. The candidate new content is the
single exact chain from cube fracture through minimum recurrence-replica
height to finite-horizon response.

## Scope

The theorem is exact for l-bit fixed-point Hamiltonians. It identifies the
top-order coefficient on each finite localized mode packet. It does not
transfer the conclusion to a generic finite-range random Anderson or
microscopic MBL Hamiltonian. It now provides an exact noisy finite-time
discriminator inside the fixed-point model, but not a physical-spin/l-bit
dressing theorem, sample-complexity bound, SPAM analysis, or experimental
advantage over existing Hamiltonian-learning and interferometric protocols.

## Formal declarations

- `lbitFullCubeCharacter_balanced`;
- `lbitFullCubeCharacter_positiveMass`;
- `lbitFullCubeCharacter_detuning`;
- `lbitFullCubeCharacter_minimumReplica`;
- `lbitTopInteraction_relation_iff`;
- `lbitTopInteraction_fracture_iff`;
- `lbitNoninteracting_temporalRank_le`;
- `lbitTwoMode_noninteracting_rectangleRelation`;
- `lbitTwoMode_interaction_fractures_rectangle`;
- `lbitFullCube_finitePhaseResponse`;
- `lbitFullCube_finitePhaseResponse_eq_one_iff`;
- `lbitTwoMode_finitePhaseResponse`;
- `lbitFullCube_calibratedPhaseResponse`;
- `lbitFullCube_calibratedHorizon_le`;
- `complex_measurements_separated_of_error_lt_half`;
- `lbitFullCube_measurementsSeparated`.

## Verification

Target source compilation with cached output passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitReplicaInteractionFractureLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitReplicaInteractionFractureLaw.olean
```

Axiom audit of all load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
