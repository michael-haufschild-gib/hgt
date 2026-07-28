# Exact causal fracture and complete clock-intervention algebra

- **ID:** `chronometric-causal-susceptibility-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM / NONCOMMUTATIVE ALGEBRA / GREEN RESPONSE / CLOCK TOMOGRAPHY
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalSusceptibility.lean`

## Exact result

For arbitrary elements of a noncommutative ring, if the displayed inverse sides hold,

\[
  E_0P_0=1,\qquad P_1E_1=1,
\]

then

\[
  E_1-E_0=E_0(P_0-P_1)E_1.                                \tag{1}
\]

If the opposite inverse sides also hold,

\[
  P_0E_0=1,\qquad E_1P_1=1,
\]

then the operator change is recovered exactly:

\[
  P_0(E_1-E_0)P_1=P_0-P_1.                                \tag{2}
\]

For a finite clock reporter matrix \(C\) with scalar left inverse \(D\), and an arbitrary family
of algebra-valued curvature reporters \(R_a(J)\) indexed by controlled source setting \(J\), Lean
also proves

\[
  \sum_iD_{ai}\big(C_i(J_1)-C_i(J_0)\big)
  =R_a(J_1)-R_a(J_0).                                     \tag{3}
\]

More generally, every finite weighted source packet is reconstructed:

\[
  \sum_iD_{ai}\sum_Jw_J C_i(J)
  =\sum_Jw_JR_a(J).                                       \tag{4}
\]

Thus all finite differences and finite source-jet stencils transfer through one complete reporter
left inverse. Agreement of state/readout functionals on every ordered clock word at every source
also forces agreement on every ordered curvature word at every source.

## Lean declarations

- `greenElement_fracture`
- `operatorChange_reconstruction_from_greenElement_fracture`
- `greenElement_fracture_and_operatorChange_reconstruction`
- `curvatureDifference_reconstruction`
- `clockReporter_curvatureSourcePacket`
- `curvatureSourcePacket_reconstruction`
- `states_agree_on_curvature_intervention_words`

## Novelty boundary

Equation `(1)` is the second resolvent identity in abstract ring form and is not claimed new.
Equations `(3)`--`(4)` are the source-family lift of existing complete finite reporter tomography.
Their value is dependency closure for the proposed causal-susceptibility law: no algebraic gap
remains between finite clock intervention packets and finite curvature intervention packets.

No physical propagator, clock, curvature observable, stress source, support class, or gravitational
field equation is introduced as an axiom. Those constructions remain external proof obligations.

## Physics bridge still required

1. Construct retarded/advanced reporter Green operators with the inverse identities on the correct
   compact-support domains.
2. Derive a gauge-invariant clock-compass reporter matrix and left inverse.
3. Show allowed conserved matter/stress interventions generate the source packets needed by the
   nonlinear inverse theorem.
4. Prove limits of finite source packets recover the required Fréchet derivatives with stability.
5. Quotient operator recovery by diffeomorphism and gauge rather than treating a gauge-fixed
   representative as observable.

## Log

- 2026-07-28 — exact noncommutative fracture/recovery identities, arbitrary finite source-packet
  reconstruction, and intervention-word transfer checked directly in Lean.
