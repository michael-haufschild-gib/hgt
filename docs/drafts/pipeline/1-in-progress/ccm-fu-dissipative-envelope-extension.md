# CCM-FU: dissipation compatible with complete successor admission

- Stage: closed; [failed local extension and positive survivor](../5-failed/ccm-fu-dissipative-envelope-extension.md).
- Type: frozen protocol for a source-specific selection candidate, now refuted analytically in Lean.
- Target: exhaustive prime selection under one quadratic budget, hence the signed Abel bound and RH.

## Frozen mathematical question

Write Q(P) for actual retained energy, H(P) for its head, V(P)=Q(P)-H(P)^2,
and Psi(P) for the maximum of Q(P) and all its one-prime successors.
Let B=Q(empty). For every proper actual processed state with Psi(P)≤B,
does there exist an available prime p such that BOTH

`Psi(P+p)≤B` and `V(P+p)≤V(P)`?

This asks whether transverse dissipation and complete successor admission
can be maintained together. The corpus proves neither. Universal V
contraction is already false at cutoff 21; some V-contracting complete
path exists at every stored cutoff through 32. Separate envelope-extension
and V-path passes do not decide their compatibility. A proof of the
displayed extension would give an exhaustive admitted order; initial
admission follows from the proved first-prime contraction law.

The exact candidate inequality retains nonempty mixed products:
`Delta_p V = 2 sum_(R nonempty,p-free) F_R F_(R+p) - F_{p}^2`.
Scalar source repair cannot remove those mixed products.

## Frozen discriminating experiment

Read all 8,860 existing subset energies at cutoffs 1..32. Regenerate no
arithmetic channels for the primary screen and do not enlarge the range.
Recover heads by the previously audited isolated late-prime energy
identity, cross-checking every available late anchor. Keep tolerance
`1e-12 max(1,B)`.

For every admitted proper state, test the displayed conjunction for every
available prime. Retain every failing state and every candidate's V gain
and envelope excess. Also record whether any V-nonincreasing next prime
exists at every proper state (including nonadmitted states), and whether
a complete path from empty satisfies both conditions at every step.
These controls distinguish a transverse trap from incompatibility with
admission or from a failure confined to unreachable states.

Independently reconstruct the defining divisor defects, all literal signed
channels, and relevant fields at 80 decimal digits for the first failure
of each of the two local assertions. Record all candidate gains, envelope
witnesses, coefficients, and sign/magnitude margins. If no failure occurs,
do not run an audit or extend the screen. Finite passes remain guidance.

Run only on the supplied RunPod, eight workers at most, one-thread numeric
libraries, a 50-second internal deadline and a 60-second external timeout.
Download script, inputs' hashes, results and audit; remove owned remote
files and workers. No numerical value enters Lean.

## Interpretation

A failure rejects this stronger dissipation mechanism, not RH or plain
successor extension. Extract the precise surviving source comparison
before retiring it. A pass selects the signed overlap comparison for
proof; it is not a proof of the comparison.

## Current result and positive survivor

The [completed RunPod diagnostic](../2-fully-proven/computations/ccm-fu-dissipative-envelope-extension-2026-09-08/README.md)
finds one failure: M=25, P={2,7,11,13,17,19,23}, with only 3 and 5
remaining. Both choices strictly increase V while strictly decreasing
the complete successor envelope. The independent 80-digit source audit
confirms both signs. The state is reachable under the proposed joint
condition; specially chosen complete joint paths still exist at every
stored cutoff through 32.

The positive survivor is payment by the actual head square: the head is
negative and the other three fibres positive, so both full-energy paths
contract despite unavoidable transverse growth. A general sharp boundary
also survives: for any two remaining coordinates, one next nonempty
energy is at most 3/2 of current nonempty energy; coordinates (1,1,2)
attain that factor. The analytic source bounds, literal arithmetic trap
and sharp general boundary are closed in Lean. The [formal certificate](../3-formalized/ccm-fu-transverse-dissipation-trap.md)
proves admission margin greater than 1/5, both nonempty-energy increases
greater than 1/500, and both envelope decreases greater than 1/250.
Only this universal local extension rule is retired. Plain successor
extension and existence of a specially chosen complete path remain open.
