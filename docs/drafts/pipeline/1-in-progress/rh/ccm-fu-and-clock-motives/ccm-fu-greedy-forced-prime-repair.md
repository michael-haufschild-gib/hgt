# CCM-FU: least-energy repair on the admission boundary

- **Stage:** 1-in-progress.
- **Type:** [BRIDGE], derived selection candidate, not a replacement for RH.
- **Goal:** Choose an admitted endpoint after a prescribed nonisolated prime.
- **Parent:** [prescribed-prime repair](../../ccm-fu-forced-prime-repair.md).

## Frozen statement

At an actual cutoff M, let B=Q_empty and retain the full successor
envelope Psi. Start at any admitted P with Psi(P)<=B and prescribe any
unprocessed prime r. If S=P+r is not admitted, choose q minimizing
Q_(S+q), breaking exact ties by smaller prime. The candidate asserts
Psi(S+q)<=B.

This concerns states immediately outside admission. The existing greedy
candidate concerns states inside admission; the previous forced-prime
screen only establishes finite existence of some repair. Neither
predicts whether this immediate-energy choice repairs S. A failure
rejects this deterministic repair rule, not the existence candidate,
general prime orders or RH.

## Frozen discriminating experiment

Use the complete saved state cubes at cutoffs 1 through 32, cross-checking
the CSV and defect-reserve JSON. Reuse B and tolerance
1e-12*max(1,B); regenerate no channels for the primary screen and do not
enlarge the cutoff range. Examine every forced transition from admission
to nonadmission. Deduplicate equal boundary states S for evaluation but
retain every admitted parent and prescribed prime.

For each S retain every repair alternative, its current energy, full
envelope and maximizing successor. Record the least-energy choice and
every alternative within the original tolerance of its energy. Flag any
near-minimum choice that fails admission. Record the initial first and
second differences and full third difference for each failed minimizing
choice and its offending successor; this identifies the precise budget
term defeating the rule.

Independently reconstruct every flagged boundary state, every supporting
admitted parent, and every one- and two-prime successor from the original
Mobius-divisor defect and Abel sums at 80 digits. Retain all reconstructed
signed fields, margins and alternatives. Resolve the minimizer at this
precision, reporting an unresolved ordering if distinct values differ by
at most 1e-60. No numerical result becomes a Lean premise; any reported
obstruction needs a separate analytic source proof.

Run only on the supplied RunPod host, with up to eight independent cutoff
workers and one-thread numerical libraries. Use a 50-second internal
deadline with pool cleanup and a 60-second external deadline. Download
script, results and hashes into the computation ledger and remove owned
remote files and processes. No larger or repeated scan is scheduled.

## Proof obligation after discrimination

For admitted P, selected r,q and every remaining s, the exact comparison
retains all first and second differences and D3(P;r,q,s). The new
late-block laws determine only a restricted part of its transport. The
candidate needs an actual signed source inequality using the minimum
Q_(P+r+q), not a supplied successful-envelope assumption or a generic
fourth-order identity. A finite pass identifies a concrete rule to attack;
a failure must expose which source interaction it fails to pay.

## Current evidence

The [completed RunPod screen](../../../2-fully-proven/computations/ccm-fu-greedy-forced-prime-repair-2026-09-08/README.md)
finds 2,455 forced exits from admission among all 8,860 saved states. These
give 515 distinct boundary states. The least-energy repair restores full
successor admission in every case; no near-minimum alternative fails. All
parents, alternatives and maximizing successors are retained in the output.
No failure triggers the prescribed independent 80-digit audit. The finite
pass leaves the displayed source comparison open; no larger scan is planned.

## Exact obstacle to transferring a successful repair

Put Delta_q(S)=Q_(S+q)-Q_S and let E2(S;q,s) be the complete mixed
second difference. For distinct available q,t,s, literal subtraction gives

`Q_(S+q+s)-Q_(S+t+s)`
` = Delta_q(S)-Delta_t(S)+E2(S;q,s)-E2(S;t,s)`.

Minimum immediate energy makes only the first difference nonpositive.
Consequently even a separately constructed admitted repair t cannot be
transferred to the minimizer q without controlling the displayed difference
of mixed interactions. The source-local bounds control magnitudes in the
nonoverlapping, bounded-quotient sector; they supply neither this comparison
nor a positive margin at an arbitrary admission boundary. With S=P+r,
transport of those mixed interactions includes the full third difference
at P, including all overlapping children.

Persistent sign separation does give hereditary single-prime contraction
at the previously certified cutoff-22 state. It does not prove that every
boundary minimizer has that separation, or that a contraction pays the
forced prime's existing excess. The general candidate has no paper proof
or Lean theorem. The displayed comparison with a separately successful repair
is one sufficient approach. The necessary target is control of the complete
repaired envelope from the actual admitted parent, uniformly in the processed
core and cutoff.

## Matching contraction fails; a different successor supplies the bound

The [cutoff-seventeen certificate](../../../3-formalized/ccm-fu-seventeen-repair-envelope.md)
has P={3,5,7}, S=P+11 and greedy repair E=S+2. Both Q_E>Q_P and
Q_(E+13)>Q_(P+13), with strict rational margins. Yet
Psi(E)+1/200<=Q_S<=Psi(P). Thus inherited contraction against each matching
parent state is false even on an actual forced exit from admission. The full
envelope can instead use a different admitted parent successor. This is a
closed source witness, not a proof that such a comparison always exists.
