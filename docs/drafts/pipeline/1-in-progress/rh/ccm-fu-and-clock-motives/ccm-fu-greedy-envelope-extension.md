# CCM-FU: least-energy choice under exact successor admission

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], derived arithmetic selection candidate; unproved
- **Parent:** [exact successor extension](../../ccm-fu-exact-successor-extension.md).
- **Goal:** Complete signed Abel bound and RH remain open.

## Frozen selection question

Let `B=Q_empty` and `Psi(P)=max(Q_P,max_q Q_(P+q))`, with q ranging
over active unprocessed primes. At every proper actual state satisfying
`Psi(P)<=B`, choose p minimizing `Q_(P+p)`, breaking ties by smaller prime.
Does this specific p satisfy `Psi(P+p)<=B`?

This would close the exact successor-extension step with a concrete
selection rule. Its missing inequality is
`Delta_p+Delta_q+E2(P;p,q)<=B-Q_P` for every other q. The rule minimizes
the actual first gain, retaining its signed parent/child pairing. The
small-core theorem controls only some mixed E2 terms and does not imply
this selection statement.

The existing greedy screen starts from the empty state. The present
question includes every admitted state, including states that greedy
processing never visits. Neither the earlier existential extension pass
nor the empty-state greedy pass determines the answer. A failure rejects
this stronger selection rule, not existential extension, PE4G or RH.

## Frozen discriminating experiment

Use every stored subset state through cutoff32, cross-checking energies
between the original CSV and saved defect-reserve JSON. Regenerate no
channels for the primary screen and do not enlarge the cutoff range.
Keep tolerance `1e-12*max(1,B)` for energy admission.

For every admitted proper state compute the least-energy choice and its
full successor envelope. Retain every failure, all alternative choices,
the second prime attaining each envelope, each first gain, each relevant
mixed difference, and reachability through admitted states. Record
whether a failure occurs on the deterministic greedy path from empty.

If any choice within tolerance of the minimum has a failed envelope,
independently reconstruct that state and all its first and second
successors from the defining divisor defects and Abel sums at80 digits.
Resolve the least-energy choice with those direct values, and retain all
signed fields and margins. Thus floating-point near ties cannot silently
select the decisive prime. Audit every flagged state, not a sample.

Run only on the supplied RunPod host, with at most eight workers,
one-thread numerical libraries and a60-second foreground deadline.
Download and hash script, inputs and results in the computation ledger;
remove all owned remote files and processes. A finite pass supplies a
selection target for proof, never a numerical premise in Lean. No larger
repeat screen is planned.

## Closed source comparison

For `N>=M/p+1`, let S be P restricted below N and let
`J_p=sum_R F_P(R+p)^2` over p-free labels. Exact quotient localization
and product support give
`J_p<=(9/25)*4^(max(card(S)-1,0))*M*floor((M-1)/p)`.
The full signed gain is `Delta_p=2 sum_R F_P(R)F_P(R+p)`.
Cauchy--Schwarz on this actual pairing therefore yields
`Delta_p^2<=(36/25)*4^(max(card(S)-1,0))*M*floor((M-1)/p)*Q_P`.
At quotient depth at most L, its right side is at most
`(36/25)*4^L*L*M*Q_P`. This removes total processed-cardinality growth
from first-gain magnitude, leaving current energy explicit. It supplies
no sign and does not prove the least-energy extension candidate.

## Current evidence

The [completed RunPod screen](../../../2-fully-proven/computations/ccm-fu-greedy-envelope-extension-2026-09-07/README.md)
reads all8860 states. All8176 eligible proper states preserve the envelope
under the least-energy choice. No near-minimum candidate fails, so the
prescribed independent80-digit audit is not triggered. The original
energy tables agree within the fixed tolerance. This finite result does
not prove the candidate; no larger repeat screen is planned.

The [small-core first-gain theorem](../../../3-formalized/ccm-fu-small-core-first-gains.md)
formalizes the displayed source bounds. Together with small-core mixed
localization, it removes full processed-cardinality growth from first
and nonoverlapping mixed gains at fixed quotient depth. It does not
supply the signed simultaneous comparison needed for greedy selection.

## Analytically certified choice at the first averaging obstruction

The [uniform successor-average counterexample](../../../5-failed/ccm-fu-successor-average-reserve.md)
has M=22 and P={3,7,11,17,19}. Its mean successor envelope exceeds B+1/75,
even though Psi(P)+1/250<=B. The unique least-energy prime is 2, and Lean
proves that this choice preserves admission. Its mechanism is persistent
sign separation: every 2-free fibre is nonpositive, every 2-containing
fibre nonnegative, and all other mergers preserve that separation.
Therefore prime 2 contracts after every additional subset of other labels,
including the live overlapping pair. All claims use analytic source bounds.

This certifies a concrete prime-sensitive mechanism where uniform averaging
fails. It does not establish that the least-energy choice always has such
separation, nor that it always preserves admission. States with unavoidable
positive gains still require the actual reserve comparison.

## Uniform cost beyond fixed quotient depth

The [uniform transport theorem](../../../3-formalized/ccm-fu-uniform-successor-transport.md)
proves `Psi(P+p)<=Psi(P)+(6/5)floor(M/p)sqrt(M Psi(P))` for every processed
state, with no sign or fixed-depth hypothesis. Its child-energy bound counts
original coefficients before aggregation and avoids exponential growth in
the processed quotient core. Square-root costs add over arbitrary finite
batches. With reserve delta*M^2, any rejected next prime must satisfy
`delta*p<(18/25)sqrt(M)`, using B<=(9/25)M^2 for the actual initial diagonal.

This gives a source-certified range in which the least-energy choice could
still fail. It neither proves that this choice leaves that range nor supplies
a uniform positive reserve along its full path. The frozen greedy candidate
remains open.
