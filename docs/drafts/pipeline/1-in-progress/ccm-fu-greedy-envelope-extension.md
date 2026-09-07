# CCM-FU: least-energy choice under exact successor admission

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], derived arithmetic selection candidate; unproved
- **Parent:** [exact successor extension](ccm-fu-exact-successor-extension.md).
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
