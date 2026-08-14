# Scalar centralizer recurrence energy as a Brown-onset provider

- **ID:** `scalar-centralizer-recurrence-energy-as-brown-onset-provider`
- **Stage:** 5-failed
- **Type:** failed proof architecture / exact scale obstruction
- **Parent:** `../2-fully-proven/centralizer-centered-shortcut-history-recurrence-energy-law.md`
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED]`
- **Date:** 2026-08-14

## Failed claim

After target resolution quotienting supplies replica frame energy `O(1/N)`, a quenched upper bound
on the scalar centralizer-centered recurrence energy should be strong enough to exclude shallow
shortcuts and close Brown first onset.

## Exact killing mechanism

For one sampled time with weight one,

```text
R = ||U(t)z||^2 = ||z||^2.
```

It is independent of time, spectrum, locality, randomness, target packing size, and return
excision.  Consequently no nontrivial theorem can make this scalar source energy `O(1/N)` for a
growing target capacity while retaining a normalized nonzero source.

The problem is not only the singleton endpoint.  Let `q_1,...,q_N` be orthonormal, take sampled
orbit vectors `r_j=q_j`, unit weights, and select target `j` at sample `j`.  Every shortcut
alignment is one and the orbit samples are maximally decorrelated.  Nevertheless

```text
q_bar = N^(-1) sum_j q_j,
||q_bar||^2 = N^(-1),
R = ||sum_j r_j||^2 = N,
<sum_j r_j,q_bar>^2 = 1 = ||q_bar||^2 R.
```

Thus the averaged observer--spectral Cauchy law is exactly saturated by a history consisting
entirely of perfect shortcuts to fresh orthogonal targets.  Diagonal recurrence energy is not a
technical remainder that stronger dephasing can remove.  It is the exact cost of producing a new
observer channel.

## Failed repair -- subtract the diagonal

Removing `sum_j w_j^2 ||z||^2` leaves an off-diagonal signed kernel, not a nonnegative Gram energy.
For the orthogonal example it vanishes even though every sample is a perfect shortcut.  Therefore
diagonal subtraction cannot replace the positive source factor in a universal shortcut
inequality.

## Representation lesson

Scalarizing the adaptive target selector before the temporal positive form confuses two distinct
mechanisms:

1. recurrence or reuse inside one observer channel;
2. production of a fresh observer channel.

Only the first can be controlled by same-channel temporal dephasing.  Brown growth cannot be
reduced to a source-only scalar recurrence-energy ceiling.

## Strongest positive survivor

Partition the history by the selected target before applying Cauchy.  The resulting
selector-partition recurrence law retains same-target temporal pairs and turns fresh-target samples
into explicit diagonal channel-production cost.  Its paper proof is dependency-closed in:

`../2-fully-proven/selector-partition-observer-channel-recurrence-law.md`.

## External and corpus audit

Gram/Cauchy identities, direct-sum Hilbert spaces, frame operators, and cross-Gram matrices are
classical.  The local corpus already warns to retain labels before scalarization in the
phase-twisted replica-action, return-excised incidence-rank, and optimal-design coarea laws.  The
new delta is a correction to the later scalar recurrence-energy frontier: its requested source
bound is mathematically impossible at one time and remains insufficient under perfect temporal
decorrelation.

No claim of standalone mathematical novelty is made for the direct-sum inequality.  Application
priority remains unverified.

