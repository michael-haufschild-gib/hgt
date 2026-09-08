# CCM-FU: prescribed-prime repair under the exact successor envelope

- **Stage:** 1-in-progress.
- **Type:** [BRIDGE], derived proof candidate, not a replacement RH conjecture.
- **Goal:** Force exhaustive prime inclusion under one every-cutoff energy budget.
- **Parent:** [exact successor extension](ccm-fu-exact-successor-extension.md).

## Frozen statement and motivation

At a fixed actual cutoff M let B=Q_empty(M) and
Psi(P)=max(Q_P,{Q_(P+q): q unprocessed}). For every proper state admitted
by Psi(P)<=B and every prescribed unprocessed prime r, either P+r is
admitted or there is another unprocessed q with Psi(P+r+q)<=B.

Admission already pays the first energy Q_(P+r). Restoring admission in
at most two steps would permit prescribed-prime coverage in blocks,
without presuming a complete source bound. The existing extension and
least-energy screens assert existence of some good next prime. They do
not predict this all-prescribed-prime repair statement. The newly proved
asymptotic even-core pair reserves likewise do not include a prescribed
omitted prime or supply this every-cutoff comparison.

## Frozen discriminating experiment

Read all saved subset states at all integer cutoffs through 32 from
subset-states.csv and defect-reserve-reanalysis.json. Cross-check the
complete energy cubes between these two inputs. Reuse the original
budget and tolerance 1e-12*max(1,B). Regenerate no channels for the screen.
Test every admitted proper state and every prescribed remaining prime;
retain every failure and every second-prime alternative with its exact
successor-envelope witness.

Independently, compute the minimum number of energy-safe mergers needed
to return to an admitted state after the prescribed first merger. This
is a diagnostic of the failure mechanism, not a relaxed primary claim.
Each intermediate Q must meet the same B. Mark infinite distance if no
such path exists. Record whether each failed parent is reachable from
empty through admitted states, and retain a shortest repair path when
one exists. Do not change the budget, tolerance, state family or two-step
claim after observing failures.

For every failed comparison, independently reconstruct all required
source fields and their energies from the defining Mobius-divisor Abel
sum at 80 decimal digits. Recheck parent admission and rejection of every
one- or two-step repair. Deduplicate reconstructed fields within a cutoff,
but omit no failure or alternative. Retain these fields and the complete
failure list in the output.

Execute only on the supplied RunPod host with at most eight cutoff
workers, one-thread numerical libraries, a 50-second internal alarm and
60-second foreground deadline. Download script and results; record hashes
and interpretation under 2-fully-proven/computations. Remove owned remote
files and processes. No computed value enters Lean. A pass remains finite
evidence; a numerical failure needs a separate analytic proof before being
called a formal obstruction. No larger scan is scheduled.

## Current evidence and exact gap

The [completed RunPod screen](../2-fully-proven/computations/ccm-fu-forced-prime-repair-2026-09-08/README.md)
finds no failure in 39,220 prescribed-prime choices across all 8,860 saved
states. One merger restores admission in 36,765 cases and two in 2,455.
No longer or impossible repair occurs. This is finite numerical evidence
for the original two-step statement, with no changed budget or state
family and no Lean premise.

For fixed prescribed r and prospective repair q, admission of P+r+q
requires every Q_(P+r+q+s)<=B as well as its own energy. Thus the source
comparison contains the complete three-prime interaction, not only the
previously controlled two-prime release. No all-cutoff bound for that
interaction or prescribed-prime repair theorem is established here.

## Pair reserve compatibility with a prescribed prime

The coefficient-level attack retains both source states P and P+r.
For nonempty P and primes q>=p outside P, Lean proves the
following quantitative profile:

p*(kappa_(P+p+q)-kappa_P)
 =2*rho_P*(p/q)^(3/2)*W_P(q/p)+O_P(p^(-1/2)),

uniformly over all q>=p. The first prime's complete contribution and the
change of both density factors occur in the error; neither is discarded.
Apply the same formula to P+r to measure the change of the prescribed
prime's debt kappa_(P+r)-kappa_P.

For even P, W_P has a negative tail while W_(P+r) has a positive tail.
Thus sufficiently separated large pairs can release reserve before r but
increase energy after r. An exhaustive argument cannot count the former
credit without its change in the future required state. Lean proves the
simultaneous two-state comparison in one common ratio window and supplies
such pairs beyond every lower prime cutoff. This constrains those pairs;
it does not reject general prescribed-prime repair. The exact statements
and dependency-closed proof are [formalized here](../3-formalized/ccm-fu-prescribed-prime-pair-reserves.md).

## Direct inclusion of a prescribed large prime

The existing even-core reserve window also has an inverse use. If every
sufficiently large pair with L*p<=q<=(L+1)*p releases c/p, fix q=r first.
The prime interval theorem, applied at r/(L+1) with relative width 1/L,
supplies p strictly between r/(L+1) and r/L for every sufficiently large
r. Both primes then meet the original window and all finite exclusions.
Thus every sufficiently large prescribed prime, rather than merely an
unbounded selection of primes, belongs to a reserve-producing pair.
The same final core can be reached with r first, since insertions commute.

Lean proves this universal prescribed-prime inclusion, preservation of
even cardinality and a positive quadratic reserve for actual energies
at every sufficiently large cutoff for the chosen pair. Its prime
threshold depends on the current core. It does not yet cover a prescribed
prime below that threshold, pay the first intermediate merger, or give
one cutoff threshold through an exhaustive sequence.

## Closed three-prime and intermediate-block components

The [three-prime transport theorem](../3-formalized/ccm-fu-three-prime-late-block-transport.md)
now identifies the complete third difference with the four complementary
products in every eight-fibre block. For an arbitrary starting core,
consuming a late-prime block changes this difference by exactly twice
the signed block mass times its retained triple fibre. The difference
is unchanged outside the joint triple support. At the original core,
this gives an exact unsigned-mass threshold for preserving the negative
third-order margin, including active overlaps.

Lean also proves Psi(P+R)<=max(Psi(P),Psi(P+L)) for every subset R of an
unprocessed late-prime block L. This pays all intermediate successor
envelopes from the two endpoint envelopes without accumulated per-step
cost. Selecting an admitted endpoint and handling nonisolated prime
mergers remain the unproved repair obligations.
