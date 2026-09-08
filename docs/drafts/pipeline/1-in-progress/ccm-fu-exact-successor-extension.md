# CCM-FU: exact successor-energy extension

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], derived extension candidate; unproved
- **Goal:** Uniform complete signed Abel bound and RH; both remain open.
- **Parent:** [reserve extension](ccm-fu-reserve-extension-induction.md).

## Frozen arithmetic question

Write `B=Q_empty(M)` and retain the actual full energies at every processed
prime set. Define

`Psi(P)=max({Q_P} union {Q_(P+q) : q active and unprocessed})`.

At a terminal state this is its actual energy. Every initial state satisfies
`Psi(empty)=B`, since every initial prime contracts. The exact-overlap
recovery theorem admits arbitrarily large states at cutoff12p under Psi
even though their geometric certificate exceeds B. Psi therefore retains
signed interactions lost by the geometric bound.

Freeze the implication: every proper actual state with `Psi(P)<=B` has an
unprocessed prime q with `Psi(P+q)<=B`. If proved at every cutoff, finite
induction would give complete PE4 and SD1 without assuming the terminal
bound. No such arithmetic proof is currently known. This is a derived
proof candidate, not a new primary conjecture or a change to the RH goal.

## Discriminating experiment

Read every saved subset state through cutoff32. Cross-check all energies
between `subset-states.csv` and `defect-reserve-reanalysis.json`; regenerate
no channels for the primary screen. Use the existing tolerance
`1e-12*max(1,B)`. Compute Psi for every state, test every eligible proper
state, and retain every failure with all successor envelopes and the
second successor attaining each envelope. Compute complete reachability
and record whether failures are reachable under Psi. Also count states
admitted by Psi but rejected by the older geometric certificate.

A failure rejects this extension implication without refuting PE4 or RH.
A pass justifies pursuing its exact signed comparison; it is not a proof.
If failures occur, independently reconstruct all failed states and their
first and second successors from the defining divisor defect and Abel sums
at80 decimal digits, retaining the full oriented fields and checking every
classification. Do not change the envelope, budget or tolerance afterward.

Run only on the supplied RunPod host, at most eight worker processes,
one-thread numerical libraries, and a60-second foreground deadline.
Download script, input hashes, output and interpretation to the computation
ledger; remove owned remote files and workers. No larger screen is planned.
The result cannot be predicted from the existing geometric-extension tests:
they omit the additional actual states admitted by the exact envelope.

## Current evidence

The [completed RunPod screen](../2-fully-proven/computations/ccm-fu-exact-successor-extension-2026-09-07/README.md)
examines all8860 saved states. All8176 eligible proper states have an admitted
successor. Psi admits826 states rejected by the geometric certificate, and
every saved cutoff has a complete Psi-admitted path. There are no failures.
All CSV and saved-JSON energies agree within the fixed tolerance. Since no
failure occurred, the prescribed independent80-digit audit was not triggered.
These observations do not establish the all-cutoff implication.

## Exact signed comparison to prove

At an arbitrary retained state, fix distinct unprocessed primes p,q and
split every remaining label into four coordinates `a_R,b_R,c_R,d_R` at
`R`, `R+p`, `R+q`, `R+p+q`. All are literal signed fibres after P, so they
can have either sign. Retain every p,q-free label R. Write

`Delta_p=Q_(P+p)-Q_P=2 sum_R(a_R*b_R+c_R*d_R)`,

`Delta_q=2 sum_R(a_R*c_R+b_R*d_R)`,

`C_pq=sum_R(a_R*d_R+b_R*c_R)`.

Expansion of the complete four-coordinate square gives the exact identity

`Q_(P+p+q)=Q_P+Delta_p+Delta_q+2*C_pq`.

For an admitted P, let `r=B-Q_P`. The missing selection estimate is one
actual p for which `Delta_p+Delta_q+2*C_pq<=r` for **every** other q.
Admission already gives `Delta_p<=r`; it does not bound the mixed C_pq.
The all-cutoff fibre interpolation identifies these terms with the original
field and its actual clipped copies at the p, q and pq quotient scales.
The same processed set must occur in every copy. Replacing C_pq by global
good/defect Cauchy bounds discards the recovery obtained at cutoff12p.

This is the exact unproved source comparison, not a new assumed lemma in
Lean. With two primes left, successor admission also includes the terminal
complete-source square. Thus the implication still has to prove the SD1
endpoint and cannot borrow it as an induction premise. No new generic
receiver or repeated finite screen supplies that arithmetic estimate.

## Proved support-localized bounds

The [localized mixed-interaction theorem](../3-formalized/ccm-fu-localized-mixed-interactions.md)
now controls every already mixed state without a current energy or parity
premise. With `A=2^(max(card(P)-1,0))`, it gives
`|Delta_q|<=(18/25)*A^2*M*floor((M-1)/q)` and
`|2*C_pq|<=(18/25)*A^2*M*`
`(floor((M-1)/(p*q))+floor((M-1)/max(p,q)))`.
Distinct retained labels have distinct prime products, and only the
displayed quotient supports contribute. The first prime difference does
not amplify the original unsigned amplitude interval.

This improves the inverse-prime dependence without discarding the joint
child or cross-child term. It does not prove successor selection: A^2 can
grow along the order, and absolute values lose the signs needed to pay
the remaining cost. Its unconditional positive consequence is a universal
separated-prime two-merger ceiling, paid by the smaller prime's existing
arithmetic reserve. A complete mixed-field reserve comparison remains open.

## Exact small-core cancellation for nonoverlapping pairs

The [small-core theorem](../3-formalized/ccm-fu-small-core-mixed-interactions.md)
proves that when p*q>=M, the full mixed difference E2=2*C_pq is exactly
unchanged on replacing P by its primes below
`max(floor(M/p),floor(M/q))+1`. The joint child is zero, so the parent
field cancels, and both copied children ignore every larger processed
prime. At quotient depth at most L this yields
`|E2|<=(18/25)*4^L*L*M`, independently of card(P) and all current sign
defects. Different quotient windows are allowed.

The growth in total processed-set size is therefore removed from this
sector. The missing simultaneous comparison still includes first gains,
pairs with p*q<M, and unbounded quotient depths. These remain arithmetic
obligations; the fixed-depth mixed bound does not close extension.

## First gains and a concrete selection rule

The [small-core first-gain theorem](../3-formalized/ccm-fu-small-core-first-gains.md)
now gives `Delta_p^2<=(36/25)*4^L*L*M*Q_P` whenever `floor(M/p)<=L`,
with no energy or sign hypothesis. Its child-energy count depends only
on the processed quotient core; the current actual energy Q_P controls
the parent pairing. First-gain magnitudes therefore avoid growth in
card(P) at fixed quotient depth as well. Signs and unbounded depths
still require the missing reserve comparison.

The separately frozen [least-energy selection candidate](ccm-fu-greedy-envelope-extension.md)
asks whether the p minimizing the first gain preserves Psi admission at
every admitted state. Its RunPod screen passes all8176 eligible saved
states through32, including states outside the empty-state greedy path.
No near-minimum failure triggers the prescribed80-digit audit. This is
finite evidence for a concrete choice of p, not a proof of selection.

## Uniform averaging obstruction and persistent source separation

The [successor-average law](../5-failed/ccm-fu-successor-average-reserve.md)
is analytically refuted in Lean at M=22, P={3,7,11,17,19}. This actual state
has Psi(P)+1/250<=B, but the average of its three successor envelopes
exceeds B+1/75. Thus a uniform average over available primes cannot prove
the frozen universal extension statement by staying below the same B.

The positive survivor is also source-certified: prime 2 separates all
nonpositive free fibres from all nonnegative containing fibres. Other
mergers preserve these sign classes, so processing 2 contracts after every
additional subset T not containing 2, including overlapping labels. Prime
2 is uniquely least in immediate energy and its successor remains admitted.
This handles the first averaging obstruction but does not produce an
admissible prime at arbitrary cutoffs. The cutoff-seven final increases
already prevent persistent contraction from holding at every state; the
simultaneous signed comparison above must still allow reserve-paid gains.

## Uniform polynomial source cost and reserve-dependent prime threshold

The [uniform successor transport theorem](../3-formalized/ccm-fu-uniform-successor-transport.md)
now bounds the entire copied child energy by (9/25)M floor(M/p)^2 for every
processed state, regardless of its size or signs. It counts original
coefficients before merging; no fixed quotient depth is needed. The earlier
small-core bound remains useful when that core is sparse.

It gives the full simultaneous comparison
`Psi(P+p)<=Psi(P)+(6/5)floor(M/p)sqrt(M Psi(P))` and additive square-root
cost over every finite prime batch. All second successors, including
overlapping labels, occur in this bound. The actual original diagonal has
the sharper ceiling B<=(9/25)M^2. Consequently a failed successor from a
state with Psi(P)+delta*M^2<=B and delta>0 must have
`delta*p<(18/25)sqrt(M)`.

Thus positive quadratic reserve makes every sufficiently large available
prime safe, uniformly in the current processed state. This does not supply
that reserve, ensure a large prime remains, control its renewal over a full
order, or decide the zero-reserve boundary. Those remain the source-selection
obligations; a growing additive batch cost is not a uniform total budget.

## Source-derived pair reserve and its exact remaining scope

The [changing-core source theorem](../3-formalized/ccm-fu-changing-core-pair-reserves.md)
proves W_(P+p)(Y)=-sqrt(p)W_P(Y/p)+O_P(1), uniformly for every Y>=1.
For even nonempty P, its negative actual residue yields a separated
ratio window containing arbitrarily large prime pairs with a net
coefficient release at least c_P/p. The enlarged core remains even, and
the actual pair releases at least c_P*M^2/p at all sufficiently large M
for that pair. Comparable pairs instead have a net positive cost of
the same order. These are complete source comparisons, with no reserve
or numerical premise.

This supplies a repeatable pair-level source reserve with core-dependent
constants. It does not prove Psi admission: the first merger may exceed
the starting energy, other immediate successors are not bounded by a
pair's endpoint, and selecting arbitrarily large pairs does not include
every omitted prime. A complete proof still needs a common every-cutoff
budget and an exhaustive schedule that pays those costs.
