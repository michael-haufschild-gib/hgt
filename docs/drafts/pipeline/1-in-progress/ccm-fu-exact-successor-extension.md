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
