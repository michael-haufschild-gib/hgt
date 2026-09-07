# CCM-FU: complete reserve-extension induction

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] / direct proof attempt for frozen PE4
- **Parent:** [adaptive prime ceiling](ccm-fu-adaptive-prime-ceiling.md)
- **Primary goal:** Complete source bound, CCM-FU boundary transport, RH.

## Attempted complete proof

Write `Phi(P)=Q_P+2 sqrt(G_P D_P)` for the literal source at one cutoff,
and `B=Q_empty`. Initial parity gives `Phi(empty)=B`. The proved merger
estimate gives `Q_(P+p)<=Phi(P)` for every unprocessed prime p.

The missing induction step proposed here is: every proper P with
`Phi(P)<=B` has an unprocessed p such that either P+p is complete or
`Phi(P+p)<=B`. If established for every actual cutoff and state, induction
on the number of remaining primes constructs a complete PE4 order; its
terminal energy is bounded by the predecessor's certificate. This does
not assume a bound for the complete source.

This is a derived proof strategy, not a replacement or weakening of PE4.
The existing arbitrary positive-cube obstruction prevents deriving it from
unsigned positivity alone. The actual arithmetic field and its signed
overlaps must enter. A failure of this sufficient extension property does
not refute existence of a complete PE4 path.

## Frozen diagnostic

Use all 8860 saved states through cutoff32 in
`defect-reserve-reanalysis.json`. Do not regenerate channels, heads,
energies, or existing complete paths. Retain the input's original tolerance
`1e-12*max(1,B)` and every state, including degenerate cutoffs.

Test the exact local extension property above at every certified proper
state. Separately test the stronger homogeneous descent assertion
`min_p Phi(P+p)<=Phi(P)` over every proper state. For any failure, retain
all outgoing Q, G, D and Phi values, and whether P is reachable from the
empty state through certified predecessors. Do not select a larger budget
after a failure. Existing existence results do not predict whether all
certified states extend; this test distinguishes an inductive invariant
from a set that merely contains some successful paths.

Run only on RunPod with cutoff jobs distributed over at most eight workers,
a 60-second foreground limit, and no background jobs. Save exact script,
input hash, output and interpretation under `2-fully-proven/computations`.
Numerical evidence supplies no Lean premise. A passing finite test leaves
the all-cutoff induction open; a failing numerical witness must be
analytically verified before it is called a formal obstruction.

## Bounded hostile extension

The saved-data test passes all 7350 certified proper states, while the
stronger homogeneous descent assertion fails at 975 states. Its first
failure is M=7, P={2}. The all-cutoff extension statement is unchanged.

Before investing in its proof, test every subset state at every integer
cutoff33..64. Reuse the existing defect/unit-clock table; do not recompute
that source. Derive dilated coefficients by the exact clipped formula and
obtain all oriented fibres by subset summation with literal Möbius signs.
Check the original diagonals against the existing greedy summary, and
independently reconstruct every reported witness and each of its successors
by direct prime merging. Retain the same tolerance and extension predicate.
Use at most eight workers and a 60-second foreground deadline. This larger
test targets an unproved induction step, not another greedy pass. Record
all failing states and all outgoing values; a failure does not retire PE4.

## Present evidence and exact proof gap

The [saved RunPod outputs](../2-fully-proven/computations/ccm-fu-reserve-extension-2026-09-07/README.md)
contain no extension failure in either range. The extension covers all
1746944 subset states at cutoffs33..64, including 999880 certified proper
states. This is numerical evidence for the same induction statement, not
an all-cutoff proof or a Lean premise.

For a proposed next prime q, write `a_R=A_P(R)` and
`b_R=A_P(R+q)` for oriented coordinates on q-free labels. Then
`A_(P+q)(R)=a_R-b_R` and

`Q_(P+q)=Q_P-2 sum_R a_R b_R`.

If `r_P=(B-Q_P)/2`, the exact required comparison is

`sqrt(G_(P+q) D_(P+q)) <= r_P + sum_R a_R b_R`

for at least one unprocessed q, unless that merge completes the order.
The current certificate only gives `sqrt(G_P D_P)<=r_P`. It does not bound
the newly redistributed positive and negative parts. Replacing r_P by
`sqrt(G_P D_P)` would demand homogeneous certificate descent, which fails
already in the saved cutoff-seven source. Bounds for the first merger's
defect apply to oriented input and cannot be iterated after that hypothesis
is lost.

## Why the available local channel bounds do not close the induction

The following exact algebraic model tests the attempted proof, not the
literal arithmetic source. On a four-coordinate Boolean cube set
`A(R)=3+(-1)^card(R)`. Its positive values are 4 and 2, so every directed
child/parent ratio is at most two. Its initial energy is 160. After k>=1
distinct coordinate differences the surviving field is
`2^k*(-1)^card(R)`: the first difference removes the constant, and each
later difference doubles the parity part. For k=1,2,3 its energies are
32,64,128, and its geometric certificates are 64,128,256 respectively.
After k=4 its sole value is 16 and energy is 256.

Thus every first-prime reserve and every two-prime original-energy bound
holds in this model. Nevertheless every two-prime state is certified and
has no certified successor: the next state is still nonterminal and has
certificate256>160. Positivity, factor-two comparisons and initial reserve
estimates together do not imply the missing induction. These explicit
counts are paper algebra, not a new Lean certificate; no actual-source
claim or route retirement follows.

The positive information in this model is the exact separation of a
constant background from a higher-order parity component: all subsequent
growth belongs to that component. The source argument must control such
joint interactions in the actual arithmetic field. The common-head
identity alone supplies no bound on them. No replacement potential,
source-specific extension proof, complete uniform energy bound, or RH
proof is claimed here.
