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
