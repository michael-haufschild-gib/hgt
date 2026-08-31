# Failed route: arbitrary bounded global AIME response existence

Status: retired; unconditional Lean trivialization.

## Retired proposal

Use existence of a bounded, source-adapted single-packet response cancelling cubic AIME on every Xi
fibre as first premise in the HB → shared Ward → RH chain.

## Fatal obstruction

Cancellation is exactly the diagonal condition `(Delta e_q)(q) = -1`. Canonical `Delta = -I`
satisfies it for every seed and Xi copy without arithmetic input. More generally, every canceller is
`-I` plus a bounded zero-diagonal operator.

## Positive survivor

Compactness was not merely a technical inconvenience: successful bounded responses require the
noncompact scalar component `-I`, but that component makes cancellation nonselective. Remaining
RH-bearing premise must be physical two-leg Peierls incidence, not operator existence on one packet.

Formal certificate: `d4HBBoundedGlobalAIMESourceResponseExistenceRouteKilled`.

