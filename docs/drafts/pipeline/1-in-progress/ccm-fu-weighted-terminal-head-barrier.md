# CCM-FU: weighted terminal head barrier

- Stage: 1-in-progress.
- Type: [BRIDGE], derived source obstruction and amplitude law.
- Parent: [fixed-weight path candidate](ccm-fu-weighted-head-dissipation.md), unchanged and open.
- Goal: identify whether prepared small-head terminal cores can support a uniformly coercive complete path.

## Frozen derived target and paper proof

For a scalar head h, absorbed leaf a and positive weight alpha, weighted
energy descent means `alpha(h+a)²≤alpha h²+a²`. If |h+a|>|h|, then h+a
has the sign of a and the inequality implies

`|h+a|≤((1+alpha)/(2alpha))|a|`.

Thus along any decreasing weighted scalar order with leaf magnitudes at
most A, every head is bounded by
`max(|initial head|,((1+alpha)/(2alpha))A)`.
The coefficient is sharp for one same-sign scalar merger. This is an
amplitude invariant, stronger than the bound on total weighted energy.

In the literal terminal field every remaining label is a singleton and
each insertion removes its square. The bound therefore transports to
every complete terminal prime order. In particular, the existing prepared
cores with head O(sqrt M) and uniformly bounded quotient leaves can only
complete monotonically at fixed positive alpha if the complete signed
sum itself is O(sqrt M).

The next source target is to exclude that smaller bound unconditionally.
The corpus's twice-Abel kernel has unit difference
O(n^(-Re(s)-3/2)). Prefix growth O(sqrt n) would make its candidate
Dirichlet sum holomorphic throughout Re(s)>0. For the actual source
coefficients Lambda(n)-1 plus the Euler edge at n=1, this sum agrees on
the safe half-plane with `-zeta'/zeta-zeta+2gamma`. Pole clearing and
analytic continuation would give a first-order analytic differential
equation for the pole-filled zeta on the open critical strip. Its known
nontrivial zero contradicts zero propagation and nonvanishing there.
This uses unconditional source identities and zero existence, not RH.

A fixed-grid version additionally needs interpolation between neighboring
grid points. The finite Abel increment and a linear bound on the actual
Chebyshev defect would supply O(sqrt M) error over each fixed-length gap.
That transfer is a separate obligation, not assumed from cofinality.

## Scope

No computation is planned: the proposed amplitude and analytic-continuation
implications are determined by reasoning from the corpus. Any obstruction
must retain the sharp amplitude law and actual terminal transport as its
positive survivor. Failure of completion through these prepared cores
would not refute the main path claim; a complete path may retain overlapping
primes until its head is larger.

## Current state

Relevant scalar merger, terminal source transport, twice-Abel kernel,
nontrivial zeta-zero existence and analytic ODE zero-propagation theorems
are present in the corpus. The weighted amplitude law and strengthened
square-root-prefix continuation are not yet formalized. No RH proof is
claimed. The frontier map remains read only.
