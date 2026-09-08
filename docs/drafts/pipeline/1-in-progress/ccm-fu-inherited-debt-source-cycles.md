# CCM-FU: source cycles and inherited prime-two debt

- **Stage:** 1-in-progress.
- **Type:** [BRIDGE], source-control mechanism; no RH theorem claimed.
- **Goal:** Control the complete cost of a prescribed small prime while preparing its retained field.

## Exact question

At a fixed cutoff, the cost of inserting 2 includes every pair of fibres
whose labels differ by 2. Controlling only the empty and `{2}` coordinates
does not control pairs carrying other remaining primes. For a large
available prime p whose copied profile is supported in these two retained
coordinates, processing p moves that retained vector by minus its copied
profile and removes that profile's pair product from the external cost of
inserting 2. The latter signed change must be retained.

Write V_K=(a_K,b_K) for the actual odd and even Mobius-divisor channel sums
at cutoff K, and u_K=V_K/sqrt(K). A packet at p near M/K has retained
displacement -sqrt(M)*u_K and removes prime-two cost M*2*u_K.1*u_K.2,
up to its exact clipping correction. A positive zero-mean source circuit
therefore controls a different quantity from a linear spanning cone:

`w_K >= 0`, `sum w_K = 1`, `sum w_K*u_K = 0`,
`sum w_K*2*u_K.1*u_K.2 > 0`.

The existing 2,7,14 circuit has the opposite quadratic orientation.
Indeed write u_2=(A,0), u_7=(x,y), u_14=(z,w), with A>0, x,y,z<0<w.
Its unnormalized positive weights are ((z*y-x*w)/A,w,-y). Their
quadratic sum is `2*y*w*(x-z)`. Exact reflection gives w=-x and
`z-x=S_14/sqrt(14)`, where the complete signed source S_14 is strictly
negative by the existing analytic source bounds. Thus the quadratic sum
is negative. This algebraic observation has not been added as a separate
Lean theorem. It does not exclude energy contraction: the block also
consumes source squares, as the complete transport law below shows.

## Frozen discriminating experiment

Reuse all 511 saved profiles at K=2..512 from
`../2-fully-proven/computations/ccm-fu-coupled-prime-packets-2026-09-07/profiles.csv`
(SHA256 `a8c93dfaec636b6f993f1e676e1e9ea744b699273cd66b0644afca4ffee8393d`).
Do not recompute or extend the channel screen. These odd/even profiles
are simultaneously realized by the common core consisting of every prime
below 513 except 2; for K>15 they are not profiles of the original core
of primes below 15 except 2.

Solve the finite linear program maximizing the displayed quadratic sum
under the displayed three equality constraints and nonnegative weights.
Retain the optimizer, support, residuals, dual and solver status. A strict
positive optimum identifies a debt-removing zero-displacement source
cycle; a nonpositive optimum only excludes cycles in this saved finite
profile set. Linear spanning alone does not predict the answer.

Independently reconstruct each selected support profile from the original
divisor defect and Abel sums at 80 decimal digits, with separate cutoff
workers. For a three-point support, recover positive circuit weights by
cross products and normalize them; retain all high-precision coordinates,
weights, balance residuals and quadratic margin. Report near-degeneracy
if any sign or margin is within 1e-60. If the optimizer has a degenerate
support or its high-precision margin is nonpositive, report it without
searching a larger range. Numerical output never enters a Lean proof.

Run only on the supplied RunPod, at most eight independent audit workers,
one-thread numerical libraries, 50-second internal and 60-second external
limits. Download script, output and hashes into the computation ledger;
remove owned remote files and processes. No larger or repeated screen.

## Current result

The [completed diagnostic](../2-fully-proven/computations/ccm-fu-inherited-debt-cycles-2026-09-08/README.md)
finds a positive circuit at **2,11,15**. A separate
[source and transport proof](../3-formalized/ccm-fu-inherited-two-cost-source-cycle.md)
establishes its covariance sign analytically, stability under independent
clipping, exact physical normalization, and the complete actual batch laws.
No numerical result supplies a proof premise.

If X,Y are the two receiving displacements and C is the sum of copied
signed covariances, then

`Delta_2(P+L)=Delta_2(P)-2*a*Y-2*b*X+2*X*Y-C`.

For a balanced block the current energy decreases by
`sum p*(x_p^2+y_p^2)` and its prime-two successor decreases by
`sum p*(x_p+y_p)^2`. Hence either covariance sign can contract both
energies; positive covariance additionally reduces their difference.
This is why a cost-only sign obstruction cannot retire the older circuit.
Every other remaining successor loses the same current-state square reserve,
so a balanced actual block contracts the full successor envelope by the
smaller of the two displayed reserves. This endpoint theorem does not assert
existence of an exactly balanced finite prime batch.

## Remaining proof obligation

The full inherited-cost identity and an actual prescribed-prime repair
producer are proved. Exhaustion still requires renewal after source windows
are used, control of prescribed primes with unbounded quotients, and the
overlapping child profiles that arise there. Fixed quotient windows have
limited prime capacity; their existence does not alone pay every future
change of core under a uniform global budget.

## Current actual producer

Exact balance is no longer required. With E=Psi(P), D=|X|+|Y| and the two
square reserves R,T above, the Lean transport theorem proves

`Psi(P+L)+min(R,T) <= E+2*sqrt(E)*D+D^2`.

Each parent successor's receiving coordinate is bounded by sqrt(E).
Prime 2 uses the merged displacement X+Y; other successors use X,Y.
The bound has no processed-cardinality factor.

The [actual repair theorem](../3-formalized/ccm-fu-prescribed-window-repair.md)
chooses fixed windows at quotients 2,7,14 and M=14(b+1)N. For every C>0,
there is A>0 such that, for all sufficiently large N, every core containing
P0, excluding 2, leaving those windows unused, and satisfying E<=C*M^2
admits any prescribed available prime q with 15<=q<M and M/q<=14:

`q in L`, `L subset {q} union windows`,
`card(L)=ceil(A*sqrt(M))+1`, `Psi(P+L)+M <= Psi(P)`.

The threshold and A are uniform in P and q. Start with q's normalized
copied vector and greedily add actual unused source primes. Directional
control bounds total receiving displacement by H*sqrt(M), while every
added source supplies at least d*M to both square reserves. Window count
divided by sqrt(M) tends to infinity, so only square-root many primes are
needed to pay the error. No rounding of circuit weights and no numerical
premise enter this construction. Its endpoint admission does not establish
an exhaustive order, renewal of the untouched-window condition, or control
of unbounded quotients.

## Prescribed prime-two front

The frozen [prepared-core diagnostic](../2-fully-proven/computations/ccm-fu-prepared-two-envelope-2026-09-08/README.md)
finds a numerical failure of pointwise envelope monotonicity for inserting
2 at M=84, P=P0. Current energy decreases, but the successor at 17 raises
the full envelope. This is diagnostic evidence, not a Lean counterexample.
The original diagonal budget is not violated in the scanned range.

[BRIDGE target] Suppose all remaining primes other than 2 have M/q<=14,
while the source windows stay unused and E=Psi(P)<=C*M^2. Inserting 2
already has current energy at most E. The existing quotient transport law
therefore bounds its new full successor envelope by

`E + 17*sqrt(M)*sqrt(E)`.

This is at most E+17*sqrt(C)*M^(3/2). A balanced actual source batch from
2,7,14, chosen at P, remains a scalar-displacement batch after inserting
2: its two copied coordinates merge, and its removed reserve is
`sum p*(I_p,0+I_p,2)^2`. The existing common positive square reserve and
window capacity can pay both the new-front cost and receiving error with
ceil(A*sqrt(M)) source primes. Target a batch containing 2 with full
endpoint envelope at most E-M. Constants and threshold must be uniform
in the processed core. This handles an unbounded quotient at the prescribed
prime itself, but assumes every other remaining quotient is bounded; it
does not settle the general overlapping front or exhaustive processing.
