# CCM-FU: inherited prime-two cost and a positive source circuit

## Exact results

The actual source at cutoffs **2,11,15** has a positive real-weighted circuit
which balances the head and prime-two coordinates and has strictly positive
quadratic covariance. This property survives sufficiently small independent
clipping, with normalization by the exact physical square-root clock.

For an actual block of mutually child-inactive primes whose copied fields
are supported in those two coordinates, the complete current energy and
complete cost of inserting 2 have exact transport laws. Every external
paired fibre remains included. Balanced blocks consume explicit source-square
reserves in both current energy and energy after inserting 2.

These are closed source and transport theorems. A real-weighted circuit
is not a finite prime batch. The results do not construct an exhaustive
prime order, prove the general repair candidate, or prove RH.

## Dependency-closed paper proof: source circuit [PROVED HERE]

Let P0 consist of all primes below 15 except 2. At K<=15 its retained
coordinates are the complete odd and even Mobius-divisor channel sums.
Write V_K=(a_K,b_K) and u_K=V_K/sqrt(K).

Analytic logarithm-series bounds, harmonic Euler-constant corrections and
rational square-root bounds give

`-.273 <= a_11 <= -.271`, `-.050 <= b_11 <= -.047`,
`-.286 <= a_15 <= -.283`, `.055 <= b_15 <= .058`.

The source at 2 has positive head and zero even coordinate. Exact
squarefree support identifies the other four quantities with their full
signed Abel sums; no numerical reconstruction is a proof premise.

Write u_2=(A,0), u_11=(x,y), u_15=(z,w). Then A>0, y<0<w and
`x<-.080<-.078<z<0`. The unnormalized weights

`alpha=(z*y-x*w)/A`, `beta=w`, `gamma=-y`

are strictly positive and have zero weighted vector sum. Their quadratic
covariance is exactly `2*y*w*(x-z)>0`. Divide by their positive sum to
obtain weights summing to one.

For arbitrary nearby vectors U,V,W use the oriented cross-product weights
`cross(W,V)`, `cross(U,W)`, `cross(V,U)`. Their weighted vector sum is
identically zero. At the displayed source all three weights and their
quadratic covariance are strictly positive. Continuity preserves these
four strict inequalities near the source, and normalization preserves the
balances and covariance sign.

The clipped profile uses numerator
`V_K + theta*(V_(K+1)-V_K)` and denominator
`sqrt(K)+theta*(sqrt(K+1)-sqrt(K))`. It is continuous at theta=0.
For theta equal to the actual prime clip weight, the exact clock identity
sets this denominator to `sqrt(M)/sqrt(p)`, with K=M/p. Thus the normalized
clipped vector is precisely the actual copied child divided by sqrt(M).
The clipping theorem concerns real weights for the three actual profiles;
it supplies no integer counts or selected primes.

## Dependency-closed paper proof: inherited cost [PROVED HERE]

At parent state P put H=(a,b)=(F_P(empty),F_P({2})), and define

`D(P)=Q_(P+2)-Q_P-2*a*b`.

The exact prime-merger formula identifies D(P) with twice the sum of all
nonempty pairs of fibres whose labels differ by 2. It includes pairs
carrying every other remaining prime.

For an available prime p let I_p=(x_p,y_p) be its exact interpolated
child field at P. Assume its active source outside 2 is already processed.
Its copied coordinates are `(-sqrt(p)*x_p,-sqrt(p)*y_p)`. Compare the
complete p-merger formula at P and at P+2. Subtracting the receiving
head/two product gives

`D(P+p)=D(P)-2*p*x_p*y_p`.

For a finite block L assume distinct p,q in L satisfy M/p+1<=q, so every
other selected prime is inactive in both adjacent child cutoffs. Child
profiles therefore remain unchanged under partial processing. Put

`X=sum_(p in L) sqrt(p)*x_p`, `Y=sum_(p in L) sqrt(p)*y_p`,
`R=sum_(p in L) p*(x_p^2+y_p^2)`, `C=sum_(p in L) 2*p*x_p*y_p`.

Induction over the actual prime block gives all three identities

`H(P+L)=(a-X,b-Y)`,
`Q_(P+L)=Q_P-2*a*X-2*b*Y+X^2+Y^2-R`,
`D(P+L)=D(P)-C`.

Consequently the complete insertion cost obeys

`Delta_2(P+L)=Delta_2(P)-2*a*Y-2*b*X+2*X*Y-C`.

This formula retains the full receiving error when the block does not
balance exactly. When X=Y=0 it gives the two exact square reserves

`Q_(P+L)=Q_P-R`,
`Q_(P+L+2)=Q_(P+2)-sum_(p in L) p*(x_p+y_p)^2`.

Both energies decrease regardless of the sign of C. Positive C additionally
decreases the insertion cost relative to the new current energy. Thus the
opposite covariance sign of the older 2,7,14 circuit does not invalidate its
linear control or exclude energy contraction; it only has the opposite
effect on this relative cost.

Every other remaining prime q is inactive at each child cutoff: otherwise
the two-coordinate support condition would put q in the processed core.
Its copied profiles are therefore unchanged by inserting q, and the same
balanced block reduces Q_(P+q) by R. Taking the maximum over the current
state and all available successors gives the complete endpoint reserve

`Psi(P+L)+min(R, sum_(p in L) p*(x_p+y_p)^2) <= Psi(P)`.

This statement assumes actual balance X=Y=0. It proves no nonempty exactly
balanced prime batch exists. Approximate batch realization must retain the
displayed receiving errors; existence of real circuit weights does not
discharge that arithmetic requirement.

## Lean sources and validation

- `DivisorTwentyTwoAnalyticBounds.lean`: two new analytic source enclosures.
- `MobiusDivisorTwoDebtSourceCycle.lean`: source identification, normalized
  ordering, positive circuit, clipping stability and exact physical clock.
- `MobiusDivisorInheritedTwoCost.lean`: complete external cost, source-copy
  transport, batch receiving error, both square reserves and full successor
  envelope reserve for a balanced batch.

Both new modules are imported by `GaloisForLFunctions.RHTower`. Scratch
checks passed for the full new source and transport proofs. Final targeted
emission, new-declaration axiom audit and formal lint are being completed.
No umbrella or full build is authorized. The existing `lake build` packaging
audit remains pending because it expands broad stale prerequisites.

The [RunPod diagnostic](../2-fully-proven/computations/ccm-fu-inherited-debt-cycles-2026-09-08/README.md)
selected the new support; all numerical inputs are absent from the proofs.

## Remaining arithmetic obligation

Produce actual prime batches with sufficient reserve and controlled
receiving error uniformly as the processed core grows. The current block
law assumes child inactivity and two-coordinate support; it does not
control general overlapping copies. Then pay every prescribed prime and
every remaining successor while preserving one uniform global budget.
Neither the finite source circuit nor these exact transport identities
discharge that growing-core and exhaustion requirement.
