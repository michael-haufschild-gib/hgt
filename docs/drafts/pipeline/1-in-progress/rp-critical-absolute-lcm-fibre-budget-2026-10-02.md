# RP: absolute budgets for clipped LCM fibres

- **ID:** RP-45-absolute-LCM
- **Stage:** 1-in-progress
- **Type:** CANDIDATE obstruction with positive arithmetic survivor
- **Source:** RP-45 in rp-unconditional-history-floor-loop-2026-10-01.md
- **Goal unchanged:** unconditional RH through the complete signed RP floor.

## Candidate being tested

Can complete LCM-fibre regrouping make the unpaid paired source absolutely
admitted at every critical damped weight? This would permit estimating each
fibre separately after shared-cutoff integration. No such admission is assumed.

Write a_M(d)=mobiusDivisorDilationChannel M d and use the existing literal
finiteLcmPairFibre over d,e in Icc1 M. Define V(M) as the sum of absolute
values of these fibres for lcm labels greater than M. The target test is
summability of V(4N)/((4N)^3*sqrt(4N)), a critical damped weight.

## Corpus-grounded paper argument under audit

Let L_M be the primes in(M/2,M], T_M their unsigned channel mass, and
Q_M their ordered off-diagonal signed pair sum. Both individual channels
are negative on these prime labels, so Q_M=T_M^2-D_M, where D_M is the
late-prime diagonal. The existing full signed diagonal is at most722*M^2,
and D_M is a nonnegative sub-sum of it.

For M=4N and N>=2, distinct p,q in L_M have pq>M. Any active positive
integer pair d,e<=M with lcm(d,e)=pq is either(p,q) or(q,p): the other
divisors are1 and pq, and a pair involving1 would require the inactive pq.
Thus the entire fibre, not just a selected term, equals2*a_M(p)*a_M(q)>=0.
Regrouping the prime-pair sum by these complete fibres gives Q_M<=V(M).

The corpus's quantitative late-prime floor is

    T_(4N) >= N*sqrt(N)/(80*log(2N)) eventually.

Since log(2N)/N^(1/4) tends to zero, eventually
T_M>=2*M*sqrt(sqrt(M)). Also sqrt(M)>=722 eventually. Consequently

    Q_M = T_M^2-D_M >= M^2*sqrt(M) eventually,
    V(M)/(M^3*sqrt(M)) >= 1/M.

The harmonic comparison would disprove this discrete critical-weight
absolute fibre admission. It is a statement about the displayed series;
no passage from sampled cutoffs to a continuous absolute integral is assumed.
Its positive survivor is the actual complete semiprime-fibre
contribution and its eventual harmonic floor at the critical weight.
This is not divergence of the complete signed source and not RH falsification.
It would force cancellation between different clipped LCM fibres; it does
not supply that cancellation. No route is retired before the geometry,
comparison, and exact Lean statement are audited.

## Inputs inspected

MobiusDivisorLatePrimeHeadAsymptotic.eventually_mobiusDivisorLatePrimeMass_ge;
MobiusDivisorLatePrimeCompensation and its first-block source floor;
MobiusDivisorAbelQuadraticDiagonal; literal finiteLcmPairFibre and its exact
reindexing in EulerDeletionTruncatedDivisorPairCorrelation. Corpus searches
are recorded in the RP-45 working log. No numerical experiment.

## Implementation status

RoutePLcmAbsoluteObstruction.lean now contains the complete clipped
semiprime-fibre classification, a full-fibre comparison, the source-derived
harmonic floor, and nonsummability. Final audit pending. The comparison does
not discard hidden terms within a selected fibre: a fibre containing a late
prime pair is proved equal to the full active carrier at that LCM.
Only finished leaves will be wired; only foreground leaf audits, no umbrella
builds, added axioms, or resource overrides.
