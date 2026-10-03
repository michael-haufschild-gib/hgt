# RP: absolute budgets for clipped LCM fibres

- **ID:** RP-45-absolute-LCM
- **Stage:** 5-failed (absolute-budget candidate only)
- **Type:** PROVED obstruction with formalized positive arithmetic survivor
- **Source:** RP-45 in rp-unconditional-history-floor-loop-2026-10-01.md
- **Goal unchanged:** unconditional RH through the complete signed RP floor.

## Candidate refuted

Can complete LCM-fibre regrouping make the unpaid paired source absolutely
admitted at every critical damped weight? This would permit estimating each
fibre separately after shared-cutoff integration. No such admission is assumed.

Write a_M(d)=mobiusDivisorDilationChannel M d and use the existing literal
finiteLcmPairFibre over d,e in Icc1 M. Define V(M) as the sum of absolute
values of these fibres for lcm labels greater than M. The target test is
summability of V(4N)/((4N)^3*sqrt(4N)), a critical damped weight.

## Corpus-grounded paper proof

Let L_M be the primes in(M/2,M], T_M their unsigned channel mass, and
Q_M their ordered off-diagonal signed pair sum. Both individual channels
are nonpositive on these prime labels, so Q_M=T_M^2-D_M, where D_M is the
late-prime diagonal. The existing full signed diagonal is at most722*M^2,
and D_M is a nonnegative sub-sum of it.

For every M, distinct p,q in L_M have pq>M: M<2q<=pq follows from
q>floor(M/2) and primality of p. Any active positive
integer pair d,e<=M with lcm(d,e)=pq is either(p,q) or(q,p): the other
divisors are1 and pq, and a pair involving1 would require the inactive pq.
Thus the entire fibre, not just a selected term, equals2*a_M(p)*a_M(q)>=0.
Regrouping the prime-pair sum by these complete fibres gives Q_M<=V(M).

The corpus's quantitative late-prime floor is

    T_(4N) >= N*sqrt(N)/(80*log(2N)) eventually.

Set M=4N in the following asymptotic comparison.
Since log(2N)/N^(1/4) tends to zero, eventually
T_M>=2*M*sqrt(sqrt(M)). Also sqrt(M)>=722 eventually. Consequently

    Q_M = T_M^2-D_M >= M^2*sqrt(M) eventually,
    V(M)/(M^3*sqrt(M)) >= 1/M.

The harmonic comparison disproves this discrete critical-weight
absolute fibre admission. It is a statement about the displayed series;
no passage from sampled cutoffs to a continuous absolute integral is assumed.
Its positive survivor is the actual complete semiprime-fibre
contribution and its eventual harmonic floor at the critical weight.
This is not divergence of the complete signed source and not RH falsification.
It forces a proof using this budget to retain cancellation between different
clipped LCM fibres; it does not supply that cancellation. Only the absolute
replacement is retired. Route RP remains open.

## Inputs inspected

MobiusDivisorLatePrimeHeadAsymptotic.eventually_mobiusDivisorLatePrimeMass_ge;
MobiusDivisorLatePrimeCompensation and its first-block source floor;
MobiusDivisorAbelQuadraticDiagonal; literal finiteLcmPairFibre and its exact
reindexing in EulerDeletionTruncatedDivisorPairCorrelation. Corpus searches
are recorded in the RP-45 working log. No numerical experiment.

## Implementation status

RoutePLcmAbsoluteObstruction.lean contains four public theorems:

- finiteLcmPairFibre_clipped_semiprime: exact complete two-term fibre.
- routePHighLcmVariation_ge_latePrimeMass: for every M,
  T_M^2-722*M^2<=V(M), without an asymptotic premise.
- eventually_routePHighLcmVariation_critical_floor: unconditional eventual
  harmonic floor for the displayed critical-weight series.
- not_summable_routePHighLcmVariation_critical: unconditional nonsummability.

The foreground final leaf audit using lake --old env lean with an explicit
output olean exited0 (handle28407), with no diagnostics. Axiom audit79559
exited0: all four public theorems use only propext, Classical.choice,
Quot.sound. No sorryAx or added axiom. Global lint exited1 on twelve unrelated
unreachable modules, listed in the RP-45 working log; this leaf had no finding.
The leaf has one umbrella import; the umbrella was not built. The comparison does
not discard hidden terms within a selected fibre: a fibre containing a late
prime pair is proved equal to the full active carrier at that LCM.
No added axioms or resource overrides. No numerical experiment. The generic
divisor-list classification is elementary and is not presented as scientific
novelty by itself. The route-specific content is its full clipped-fibre
comparison with actual channel mass and the resulting critical-weight
nonsummability. Corpus applicability was audited in RP-45; literature novelty
is not claimed. Lean exposed the unnecessary lower cutoff restriction in the
initial paper argument; the strengthened all-M geometry was rechecked above.

The strongest positive survivor is the all-cutoff native lower bound and its
eventual harmonic consequence, both formalized in the same leaf. This does
not leave the no-go at a negation or a reformulation of its negation.
