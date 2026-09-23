# Uniform finite-clock debt for moving helper sets

- **ID:** rh-moving-helper-clock-debt
- **Owner:** critical-clock product task
- **Stage:** 3-formalized
- **Type:** [BRIDGE] THEOREM (Lean)
- **Source:** MobiusDivisorPrescribedClockBlock; MobiusDivisorInheritedPrimeInsertionProducer
- **Statement:** Actual positive omitted-prime debt persists at every sufficiently large cutoff, uniformly over arbitrary helper sets with a sufficiently large least prime and sufficiently small reciprocal mass.

## Goal

The requested chain remains paid exhaustive continuation -> bounded critical
action -> RH. This theorem tests a necessary finite-counting restriction on
that construction. It does not construct payments or imply RH. Unlike the
previous fixed-window result, one cutoff threshold precedes every helper
set and every moving prime window.

## Gates

- [x] Actual arithmetic energy, original clock weight, all mixed terms.
- [x] Dependency-closed paper argument below.
- [x] Scratch Lean proof and standard-axiom audit.
- [x] Named leaf build and umbrella wiring.

## Paper proof [PROVED HERE]

Write W(P,M) for the original finite clock and C(P)=((3/5)*2^(card(P)-1))^2.
Let every helper prime p in S satisfy p>=B>0.

1. Retain cofactors r>M/B divisible by no p in S. Their two source cutoffs
   M/r and M/r+1 are <= every p in S, so the union-inactive theorem leaves
   their heads exactly unchanged. They remain in the new cofactor set.
2. Every old sample is nonnegative and at most C(P)*M*(1+log M), by the
   actual source-amplitude theorem. New samples are nonnegative too.
3. At most floor(M/B) old cofactors are small. For each helper p, exactly
   floor(M/p) positive integers at most M are divisible by p. The union
   bound therefore proves
   W(P,M)-W(P+S,M) <= C(P)*M^2*(1+log M)*(1/B+sum_S 1/p).
   No limit, cardinality, depth, or cutoff-onset constant depends on S.
4. The actual omitted-prime producer gives r and delta>0 with
   K(P+r)-K(P)=2*delta. The two fixed-core clock limits give a single M0
   after which W(P+r,M)-W(P,M)>3*delta/2*M^2*(1+log M).
5. Choose B with C(P+r)/B<=delta/4 and eta=delta/(4*C(P+r)).
   Every helper set with p>=B and sum 1/p<=eta can lower the enlarged
   clock by at most delta/2 times the normalization, at EVERY M>=M0.
   Thus the actual debt remains >=delta times that normalization,
   uniformly over moving helper sets and all their mixed source terms.

6. For helpers in tau<log p<=(1+kappa)*tau, interval Mertens gives
   tau*sum_S(1/p)<=kappa*tau+log(2)+mertensIntervalConst. Choose
   kappa=eta/4 and T>=max(log(B),1,4*(log(2)+mertensIntervalConst+1)/eta).
   Then every tau>=T satisfies p>=B and reciprocal mass<=eta. The SAME M0
   from step 4 works for all tau, all helper subsets, and all M>=M0.

## Method interrogation

- The prior proof knew the helper window was fixed only at the finite
  powerset intersection. That line prevented coupling window and cutoff.
- The replacement invariant is the unchanged original cofactor sample,
  including its literal logarithmic weight. Only small cofactors and
  multiples of actual helpers can move.
- What this means for the whole route: moving short windows cannot bypass
  the produced debt merely by staying ahead of a window-dependent limit.
  Broader helper sets, existing active helpers, and full cumulative signed
  control remain outside this obstruction. This bridge does not replace
  the primary paid exhaustive continuation problem.

## Novelty and scope

The prior bounded-child-quotient bound counts ALL primes up to M and does
not yield this uniform reciprocal-mass statement. The prior clock-span
producer fixes the prime window before selecting its cutoff onset. The
new argument retains exact cofactors and counts only actual helper primes.
No literature or retrieved result supplied the uniform moving-set theorem.
This is a positive retained-source lower bound, not a negation alone.

## Lean certificate

`MobiusDivisorMovingClockDebt.lean` exports
`exists_mobiusDivisorUniformMovingHelperDebt` and
`exists_mobiusDivisorMovingClockSpanDebt`. Both passed scratch checking with
`lake env lean /tmp/hgt-moving-clock.lean`. Their axiom audits list only
`propext`, `Classical.choice`, and `Quot.sound`.

`lake build GaloisForLFunctions.RHTower.MobiusDivisorMovingClockDebt`
passed without new-leaf warnings. The leaf is wired into `RHTower.lean`.
No full or umbrella build ran. Repository lint returned four unrelated
reachability errors: `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
`ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
`XiHeatCassiniWoldJointDepthMobiusSourceTransport`.

Paid exhaustive continuation and RH remain unproved. The new theorem is
uniform in helper sets and moving clock windows for each fixed initial
core; its constants are not uniform as that initial core changes.

Corpus index refresh passed. Owned scratch Lean files and proof fragments
were removed after promotion; all owned Lean, build, search, lint and index
processes exited. Audit logs remain under `/tmp/hgt-moving-clock*`.
