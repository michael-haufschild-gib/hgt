# PM: individual prime pairs reinforce energy

- **Stage:** 5-failed (termwise dissipation claim only)
- **Type:** FORMALIZED SIGN OBSTRUCTION / FORMALIZED MIXED-COVARIANCE SURVIVOR
- **Route:** PM, actual Ramanujan Gram budget for cofinal small-damping L2 admission.
- **Lean:** `formal/GaloisForLFunctions/RHTower/PMPairedRamanujanGram.lean`.
- **Status:** Ten exported declarations built, directly audited and checked for axioms.

## Failed conjecture

Let a_epsilon(q) be the actual Ramanujan weight and G(q,r) the primitive
Gram kernel with weights 1/[N(N+1)]. The attempted justification for prime
pairing was that the q,p*q cross energy is nonpositive, allowing it to be
dropped from an upper bound.

This fails systematically. For every epsilon>0 and every squarefree q>1
which is not a prime power, sufficiently large primes p satisfy

`a_epsilon(q).re * a_epsilon(p*q).re * G(p*q,q) > 0`.

The statement concerns the actual coefficients. No model coefficients,
numerical experiments, RH assumption or small-damping admission premise
enter its proof. It rules out this termwise sign argument, not the full
natural-cutoff Gram conjecture or route PM.

## Exact positive survivor

For p prime, p not dividing q, and every N,

`P_(p*q)(N) = p*P_q(N/p)-P_q(N)`.

For q,r>1 and p not dividing either,

`G(p*q,p*r)+G(p*q,r)+G(q,p*r) = (p-1)*G(q,r)`.

For every fixed q,r>1, as primes p tend to infinity,

`G(p*q,r) -> phi(r)*Lambda(q)/2-G(q,r)`.

Moreover G(q,q)>0 for every q>1. Consequently G(p*q,q) is eventually
negative for every non-prime-power q>1, without a squarefreeness condition.
Squarefreeness is needed only to make the actual weight nonzero in the
strictly positive weighted-cross conclusion.

## Dependency-closed paper proof

1. Split the divisors of p*q into d and p*d, for d|q. Möbius prime
   multiplication and nested integer division give the primitive identity.
2. For k>=1, the reciprocal weights in [p*k,p*(k+1)) telescope to
   1/[p*k*(k+1)]. The k=0 term vanishes for a function f with f(0)=0.
   Absolute summability of bounded functions times reciprocal weights
   justifies the complete regrouping.
3. Multiply the two primitive identities and use this exact dilation
   identity. Expanding all four terms gives the Gram relation.
4. Let bounded g have mean m and bounded prefixes of g-m, and let bounded
   f satisfy f(0)=0. Every shifted prefix of g-m is bounded by twice the
   original prefix bound. Finite Abel summation against the decreasing
   reciprocal weights bounds each centered block by a constant times
   1/[p*k*(p*k+1)]. The summed, p-scaled error tends to zero. Hence

   `p*sum_N f(N/p)*g(N)/[N(N+1)]
      -> m*sum_k f(k)/[k(k+1)]`.

5. Set f=P_q.re and g=P_r.re. Their period means are -phi(q)/2 and
   -phi(r)/2; periodic centering gives bounded prefixes. The existing
   reciprocal moment is sum P_q(N).re/[N(N+1)]=-Lambda(q). Subtracting
   G(q,r) via the prime identity proves the stated mixed limit.
6. The nonzero period sum of P_q supplies a nonzero primitive value at a
   positive index. Its positive diagonal Gram term proves G(q,q)>0.
   For q not a prime power, Lambda(q)=0, giving eventual negative mixed
   covariance. For squarefree q the actual weight is nonzero, and
   a_(p*q)=-a_q/(p^(1+epsilon)-1). Its coefficient product is negative,
   so the actual weighted cross energy is positive.

## Lean and novelty audit

The primary declarations are:

- `pmRamanujanPrimitiveGram_prime_pair`.
- `tendsto_pm_floor_dilation_covariance`.
- `pmRamanujanPrimitiveGram_pos`.
- `tendsto_pmRamanujanPrimitiveGram_prime_mul`.
- `eventually_pmRamanujanPrimitiveGram_prime_mul_self_neg`.
- `eventually_pmPowerDampedRamanujan_prime_pair_cross_pos`.

Search63 and Search65 completed; Search64 and Search66 were partial.
Candidate/source statements and returned ingredient groups were examined;
no existing paired primitive, paired Gram, or floor-dilation covariance
limit was returned. Relevant source identities were inspected and every
used statement was checked by Lean. Search66's coverage report remained
pending, so no exhaustive semantic-coverage claim is made.

- [x] Exact no-go and positive survivor paper proofs.
- [x] `lake --old build GaloisForLFunctions.RHTower.PMPairedRamanujanGram`.
- [x] Final `lake env lean GaloisForLFunctions/RHTower/PMPairedRamanujanGram.lean`.
- [x] All ten exports: only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Wired into `RHTower.lean`; no umbrella build.
- [x] Formal lint run: no error for this leaf. Global gate reports twelve
  unrelated unwired modules, recorded in the working log.

## Continuing hard problem

The limit keeps q and r fixed. Its proof does not give the required bound
when both grow with the denominator cutoff. The complete covariance
across different cofactors and the full unpaired boundary remain in the
actual quadratic form. The active producer conjecture and exact boundary
decomposition remain in `../1-in-progress/pm-paired-cutoff-gram-budget.md`.
No RH proof or falsification has been obtained.
