# Finite Weil quadratic replication spectrum

Status: formalized and natively audited (2026-10-12).

## Objective

Classify every limiting Bhattacharyya affinity attainable by diverging replication
schedules for the actual finite Weil quadratic tilted laws. Mathematical evidence
is restricted to the local Lean corpus. No web, external papers, computations, or
literature novelty claims.

## Corpus frontier

AdaptiveAffinityReplication and FastAffinityReplication settle targets one and
zero. WeilLogShiftQuadraticReplication identifies diagonal equality as the stable
regime; WeilLogShiftQuadraticFastReplication identifies eventual finite-law
inequality as the exact fast-separation criterion. No intermediate-target
construction was found in the scoped replication search (four declarations).
The broader powers search is discovery evidence, not a corpus-wide novelty claim.
EllipticThetaLogGlobalMeromorphic supplies a local minimal-power crossing argument.

## Dependency-closed proof

1. For an ENNReal base x<1 and target 0<q<1, let n be the first natural exponent
   with x^n<q. Geometric convergence ensures existence. Then n>0, and minimality
   at n-1 gives q*x <= x^n < q. This uses non-strict multiplication and includes x=0.
2. If f(r) tends to one and is eventually below one, choose that first exponent
   at each good r (zero elsewhere). The squeeze q*f(r) <= f(r)^m(r) <= q proves
   convergence to q. For each fixed N, f(r)^N eventually exceeds q. Monotonicity
   of powers for bases <=1 then forces m(r)>N. Thus m escapes to infinity.
3. For arbitrary f bounded by one with limit c<=1, all escaping powers tend to
   zero when c<1. When c=1, target one exists by slow diagonal selection; target
   zero exists iff eventually f<1; every intermediate q exists under precisely
   that same eventual strictness. Any attainable q is <=1. Any q<1 forces f<1
   eventually, since bases >=1 have every natural power >=1.
4. Apply this exact classification to actual finite tilted probability measures.
   Existing native results discharge the affinity bound, affinity limit, strict
   rigidity, product factorization, and limit-equals-one iff diagonal equality.
   The final root has only structural subcritical parameter domains and an
   arbitrary ENNReal target; no analytic assumptions are added.

## Exact intended root

For canonical depths 2*(r+1)^2+t(r), subcritical sums s=a+2*b+d and S=A+2*B+D,
and arbitrary q in ENNReal, an escaping replication schedule with affinity limit q
exists iff:

- s differs from S and q=0; or
- s=S and either q=1, or q<1 and the actual finite laws are eventually unequal.

Schedules for intermediate targets need not be monotone. A coefficient-level
classification of finite-law equality and rates for prescribed schedules remain
outside this increment.

## Plan and verification

1. Complete scoped corpus discovery; verify every needed local Mathlib API natively.
2. Formalize threshold selection, generic spectrum, and actual-law root in leaves.
3. Build each leaf sequentially with empty native logs; wire umbrellas only afterward.
4. Audit all new declarations, dependencies, axioms, scoped index publication,
   whitespace, and repository lint; record unrelated lint failures separately.

Progress: conjecture and dependency-closed proof recorded before implementation.
All three leaves pass native Lean with empty logs. The generic spectrum
theorem derives c<=1 from the limit and affinity bound, avoiding a redundant
premise. The actual-law root discharges all analytic hypotheses from existing
probability, affinity-limit, product-factorization, and rigidity theorems.

Scoped prior audit: all 38 records from the HTGeometry powers/tendsto query were
inspected across two pages. PowerSequenceLimitOne supplies a rate-based sufficient
condition for target one, distinct from the new complete existence classification.
The four WeilLogShift replication records were all inspected. These targeted
results do not assert a corpus-wide absence of related mathematics.

## Formalized declarations

- HTGeometry/IntermediateAffinityReplication.lean:
  exists_ennreal_power_crossing and exists_ennreal_powers_tendsto_intermediate.
- HTGeometry/AffinityReplicationSpectrum.lean:
  exists_ennreal_powers_tendsto_iff.
- RHTower/WeilLogShiftQuadraticReplicationSpectrum.lean:
  exists_finiteWeilCanonicalJointQuadraticTilt_replication_limit_iff.

The resulting spectrum is exactly {0} for unequal diagonal coefficients, [0,1]
for equal diagonal coefficients with eventual finite-law inequality, and {1}
for equal diagonal coefficients without eventual finite-law inequality. The
latter includes infinitely many equal finite-law pairs, not just eventual equality.
This classification uses subcritical coefficient domains and canonical depths;
the earlier fast-separation criterion separately holds for arbitrary depths and
all real coefficients.

## Final verification

- Three sequential native leaf builds completed with empty logs. Both umbrellas
  are wired; no umbrella or full build was run.
- Final native scratch audit passed four axiom reports and sixteen API checks.
  Only propext, Classical.choice, and Quot.sound occur.
- Metadata audit verified four unique declarations, six direct import edges,
  five incoming imports, three fresh objects, direct dependency freshness,
  and exactly one umbrella import per leaf.
- Refreshed scoped publication plus cached follow-up searches returned all four
  declarations, with no partial flags, markers, or stderr diagnostics.
- All source and umbrella whitespace checks passed.
- Single repository lint run found sixteen unrelated errors and 367 warnings.
  Unreachable RHTower modules: CCMPolarOddPrimeJumps, CharacterProductZeroPlanting,
  PaperWoldCompactDomain, PaperWoldCompositeFlat, PaperWoldCompositeMass,
  PaperWoldEssentialFloor, PeriodicExpProducerSingleCharacter,
  Sieve.FourthDerivativeTestSharp, WeilBoundedDenominatorLockRH,
  XiLogDerivEventualPositivity, ZetaFiveSeventhsLineBound.
  Unreachable HTGeometry modules: DirichletExpMultiplicativeTwist,
  PeriodicCharacterDecomposition, PrimeProgressionReciprocalDivergence,
  QKrawtchoukCompanionTriangular. Existing proof debt:
  CCMPolarOddPrimeJumps.lean:104, ccmPolarOddSource_eq_core_add_atoms.
  No error belongs to these three leaves.
- Audit artifacts use /tmp/hgt-affinity-spectrum-; native leaf logs use
  /tmp/hgt- followed by the leaf basename and .log.

## Remaining frontier

The subsequent finite-weil-quadratic-tilt-equality increment gives an exact finite
potential test for law equality, anchored at source atom 0, and transfers it to
this spectrum. A uniform classification of the coefficient subspace, prescribed
replication schedules, and monotone intermediate-target schedules remain open
here. No monotonicity claim is made for the minimal-crossing construction.
The corpus-wide research goal remains active.
