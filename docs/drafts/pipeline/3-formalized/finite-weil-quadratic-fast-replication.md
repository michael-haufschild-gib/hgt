# Finite Weil quadratic fast replication

Status: formalized and natively audited (2026-10-12).

## Target and local frontier

Use only local Lean mathematical sources. No web, external papers, or numerical
experiments. The preceding adaptive result supplies slow stable schedules when
subcritical diagonal coefficients agree. Here the target is an exact fast
separation criterion for actual finite laws, valid for all real coefficients
and arbitrary depth schedules k:Nat->Nat:
a monotone diverging schedule m(r)>=r with affinity tending to zero exists iff
the two finite tilted measures are eventually unequal.

Finite fluctuation points have separate centered-index and centered-correction
coordinates. Diagonal equality alone is therefore not assumed to classify
finite-law equality. Coefficient-level identification remains a later question.

## Dependency-closed paper proof

1. For arbitrary probability measures P,Q, put u=(dQ/dP).toReal. The corpus
   proves integrability of u and sqrt(u). Expanding (sqrt(u)-1)^2 establishes
   integrability of the squared defect. General RN integration, including the
   singular part, gives the exact positive decomposition

   2*(1-affinity(P,Q).toReal)
     = integral (sqrt(u)-1)^2 dP + (Q.singularPart P).real(univ).

   Both right-hand terms are nonnegative, hence affinity<=1. Equality forces
   the squared defect to vanish almost everywhere, so dQ/dP=1 P-almost
   everywhere. The corpus's withDensity_rnDeriv_le then gives P<=Q; equal
   total probability mass gives P=Q. Conversely self-affinity is one. Thus
   affinity<1 iff P differs from Q, without absolute-continuity premises.
2. Fast diagonal selection into a countably generated filter: if rows F(r,n)
   converge for all sufficiently large r, choose thresholds N(r) for membership
   in the r-th antitone basis set, with arbitrary thresholds for bad initial
   rows. Set m(r)=max(r,partialSups N r). This is monotone, at least r, and
   eventually lands F(r,m(r)) in every prescribed basis neighborhood.
3. Apply step 2 to F(r,n)=f(r)^n in ENNReal. Eventual f(r)<1 supplies row
   convergence to zero. Conversely product convergence to zero forces eventual
   f(r)^m(r)<1; if f(r)>=1 every natural power is >=1. Therefore fast schedules
   exist exactly when f(r)<1 eventually. No global bound on f is needed.
4. Actual finite quadratic tilted laws are probability measures for every r,k
   and every real coefficient triple. Apply step 1 pointwise and existing
   Bhattacharyya product factorization, then step 3. Because the pointwise
   probability facts hold for every r,k, the depth schedule is arbitrary.
   No subcriticality, depth-growth, or convergence-rate premise is needed at
   this actual-law root.

## Local evidence and plan

- Local bhattacharyya/equality query returned no declarations; source search
  found existing self-affinity and the new real-overlap bridge, but no general
  equality-rigidity theorem.
- Broad hellinger/zero query had 135 eligible declarations; inspected first
  page (20), dominated by unrelated Hellinger--Gamma algebra. This was
  exploratory, not a complete novelty audit. Direct local source/API checks
  supply the relevant RN, integral-zero, probability-order, and partialSups facts.
- Expected leaves: ProbabilityAffinityRigidity, FastDiagonalSelection,
  FastAffinityReplication, WeilLogShiftQuadraticFastReplication.
- Native leaf checks, umbrella wiring, lint, complete scoped source/import/index
  audit and native axiom audit precede publication.
- Strengthening audit: the proof exposed that canonical quadratic depth was
  unnecessary. The paper argument above now quantifies over arbitrary depth
  schedules. Local fast/replication search in WeilLogShift, excluding this
  new leaf, returned no declarations or markers.

ProbabilityAffinityRigidity, FastDiagonalSelection, and FastAffinityReplication
passed natively with empty logs. The strengthened actual-law leaf also passed.

## Final verification

- Four native leaf builds passed with empty logs: ProbabilityAffinityRigidity,
  FastDiagonalSelection, FastAffinityReplication, and
  WeilLogShiftQuadraticFastReplication. Both umbrellas are wired without
  building them.
- Nine theorem axiom reports and fourteen local API checks passed. Only
  propext, Classical.choice, and Quot.sound occurred.
- Metadata audit verified eight direct import edges, seven incoming imports,
  direct dependency freshness, four fresh objects, and unique umbrella imports.
- Refreshed scoped publication and cached follow-up queries returned all nine
  declarations, with no partial flags, stale markers, or stderr diagnostics.
- Source and umbrella whitespace checks passed.
- Repository lint remains blocked by eleven unrelated errors and 367 warnings:
  ten unreachable modules (CCMPolarOddPrimeJumps, CharacterProductZeroPlanting,
  PaperWoldCompositeLower, PaperWoldHilbertSchmidtStability,
  PaperWoldSharpHilbertSchmidt, XiCosineShiftDefectZeroDensity,
  DirichletExpMultiplicativeTwist, PeriodicCharacterDecomposition,
  PrimeProgressionReciprocalDivergence, QKrawtchoukCompanionTriangular) and the
  existing sorry in CCMPolarOddPrimeJumps.lean:104. None is in these four leaves.
- Audit artifacts use the /tmp/hgt-weil-fast-replication- prefix.

## Remaining boundary

The existence criterion is exact at the level of finite measures, for arbitrary
real coefficients and arbitrary depth schedules. A coefficient-level
classification of finite-law equality remains open here. Prescribed replication
schedules also require further information. The corpus-wide research goal
remains active.
