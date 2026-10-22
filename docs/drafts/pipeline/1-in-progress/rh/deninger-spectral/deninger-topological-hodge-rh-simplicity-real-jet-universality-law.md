# Deninger topological-Hodge RH/simplicity Real-jet universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.Deninger.DeningerTopologicalHodgeRHSimplicityRealJetUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

The corpus distributes consequences of a direct positive compact-open Deninger Hodge star across
separate modules:

- `DeningerArithmeticTopologicalCohomology` proves that it forces RH;
- `DeningerArithmeticJordanObstruction` proves that it forces local analytic multiplicity one;
- `DeningerCompactOpenGradedRealJetUniversalityLaw` supplies the continuous Real involution and
  all-order conjugate-zero parity;
- `XiHedenmalmSimplicityUniversalityLaw` classifies joint RH and simplicity in the eight
  simplicity charts together with prime--Gamma sign, reciprocal self-adjointness, Hermitian local
  Jordan models, a conservative theta metric, and the positive-half theta source.
- `XiWholeCorpusPositivePhaseUniversalityLaw` expands RH into eighteen parameter-uniform terminal
  analytic, geometric, Hankel, dyadic, local, seam, Hurwitz, thermal, Sonin, and Krylov families.

No theorem closes these into one statement of the exact burden carried by the direct topological
Hodge model.

## Statement

Every direct positive topological Hodge star on compact-open Deninger arithmetic `H¹` forces one
simultaneous certificate:

1. RH;
2. every Xi zero is simple and every local Xi Jordan model is normal;
3. all eight Hedenmalm continuation/Hilbert/Jordan/Bezoutian/theta simplicity charts hold, along
   with the prime--Gamma, reciprocal-operator, Hermitian-Jordan, conservative-metric, and
   positive-half theta-source RH classifiers;
4. every admissibly parameterized eighteen-family whole-corpus positive certificate holds;
5. the descended Real map is involutive;
6. every Xi jet transforms under conjugate-zero reindexing with exact parity `(-1)^k`.

## Dependency-closed proof

1. Apply the existing topological-Hodge RH theorem.
2. Apply the Jordan-chain obstruction at every divisor support point to get multiplicity one.
3. Convert multiplicity one to local Jordan normality, then use the global Jordan-normal
   equivalence to obtain `XiZerosSimple`.
4. Feed RH and simplicity into the enlarged universal Hedenmalm RH/simplicity equivalence.
5. Feed RH into the whole-corpus positive-phase equivalence for arbitrary admissible parameters.
6. Extract cohomological involutivity and all-order Xi-jet parity from compact-open graded
   Real-jet universality.

No computation or new Hodge axiom is introduced.  The law makes explicit that this direct
topological Hodge object proves strictly more than RH: it also forces simplicity.

## Novelty audit

Corpus audit: each implication exists separately, but no theorem packages global topological
Hodge positivity, RH, simplicity, the enlarged universal RH/simplicity charts, the eighteen-family
whole-corpus positive phase, and graded Real symmetry.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Pending exact source check and final umbrella audit.
