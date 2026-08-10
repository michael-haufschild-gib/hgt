# Consensus-face / collision-history mechanism

## Higher-level pivot
Scalar higher "curvature" was rejected. Ordinary Boolean Möbius inversion of nonnegative raw overlaps has alternating top coefficient I_r = (-1)^r(r-1) on constant-observer Dirac profiles, hence is negative at every odd arity. Positivity lives in a witness face, not an alternating scalar.

Surviving route-independent mechanism:
source distinction -> simultaneous consensus face -> collision-depth filtration -> independently weighted history.

Nested observer exits are load-bearing. For two composable observers X -> K -> L and equal-mass nonnegative finite profiles, a single explicit coupling simultaneously maximizes agreement at K and L. Arbitrary finite nested chain is paper-proved but not Lean-certified yet. Incomparable observers can have disjoint maximizing faces.

A cofinal collision profile d_n=1/((n+1)(n+2)) has capacity A_N=1-1/(N+1), vanishing tail 1/(N+1), but divergent depth-weighted history because (n+1)d_n=1/(n+2). Thus bounded normalized observer loss does not imply bounded lifted history; cost/uniform integrability is a separate constitutive law.

## Lean
New modules:
- formal/GaloisForLFunctions/HTGeometry/ConstitutiveHierarchicalMaximalCoupling.lean
  capstone exists_coupling_simultaneously_maximal_for_two_nested_observers
- formal/GaloisForLFunctions/HTGeometry/ConstitutiveCofinalCollisionHistory.lean
  capstone cofinalCollision_bounded_budget_infinite_history

Both wired into HTGeometry/UniversalLawField.lean.
Direct elaboration clean, formal lint passed, final umbrella build passed (11,514 jobs).
#print axioms on capacity bound, simultaneous-maximality, nonsummability, and collision capstone returned only propext, Classical.choice, Quot.sound.
No stale Lean processes.

## Documentation
Stage2 cards:
- nested-observer-hierarchical-maximal-coupling-face-law.md
- cofinal-collision-depth-nonintegrable-history-law.md
Stage3 cards certify only two-level and analytic cores.
Stage5 no-go card: nonnegative-mobius-irreducible-overlap.md.
_LEAN-CERTIFICATION.md updated.

## Exact open boundary
Do not claim arbitrary finite hierarchy or countable coupling realization Lean-proved. Scalar Möbius counterexample itself remains Lean-pending. Next mechanism research should investigate compatibility criteria for observer diagrams beyond chains and characterize when local maximal-consensus faces have nonempty intersection.