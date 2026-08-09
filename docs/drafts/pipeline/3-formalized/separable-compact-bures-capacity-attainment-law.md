# Separable compact Bures capacity attainment law

- **ID:** `separable-compact-bures-capacity-attainment-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Parents:** `bures-incidence-minimax-coarea-law.md`
- **Statement:** For every separable complex Hilbert space, every nonempty norm-compact occupied
  target family in its closed unit ball, and every Bochner-square-integrable source field, the
  complete-union Bures capacity equals an attained maximum on the trace-norm closed convex hull of
  occupied rank-one rays; return removal charges its mass once and retains every surviving source
  sheet.

## Goal

Remove finite dimension, finite target enumeration, finite rank, and abstract nonattained `sSup`
from the complete-incidence law.  The theorem identifies the exact compact covariance carrier and
proves that its worst and best Bures targets exist.  It does not identify this capacity with an
infinite-dimensional positive-reporter infimum; that is a different theorem requiring an operator
trace/inversion interface.

## Universal law

Let `H` be a separable complex Hilbert space, `mu` a finite measure, `u` a Bochner `L²` field, and
`V` a nonempty norm-compact subset of the closed unit ball.  Put

```text
C = U U*,
U f = integral f(x)u(x) dmu(x),
K(V) = closed convex hull in trace norm of {|v><v| : v in V}.
```

Then `K(V)` is nonempty, convex, positive, trace-norm compact, and contained in the trace-norm unit
ball.  Every `M in K(V)` has a Hilbert--Schmidt positive square root with

```text
||sqrt(M)||_2 <= 1.
```

For operator Bures root fidelity

```text
F(C,M) = ||sqrt(C)sqrt(M)||_1,
```

the map `M -> F(C,M)` is continuous on `K(V)`.  Consequently there are `M_min,M_max in K(V)` with

```text
F(C,M_min) <= F(C,M) <= F(C,M_max)       for every M in K(V).
```

If `Cap_prob(C,V)` is the supremum of `F(C,M_lambda)^2` over all genuine probability laws supported
on `V`, with covariance `M_lambda = integral |v><v| dlambda(v)`, then

```text
Cap_prob(C,V) = F(C,M_max)^2.                            (1)
```

For every amplitude threshold `a>0`, with

```text
E_a = {x : exists v in V, |<u(x),v>| >= a},
```

one has the attained complete-union bound

```text
a^2 mu(E_a) <= F(C,M_max)^2.                             (2)
```

For every measurable return set `R`, let `C_R` be the covariance formed with `mu|R^c`.  There is a
maximizer `M_R in K(V)` such that

```text
mu(E_a) <= mu(R) + F(C_R,M_R)^2 / a^2.                   (3)
```

No target count, rank factor, ambient dimension, source quotient, or finite-support replacement
appears in `(1)`--`(3)`.

## Dependency-closed proof

1. Approximation-number Schatten-one operators form a Banach space for trace norm.  Trace norm
   dominates operator norm; finite sums of approximation numbers are lower semicontinuous under
   operator-norm limits; Fatou closure gives completeness.
2. The map `v -> |v><v|` is trace-norm continuous.  The closed convex hull of its compact image is
   trace-norm compact because convex hulls of totally bounded subsets of a normed space remain
   totally bounded.
3. Every supported probability covariance is a Bochner integral of occupied rays and hence lies in
   `K(V)`.  Conversely, every finite convex combination of occupied rays is the covariance of the
   literal convex mixture of their probability laws.  Therefore genuine designs contain the dense
   convex hull used to define `K(V)`.
4. A supported probability design has Hilbert--Schmidt synthesis norm at most one.  Douglas
   factorization expresses its covariance square root as synthesis followed by a contraction, so
   its root has Hilbert--Schmidt norm at most one.  Positive square-root continuity in operator norm
   and lower semicontinuity of Hilbert--Schmidt mass carry this bound through trace-norm closure.
5. If `B_n -> B` in operator norm and `B_n,B` have Hilbert--Schmidt norm at most one, then for every
   fixed Hilbert--Schmidt `A`, `A B_n -> A B` in trace norm.  Approximate `A` in Hilbert--Schmidt norm
   by a finite-rank truncation: sharp Schatten Hölder controls the truncation error, while rank times
   operator norm controls the finite-rank part.
6. Step 5 and operator-norm continuity of positive square root make Bures fidelity continuous on
   `K(V)`.  Compactness gives both extrema.
7. Every genuine design value is below the maximum by Step 3.  A sequence of finite genuine designs
   converges to the maximizer, so continuity proves the reverse capacity inequality and `(1)`.
8. The exact separable probability-design incidence law gives `(2)`.  Restricting the source measure
   to `R^c`, applying `(2)`, and using
   `mu(E) <= mu(R) + (mu|R^c)(E)` proves `(3)`.

## Lean theorem map

Module: `GaloisForLFunctions/HTGeometry/SeparableBuresCompactTargetBody.lean`

- `SchattenOneOperator` and its `CompleteSpace` instance
- `separableBuresCompactTargetBody_isCompact`
- `targetProbabilityCovariance_mem_separableBuresCompactTargetBody`
- `isTargetProbabilityCovariance_real_convex`
- `positiveRankOne_isTargetProbabilityCovariance`
- `convexHull_targetRaySet_isTargetProbabilityCovariance`
- `separableBuresCompactTargetBody_root_isHilbertSchmidt_norm_le_one`
- `traceNorm_comp_tendsto_of_fixed_hilbertSchmidt_of_unit_hsBound`
- `continuousOn_operatorBuresRootFidelity_compactTargetBody`
- `exists_extremal_operatorBuresRootFidelity_compactTargetBody`
- `exists_compactTargetBody_max_eq_targetProbabilityBuresCapacity`
- `exists_compactTargetBody_max_capture_bound`
- `returnRestrictedSourceCovariance`
- `exists_compactTargetBody_max_returnExcised_capture_bound`

Supporting modules:

- `SchattenOneBanach.lean`
- `HilbertSchmidtFiniteRankDensity.lean`
- `RectangularNuclearNormBound.lean`
- `SeparableBuresIncidenceLaw.lean`
- `SeparableBuresProbabilityDesignLaw.lean`

## Exact boundary

This card proves the compact-body maximum, exact probability-design capacity, capture law, and
return-excised law.  It makes no claim that

```text
max_(M in K(V)) F(C,M)
 = inf_(bounded A>0) max_(M in K(V)) 1/2[Tr(CA)+Tr(MA^-1)]
```

has been formalized in infinite dimension.  Finite-dimensional reporter minimax and singular
Alberti formulas are formalized separately.  The main paper may use the infinite compact-capacity
law above, but must keep any infinite reporter equality out unless that separate operator theorem is
closed.

## Gates

- [x] 0 -> 1: well-posed exact carrier and attack
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: final module and HTGeometry umbrella builds; whole-corpus lint green
- [ ] 3 -> 4: integrated into publication with external priority audit

## Log

- 2026-08-09 -- proved Schatten-one completeness and finite-rank Hilbert--Schmidt density.
- 2026-08-09 -- proved compact target body, literal convex probability mixing, dense design hull,
  uniform root control, mixed-topology nuclear continuity, Bures continuity, extrema, exact capacity,
  attained capture, and return-excised attained capture.
- 2026-08-09 -- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- 2026-08-09 -- final audit: `lake build
  GaloisForLFunctions.HTGeometry.SeparableBuresCompactTargetBody` and `lake build
  GaloisForLFunctions.HTGeometry` passed; `scripts/formal_tools.py lint` passed.
