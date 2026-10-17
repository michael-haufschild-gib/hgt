# Infinite coprime trace extension and orthogonal energy projection

- **ID:** infinite-coprime-trace-extension
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Extend the finite divisor-trace realization to arbitrary square-summable
  data, with an actual L² velocity and exact infinite energy/projection identities.

For d∈ℕ set m=d+2 and active centers n_j=m(j+1). Given an actual ℓ² sequence v,
construct E_d(v) from disjoint unit tent derivatives centered at n_j. Proved laws:

    primitive E_d(v)(n_j)=v_j,
    primitive E_d(v)(n)=0 at every other nonnegative integer,
    ∫ |E_d(v)|² = 2 Σ_j |v_j|².

The construction must prove L² convergence or direct L² admission; finite sums
alone do not establish an infinite extension. A velocity q=E_d(v) yields actual
logarithmic traces at log n and the weighted additive derivative-energy law.

For any physical L² q, define the discrete second difference

    a_j=2 primitive q(n_j)−primitive q(n_j−1)−primitive q(n_j+1).

The actual a∈ℓ² is derived from q, and E_d(a/2) is its orthogonal projection onto
the closed tent-velocity subspace, with the unconditional exact defect

    ∫q² = (1/2)Σ_j a_j² + ∫(q−E_d(a/2))².

This should recover sharp infinite coprime coercivity when neighboring traces
vanish, but the core construction and projection must not assume trace support,
summability of an arbitrary raw sequence, or an unproved analytic admission.
Use ℓ² as intrinsic input data and derive every required convergence statement.
No claim of unitary affine action or closed SourceGraph identification.

Corpus query `infinite square summable coprime divisor trace interpolation L2
velocity energy isometry` completed without partial stages or errors. All 20
candidate lemmas and 20 source arguments were inspected. Finite step/divisor
realization and finite exact defects are available; no matching infinite
extension or projection theorem was found. Semantic coverage unmeasured,
coverage snapshot older than index, background refresh incomplete. Inspect
the finite interpolation sources and primary parent theory again before proof.
Paper construction and projection proof recorded in
`docs/reports/BiScaleUncertainty/InfiniteCoprimeTraceExtension.md`.
Dependency-closed paper proof and Lean formalization complete. Certified package
9/100, counted once. Both direct leaf checks pass without diagnostics.

Completed: disjoint unit-cell Hilbert frame; normalized tent synthesis isometry
and adjoint; every integer trace; exact infinite energy/projection laws; closed
range; unique best approximation and exact equality classifiers.

Fresh focused corpus search inspected all 20 candidate lemmas and all 20
source arguments. No matching infinite coprime extension/projection found.
Search had no partial stages or errors; coverage snapshot older than index,
semantic coverage unavailable, background refresh incomplete. Classical
Riesz–Fischer and orthogonal projection theory checked against NPTEL chapter 1,
Theorems 1.5.4–1.5.7; no external novelty claim for those parent tools.

Lean leaves: `CoprimeTentHilbertFrame.lean` (17 public theorems, 8 definitions,
one abbreviation) and `InfiniteCoprimeTraceProjection.lean` (23 public theorems,
3 definitions). All 52 public declarations audited, only standard Lean axioms.
Twelve main signatures checked; no added analytic premises. Imports, both maps,
all 40 theorem names in generated index and scoped whitespace checks pass.

Global lint reports nine unrelated concurrent unreachable modules:
`DyadicSchurCollarEnergy`, `DyadicSchurSupport`, `FourthMomentJumpReceiver`,
`InfiniteGridStrictEnergyLoss`, `ShortSupportEnergyInjection`,
`SmallSourceCorrelationStability`, `TwoColumnSchurGeometry`,
`TwoColumnSchurSupport`, `UnitEnergySmallSources`. No new-leaf error. Exact logs,
scope boundaries and reusable APIs are in `ContinuumCoprimeShear-FACTS.md`.

Next unproved candidate: arithmetic gcd/lcm classification of these projection
commutators, `../0-backlog/coprime-projection-arithmetic-commutator.md`.
