# Surviving coordinates of prime-height persistence

- **ID:** esg-critical-coordinate-persistence
- **Stage:** 3-formalized
- **Type:** INTEGRAL PERSISTENCE COORDINATES

## Exact statement

Over any commutative ring, let `D_k(N)` be the actual odd exterior chains whose
prime-support products are at most `N`. Let `W_k(N)` be the finitely supported
coefficient module on odd prime supports of cardinality `k` and product `m`
satisfying `m≤N<2m`.

Coordinate restriction `π_N : D_k(N) → W_k(N)` is split surjective, and its
kernel is exactly `D_k(⌊N/2⌋)`, viewed inside `D_k(N)`. The quotient by this
kernel is linearly equivalent to `W_k(N)`.

For `N≤M`, the map `W_k(N) → W_k(M)` retains a coefficient precisely while
`M<2m`. These maps form a functor. Projection `π_N` commutes with the actual
height inclusions of odd chains. The statement includes exterior degree zero.

## Proof

The exterior basis identifies odd chains with their finitely supported
coefficients. Restrict to the surviving support set; the inverse lift on this
set is the inverse basis representation. Their composite is identity.
A coordinate already born by `N` is discarded exactly when `2m≤N`, equivalently
`m≤⌊N/2⌋`. This proves the kernel identity and the quotient comparison.

If `N≤M≤L`, a coordinate born by `N` and surviving at `L` also survives at `M`.
Thus successive restrictions equal restriction to the last height. The same
observation proves naturality of projection from odd chains.

## Lean realization

[PrimeCriticalCoordinates.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeCriticalCoordinates.lean),
namespace `GaloisForLFunctions.EffectiveScalingGeometry`:

- `primeCriticalProjection_lift`, `primeCriticalProjection_ker`.
- `primeCriticalQuotientEquiv`.
- `primeCriticalMap_apply`, `primeCriticalMap_comp`.
- `primeCriticalProjection_natural`, `primeCriticalPersistence`.

Direct `lake --old env lean` audit passes. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`. Imported by the programme umbrella.

## Scope

Together with the [cycle-height theorem](esg-cycle-height-structure.md), this
identifies the concrete subquotient and its persistence maps. The [actual categorical comparison](esg-prime-homology-coordinates.md) is established
in every augmented degree, with integer interval labels. Canonical coefficient
extension is proved in the
[integral persistence card](esg-integral-prime-persistence.md).
No Euler-cancellation bound or new priority claim for the classical rank
formula is made.
