# Actual hyperelliptic Frobenius fixed points

- **ID:** RIAC-hyperelliptic-fixed-points
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](../1-in-progress/riac-curve-orientation-square-root.md)
- **Lean:** [HyperellipticFixedPoints.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/HyperellipticFixedPoints.lean)

## Arithmetic comparison

Let `F` have odd cardinality `q`, let `f∈F[X]` have odd degree, and let
`E/F` be finite. For `d>0` dividing `[E:F]`, the actual fixed points of
`Frobenius^d` on `C(E)={(x,y):y²=f(x)}⊔{∞}` are in bijection with
`C(K)`, where `K/F` is the actual degree-`d` extension. Consequently

`#Fix(Frobenius^d | C(E)) = q^d+1−Σ_(α∈lRoots(f)) α^d`.

The roots are those of the existing arithmetic L-polynomial. No splitting,
square-root bound, simplicity, or cancellation assertion is an input.

## Proof

An embedding `e:K→ₐ[F]E` exists by finite-field degree divisibility.
`Frobenius_F^[K:F]` raises elements to `#K`, hence generates `Gal(E/K)`.
Its fixed elements are fixed by every automorphism and lie in the image
of `e`. Apply this characterization to both coordinates; injectivity of
`e` descends the equation `y²=f(x)`. Infinity remains fixed.

The quadratic-character solution count and the proved extension
character-sum identity give the displayed root-power-sum formula. Taking
`[E:F]=n!` discharges degree divisibility for every `1≤d≤n`. No claim is
made for arbitrary iterates in that finite ambient extension.

## Lean declarations

- `finiteField_frobenius_pow_apply`, `finiteField_frobenius_fixed_iff`,
  `finiteField_frobenius_pow_fixed_iff`, `finiteFieldFrobeniusFixedEquiv`.
- `hyperellipticPointMap_injective`, `hyperellipticPointEquiv`,
  `hyperellipticFrobenius_pow`, `hyperellipticFrobenius_fixed_iff`,
  `hyperellipticFrobeniusFixedEquiv`.
- `hyperelliptic_card_points`, `hyperelliptic_card_points_roots`,
  `hyperelliptic_frobenius_fixed_count`, `hyperelliptic_factorial_fixed_count`.

Direct Lean check and 13 transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`.

## Boundary

This discharges the arithmetic fixed-point input for the general signed
cycle comparison. It gives no integer-cutoff estimate for
`Σ_p index_p(N)=1−M(N)`.
