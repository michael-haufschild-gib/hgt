# Primitive Mayer cycles and closed modular geodesics

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 1.
- **Inputs:** [integral coding](gauss-mayer-modular-primitive-coding.md), [translation lengths](gauss-mayer-hyperbolic-translation-length.md), [inverse orientation](gauss-mayer-inverse-orientation-multiplicities.md).

## Theorem

Let `X=SL₂(ℤ)\SL₂(ℝ)` carry the actual flow `[C]↦[Ca_t]`,
where `a_t=diag(exp(t/2),exp(−t/2))`. Define oriented closed geodesics
independently as phase classes of frames with a positive return time.
Primitive Mayer pair cycles are in bijection with these geometric orbits.
The least positive return time is exactly the actual displacement length
`L_c=2 log λ_c`. The lifted axis `t↦C·(i exp(t))` has distance `|t−u|`,
so this normalization is geometric arc length.

Actual time reversal corresponds to inverse integral conjugacy. Its
unoriented fibers have cardinality one for self-reversing geodesics and
two otherwise. For `Re w>2`, the genuine determinant satisfies

```text
D(w,1)D(w,−1)
  = ∏_(oriented g) ∏_(m≥0) (1−exp(−(w/2+m)L_g))
  = ∏_(unoriented u) ∏_(m≥0) (1−exp(−(w/2+m)L_u))^κ(u).
```

The first product defines the geometric Selberg Euler product at `s=w/2`.
The joint geometric weights are absolutely summable. Both joint and nested
products, including the exact geometric multiplicities `κ(u)∈{1,2}`, are
certified. The scattering comparison is a separate open obligation.

## Proof

A return `γC=Ca_t` has integral trace `exp(t/2)+exp(−t/2)`.
For `0<t<2 log 2`, this lies strictly between two and three, which is
impossible. Thus the return subgroup is not dense; the real subgroup
dichotomy makes it either trivial or `Tℤ`, `T>0`.

The explicit determinant-one eigenbasis of a primitive cycle supplies a
return at `L_c`. If `L_c=nT`, the integral return at `T` has `n`th power
equal to the actual cycle matrix. Whole-pair root classification excludes
`n>1`, proving that `L_c` is the least period.

Two frames with the same nonzero integral return differ by a matrix
commuting with a nontrivial real diagonal element. Its off-diagonal
entries vanish, and determinant one makes it `±a_u`. The integral central
matrix `−I` removes the sign, so the frames differ only by phase.
Phase preserves period groups. Equality of least periods and conjugacy of
primitive returns therefore prove injectivity of the cycle map.

Conversely, any positive integral return is conjugate to a nonempty pair
word. Extract its primitive root `v` and repetition number `n`. The
canonical frame of `v` returns under the powered matrix at `nL_v`.
Positive return time is determined by trace: for `x,y>1`,
`x+x⁻¹=y+y⁻¹` gives `(x−y)(xy−1)=0`. Equal-return phase uniqueness
identifies the original orbit with the root's orbit, proving surjectivity.

Right multiplication by `J=[[0,−1],[1,0]]` reverses the actual axis and
satisfies `Ja_t=a_(−t)J`. It replaces a return by its inverse at the same
positive time. Since `J²=−I`, it induces an involution on geometric orbits.
The exact integral inverse-conjugacy criterion identifies it with the
inverse-cycle involution. Reindex the certified primitive-orbit product
through these geometric equivalences; absolute convergence and every
orientation-fiber cardinality are preserved.

## Lean certificates

All modules lie in `RenormalizedIntersectionTheory/`.

| Module | Main declarations |
|---|---|
| `GaussMayerGeodesicFlow` | `MayerGeodesicFlow.isometry_axis`, `periods_eq_bot_or_positive_lattice` |
| `GaussMayerGeodesicCentralizer` | `MayerGeodesicCentralizer.common_return_phase` |
| `GaussMayerRealEigenbasis` | `MayerRealEigenbasis.exists_expanding_eigenbasis` |
| `GaussMayerPrimitiveGeodesicReturns` | `MayerPrimitiveGeodesicReturns.cycleFrame_periods`, `cycleFrame_least_period` |
| `GaussMayerClosedGeodesics` | `MayerClosedGeodesics.cycleEquiv`, `length_ofCycle`, `length_isLeast` |
| `GaussMayerGeodesicReversal` | `MayerGeodesicReversal.axis_reversed`, `reverse_ofCycle`, `reverse_ofCycle_eq_iff` |
| `GaussMayerGeodesicProduct` | `MayerGeodesicProduct.hasProd_geodesic`, `signed_determinant_eq_selbergZeta`, `orientationMultiplicity_card`, `signed_determinant_unoriented_geodesics` |

Direct production checks and transitive axiom audits passed with only
`propext`, `Classical.choice`, and `Quot.sound`. No geometric classification,
return law, or analytic convergence premise is imported as an assumption.
