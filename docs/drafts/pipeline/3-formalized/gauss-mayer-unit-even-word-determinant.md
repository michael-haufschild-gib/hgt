# Mayer trace logarithm on the closed unit disk

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](../1-in-progress/gauss-mayer-primitive-orbit-product.md).
- **Inputs:** [local even-word identity](gauss-mayer-even-word-determinant.md), [source trace decay](gauss-mayer-word-probability-and-trace-decay.md).

## Theorem

For every `Re w>2` and `|z|≤1`, the actual global Mayer determinant satisfies

```text
D(w,z) D(w,−z) = exp(−E(w,z)),
E(w,z) = Σ_(n≥0) z^(2n+2)/(n+1) Σ_(a∈Word(2n+2)) Tr_a(w).
```

The full series over lengths and words converges absolutely. In particular,
the identity holds at `z=1`, and `D(w,z)≠0` throughout the closed unit disk.

## Proof

Put `q=exp(−(Re w−2)log 2)∈(0,1)`. The certified source bound is
`Σ_a |Tr_a(w)|≤(8/3)q^(n+1)` at length `2n+2`. For every `R>0` with
`R²q<1`, the `n`th term of `E` on `|z|<R` has norm at most
`(8/3)(R²q)^(n+1)`, since `n+1≥1`. This summable bound on holomorphic
polynomial terms proves that `E` is holomorphic on that disk.

Choose `R=2/(1+q)`. Then `R>1` and `R²q<1`, the latter inequality
being equivalent to `(1−q)²>0`. Both the entire signed determinant product
and `exp(−E)` are holomorphic on the connected disk `|z|<R`. The certified
local even-word identity makes them equal near zero. The identity theorem
therefore makes them equal throughout the disk, including `|z|≤1`.

On the closed unit disk, summing norms of individual word terms is bounded
by `(8/3)Σ_n q^(n+1)`. Nonnegative double-sum summability gives absolute
convergence before regrouping. The complex exponential never vanishes, so
neither factor of the signed determinant product can vanish there.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerUnitEvenWordDeterminant.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerUnitOrbitDeterminant`.

- `differentiableOn_evenWordExponent`: holomorphy on the larger disk.
- `summable_norm_evenWordSeries_on_closed_unit`: full absolute convergence.
- `signed_determinant_eq_evenWordExponent_on_closed_unit`: actual determinant identity.
- `signed_determinant_one_eq_evenWordExponent`: unit-parameter specialization.
- `determinant_ne_zero_on_closed_unit`: spectral zero exclusion for `Re w>2`.

Direct production check passed without diagnostics. All five transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
RenormalizedIntersectionTheory umbrella imports the module.

## Scope

This closes continuation of the source trace logarithm to spectral parameter
one. [Primitive pair-cycle regrouping](gauss-mayer-primitive-orbit-logarithm.md)
is certified; the Euler product remains unproved. This far-right zero-free
region gives no critical-strip resonance exclusion or scattering normalization.
