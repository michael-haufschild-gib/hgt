# Exact even-word logarithm of the Mayer determinant

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](../1-in-progress/gauss-mayer-primitive-orbit-product.md).

## Theorem

For every `Re w>1`, there is `r>0` such that for `|z|<r`,

```text
D(w,z) D(w,−z) = exp(−Σ_(n≥0) z^(2n+2)/(n+1) Σ_(a∈Word(2n+2)) Tr_a(w)).
```

Here `D` is the actual global source Fredholm determinant and
`Tr_a(w)=λ_a^(−w)/(1−λ_a⁻²)` is the actual even-word fixed-point trace.
The complete double series over lengths and words converges absolutely
on the same neighborhood, before any regrouping into primitive cycles.

## Proof

The source matrix kernel represents its Hilbert realization exactly. The
existing coordinate-matrix power theorem therefore identifies each kernel
power diagonal with the actual operator trace. Near zero, the global
regularized determinant agrees with its convergent trace exponential.
The ordinary determinant adds the exact first-trace factor. Multiplying
its values at `z` and `−z` cancels that factor; odd powers cancel and each
even power doubles. Thus the coefficient at length `2n+2` is `1/(n+1)`.
The certified countable Gauss-word trace formula identifies each coefficient
with the displayed literal fixed-point sum.

For absolute convergence, let `B(w,a)` be the existing product digit majorant
and `M(w)` its one-digit sum. Head/tail factorization proves
`Σ_(a∈Word(k)) B(w,a)=M(w)^k` exactly. The actual Cauchy diagonal satisfies
`|diagonal_j(a)|≤(25/32)^j B(w,a)`, hence
`|Tr_a(w)|≤(32/7)B(w,a)`. The total norm at length `2n+2` is bounded by
`(32/7)(|z|M(w))^(2n+2)`, since `n+1≥1`. This is geometrically summable when
`|z|M(w)<1`. Intersect the determinant neighborhood with
`|z|<1/(1+M(w))` to obtain both conclusions simultaneously.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerEvenWordDeterminant.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitDeterminant`.

- `norm_wordTrace_le`, `tsum_norm_wordTrace_le`: uniform absolute majorants.
- `summable_norm_evenWordSeries`: absolute summation over all even words.
- `exists_signed_determinant_eq_evenWordExponent`: actual determinant identity.
- `exists_signed_determinant_and_absolute_evenWordSeries`: common neighborhood.

Direct production check passed without diagnostics. All five transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
RenormalizedIntersectionTheory umbrella imports the module.

## Scope

The global Fredholm construction and fixed-length word trace formula already
existed. The contribution is their source-level parity identity with absolute
summation across all lengths. The exponent is identified with the global
determinant only on its proved convergence neighborhood. Primitive-cycle
reindexing, geometric length identification, scattering normalization, and
critical-strip resonance exclusion remain separate obligations.
[Convergence and continuation at `z=1`](gauss-mayer-unit-even-word-determinant.md)
are certified for `Re w>2`.
