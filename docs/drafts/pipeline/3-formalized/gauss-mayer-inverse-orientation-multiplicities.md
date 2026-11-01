# Inverse-orientation multiplicities in the actual Mayer product

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md).
- **Inputs:** [primitive modular coding](../3-formalized/gauss-mayer-modular-primitive-coding.md), [primitive-cycle Euler product](../3-formalized/gauss-mayer-primitive-orbit-product.md), [actual translation lengths](../3-formalized/gauss-mayer-hyperbolic-translation-length.md).

## Statement

Digit reversal induces an involution `J` on the existing primitive pair
cycles. The equality `Jc=d` holds exactly when the actual matrix of `d` is
integrally conjugate, by a determinant-one matrix, to the inverse matrix of
`c`. Pair length, expanding multiplier, and actual translation length are
invariant under `J`.

Let `U` be the quotient by `c∼d` iff `c=d` or `Jc=d`. Each fiber is
`{c,Jc}`. Its cardinality is `κ(U)=1` for a self-inverse class and `κ(U)=2`
otherwise. The actual determinant satisfies

```text
D(w,z)D(w,−z)
  = ∏_U ∏_(m≥0) (1−z^(2ℓ(U)) exp(−(w/2+m)L_U))^κ(U).
```

The joint product over `(U,m)` has the same value. These products converge
near `z=0` for each `Re w>1`, and throughout `|z|≤1` for `Re w>2`.
For the class of the singleton pair word `[(a,b)]`, multiplicity is one
exactly when `a=b`, and two otherwise.

## Proof

### Inverse classes

The map `r(u)=reverse(u).map swap` is an involution, preserves length, and
satisfies `r(u^n)=r(u)^n`. The last identity follows by reversing the order
of the `n` identical blocks. If `r(u)` were a proper whole-word power,
applying `r` again would make `u` a proper power. Thus `r` preserves
primitivity.

Reversal and mapping preserve cyclic rotation, so `r` descends to `J` on
primitive cycles. Its square is the identity. The existing theorem
`actualPairedMatrix_inverse_conjugacy_iff` identifies matrix inverse
conjugacy with cyclic rotation of `r(u)`. This proves the stated exact
interpretation of `J`.

The actual matrix of `r(u)` is the transpose of the matrix of `u`.
Its trace, hence its expanding multiplier, is unchanged. Rotation preserves
the same multiplier and word length. These invariances descend to cycles;
`L_c=2 log λ_c` gives translation-length invariance.

### Fiber cardinalities

The relation `c=d` or `Jc=d` is an equivalence because `J²=id`.
For any representative `c` of `U`, its complete fiber is `{c,Jc}`.
It has one element when `Jc=c` and two otherwise. The invariant lengths
and multiplier are therefore well-defined on `U`.

Every singleton pair word is primitive: a proper power would have length
`n·length(v)=1` with `n>1`, which is impossible. Its reversal is `[(b,a)]`.
A singleton list is cyclically rotated only to itself, so the inverse class
is equal to the original exactly when `a=b`. Both multiplicities are needed.

### Infinite products

Put `X(c,m)=z^(2ℓ(c)) exp(−(w/2+m)L_c)`. This is exactly the certified
source weight and is invariant under `J`. The source theorem supplies both
`Σ_(c,m)|X(c,m)|<∞` and the joint product with value `D(w,z)D(w,−z)` on the
stated domains.

Regroup the source joint product by the map `(c,m)↦(U(c),m)`. Every fiber
is the finite set `{c,Jc}` at a fixed mode. All its factors coincide, so its
product is `(1−X(c,m))^κ(U)`. The product Fubini theorem with these explicit
finite-fiber products gives the asserted joint quotient product.

For each fixed `U`, source norm summability restricts to the modes of any
representative. Thus `Σ_m X(c,m)` converges absolutely. The complex
infinite-product criterion for `1+f` with summable `f` proves convergence of
`∏_m(1−X(c,m))`; taking its finite power `κ(U)` preserves convergence.
Product Fubini now identifies the nested quotient/mode product with the
joint quotient product. All inputs are supplied by the actual source
convergence theorem.

## Lean certificate

Modules in `RenormalizedIntersectionTheory/`:

- `GaussMayerInverseCycles.lean`, namespace `MayerInverseCycles`:
  `inverseCycle_involutive`, `inverseCycle_eq_iff_inverse_conjugacy`,
  `cycleLength_inverseCycle`, `multiplier_inverseCycle`, and
  `orbitTranslationLength_inverseCycle` give the actual inverse-class
  involution and its invariants. `mem_orientations`, `orientations_unoriented`,
  `multiplicity_unoriented`, `multiplicity_one_or_two`, and
  `multiplicity_singleton` identify the complete fibers and their cardinalities.
- `GaussMayerUnorientedProduct.lean`, namespace `MayerUnorientedProduct`:
  `exists_signed_determinant_unorientedProduct` and
  `signed_determinant_unorientedProduct_on_closed_unit` prove the joint and
  nested actual determinant products, including mode convergence.
  `signed_determinant_one_eq_unorientedProduct` specializes to `z=1`.

Both direct production checks passed without diagnostics. All seventeen
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The programme umbrella imports both modules.

## Scope

This quotient identifies actual primitive integral matrix classes with their
inverses and retains their exact multiplicity in the source determinant.
An independently constructed closed-geodesic space and scattering determinant
remain separate comparisons.
