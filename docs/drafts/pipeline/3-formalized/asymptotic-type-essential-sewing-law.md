# Asymptotic-type essential sewing law

Status: formalized.

## Statement

Let \(a\) be a nonvanishing asymptotic scale along an arbitrary filter.  Let \(f\) be
all-orders flat relative to \(a\), and let \(g\) have nonzero finite grade \(d\):
\[
 f=o(a^m)\quad(m\geq0),\qquad g=\Theta(a^d).
\]
Then the exact scalar sewing cost satisfies
\[
 a^{-K}=o(g/f)\qquad(K\geq0).
\]

More generally, for arbitrary real normed spaces \(E,F\), if \(f_x\in E\) is eventually
nonzero and all-orders flat, \(\|g_x\|=\Theta(a_x^d)\), and bounded linear maps
\(R_x:E\to F\) satisfy \(R_xf_x=g_x\), then
\[
 a_x^{-K}=o(\|R_x\|)\qquad(K\geq0).
\]

Thus an all-orders-flat germ and a nonzero finite-grade germ are different asymptotic species.
Exact sewing between them requires an essential scale singularity; finite dimension, infinite
rank, and matrix enlargement do not change the conclusion.

## Proof

At order \(K+d\), all-orders flatness gives
\[
 f=o(a^{K+d}).
\]
Inversion reverses the little-\(o\) relation, and multiplication by the finite-grade target gives
\[
 a^{-K}=o(g/f).
\]
For an exact bounded linear sewing,
\[
 \|g_x\|\leq\|R_x\|\,\|f_x\|,
\]
so the scalar norm ratio is \(O(\|R_x\|)\), proving the operator theorem.

## Formal source

- `formal/GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean`
- `RHTower.reesEssentialSewingCost_beyondEveryFiniteOrder`
- `RHTower.reesExactSewingOperatorNorm_beyondEveryFiniteOrder`

Direct source check:

```text
lake env lean GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean
```

Result: success.

## Role in publication

This is the arithmetic-independent theorem underlying the prime-valuation reflection fracture.
The prime source supplies a flat positive sector and a finite half-normal negative sector; the
universal law proves that every exact internal sewing has norm beyond every finite inverse Wold
order.

