# Primitive Gauss sums detect additive primitivity

- **ID:** primitive-gauss-sums-detect-primitive-additive-characters
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** For a primitive complex multiplicative character of a finite commutative ring, its Gauss sum against an additive character is nonzero exactly when that additive character is primitive. Its squared norm is then the ring cardinality, and otherwise zero.

## Proof

If the additive character `ψ` is imprimitive, choose `a≠0` with
`ψ(ax)=1` for every `x`. The principal ideal `(a)` is nonzero.
Primitivity of the multiplicative character `χ` gives a unit `u`
such that `u-1∈(a)` and `χ(u)≠1`. Writing `u-1=ar`, we have
`ψ(ux)=ψ(arx+x)=ψ(x)`. Changing variables by `u` in the Gauss
sum therefore multiplies it by `χ(u)` without changing its value;
the sum must be zero.

If `ψ` is primitive, the previously proved exact squared Gauss norm
is `|R|>0`, so the Gauss sum is nonzero. Combining the two cases
proves the support criterion and exact zero-or-cardinality norm law.

## Lean

Module: `GaloisForLFunctions.HTGeometry.PrimitiveGaussSumsDetectPrimitiveAdditiveCharacters`.
Namespace: `GaloisForLFunctions.FiniteRing`.

- `gaussSum_eq_zero_of_not_isPrimitive`
- `gaussSum_ne_zero_iff_isPrimitive`
- `norm_gaussSum_sq_eq_ite`

All three transitive `#print axioms` audits show only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/PrimitiveGaussSumsDetectPrimitiveAdditiveCharacters.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled. This
criterion applies to actual trace characters after their construction;
the arithmetic ideal description of their primitivity is still needed
for the completed Hecke functional equation.
