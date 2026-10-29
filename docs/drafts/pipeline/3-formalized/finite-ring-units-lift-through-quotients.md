# Units lift through quotients of finite commutative rings

- **ID:** finite-ring-units-lift-through-quotients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Every surjective ring homomorphism with finite commutative source is surjective on unit groups.

## Proof

In a finite monoid, two powers of any element agree: choose `i<j` with
`a^i=a^j` and put `d=j-i>0`. For every `k≥i`, multiplication by
`a^(k-i)` gives `a^(k+d)=a^k`. Iterating, `a^(k+td)=a^k`.
For `n=(i+1)d`, we have `n>0`, `n≥i`, and hence `a^(2n)=a^n`.
Thus a positive power of every element is idempotent.

Let `f:R→S` be a ring homomorphism with finite commutative source,
and suppose `f(r)` is a unit. Choose `e=r^n` idempotent, `n>0`.
Then `f(e)` is both idempotent and a unit, so `f(e)=1`.
Set `x=re+(1-e)` and `y=r^(n-1)e+(1-e)`. Since `e²=e` and
`r r^(n-1)=e`, direct expansion gives `xy=yx=1`. Therefore `x`
is a unit and `f(x)=f(r)`. If `f` is surjective, start with any
preimage of the target unit to obtain the claimed unit lift.

This proof includes the zero ring and uses no local decomposition.

## Lean

Module: `GaloisForLFunctions.HTGeometry.FiniteRingUnitsLiftThroughQuotients`.
Namespace: `GaloisForLFunctions.FiniteRing`.

- `exists_pos_pow_idempotent`
- `exists_unit_map_eq`
- `units_map_surjective`

The first and last declarations were checked transitively with
`#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
Final direct source audit passed without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/FiniteRingUnitsLiftThroughQuotients.lean
```

The module is wired into `HTGeometry.lean`; the umbrella was not compiled.
This supplies unit lifting for finite quotient-character descent. It does
not by itself identify a conductor or prove the Hecke functional equation.
