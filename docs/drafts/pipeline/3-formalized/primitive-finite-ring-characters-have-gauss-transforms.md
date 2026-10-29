# Primitive finite-ring characters have exact Gauss transforms

- **ID:** primitive-finite-ring-characters-have-gauss-transforms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** For a primitive multiplicative character of a finite commutative ring, every shifted Gauss sum equals the inverse-character value times the original Gauss sum. A primitive additive character gives squared Gauss norm equal to the ring cardinality.

## Definitions and proof

Pullback of a multiplicative character means pullback on unit groups,
followed by extension by zero on nonunits. This distinction matters:
a nonunit can become a unit in a quotient.

For an ideal `J`, a character factors through `R/J` exactly when it is
one on all units `u` with `u-1∈J`. The forward implication follows by
evaluation. For the converse, [finite-ring unit lifting](finite-ring-units-lift-through-quotients.md)
makes the map on unit groups surjective; the group homomorphism descends
through its kernel and extends by zero. The descended character is unique.
A character is primitive when it factors through no nonzero ideal.
Equivalently, every nonzero ideal has a congruence unit on which its
character is not one.

For a nonunit `a`, multiplication by `a` on the finite ring is not
injective, so its annihilator is nonzero. Primitivity supplies a unit
`u` with `(u-1)a=0` and `χ(u)≠1`. The change of variables `x↦ux`
leaves the shifted additive character `ψ(ax)` fixed but multiplies
the Gauss sum by `χ(u)`. Thus the Gauss sum is zero. For unit `a`,
the usual change of variables gives

```
τ(χ,ψ(a·)) = χ⁻¹(a) τ(χ,ψ).
```

These two cases prove the identity for every `a`, with no primitivity
requirement on `ψ`. If `ψ` is primitive, additive orthogonality gives

```
Σ_a τ(χ,ψ(a·)) ψ(-a)
  = Σ_b χ(b) Σ_a ψ(a(b-1))
  = |R| χ(1) = |R|.
```

Substitution of the Gauss transform yields
`τ(χ,ψ) τ(χ⁻¹,ψ⁻¹)=|R|`. For complex-valued characters, the second
factor is the complex conjugate of the first, so `|τ(χ,ψ)|²=|R|`.
The argument includes the zero ring.

## Lean

Module: `GaloisForLFunctions.HTGeometry.PrimitiveFiniteRingCharactersHaveGaussTransforms`.
Namespace: `GaloisForLFunctions.FiniteRing`.

- `inflateChar`, `inflateChar_injective`, `exists_inflateChar_eq_iff`
- `FactorsThrough`, `factorsThrough_iff`
- `IsPrimitive`, `isPrimitive_iff`, `exists_unit_stabilizer`
- `gaussSum_nonunit_eq_zero`
- `gaussSum_mulShift_eq_of_isPrimitive`
- `sum_gaussSum_mul_inverse_eq_card`
- `gaussSum_mul_inverse_eq_card`
- `norm_gaussSum_sq`

The descent criterion, primitive criterion, full Gauss transform,
reciprocal product, and norm identity were checked transitively with
`#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
Final direct source audit passed without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/PrimitiveFiniteRingCharactersHaveGaussTransforms.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled. This is a
general theorem about primitive characters, not a replacement for the
remaining construction of the actual Hecke trace character, conductor
reduction, or arithmetic identification of the dual theta coefficients.
