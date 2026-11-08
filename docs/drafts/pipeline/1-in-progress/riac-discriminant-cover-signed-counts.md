# Discriminant covers as signed arithmetic counts

- **ID:** RIAC-discriminant-cover
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Construct the coefficient-polynomial cover `y²=disc(f)` and identify it with the independently counted root-orientation cover.

## Mathematical target

For an odd finite field `F` of cardinality `q`, let
`D_n(F)={(f,y): f monic of degree n, y∈F, y²=disc(f)}`.
The expected counts are `2`, `2q`, `q^n` in degrees zero, one and at least two.
The count must be derived from arithmetic fibres and independent orbit
counts, without using a polynomial Möbius cancellation theorem.

## Formalized actual count

The [arithmetic Vieta correspondence](../3-formalized/riac-arithmetic-vieta.md)
identifies monic degree-`n` polynomials with Frobenius-stable permutation
orbits of roots in the constructed extension `E/F` of degree `n!`.
All root multiplicities are retained.

The [root-orientation cover](../3-formalized/riac-root-orientation-cover.md)
is the actual finite set

`C_n(F)={(f,y): f monic of degree n, y∈F, (ιy)²=V(x_f)²}`.

Here `x_f` orders the roots in `E`, `V` is their Vandermonde product, and
`ι:F→E`. Its square is independent of the ordering. Collisions give the
single point `y=0`; distinct roots give two or zero points according to
Frobenius orientation. Each fibre therefore has cardinality `1+w`, where
`w` is the actual signed transporter weight.

[Normal-basis bijections](../3-formalized/riac-independent-frobenius-orbit-counts.md)
count every permutation twist independently, and the
[signed orbit theorem](../3-formalized/riac-finite-field-signed-orbits.md)
cancels the total orientation weight for `n≥2`. Consequently
`#C_n(F)=q^n`, with direct Lean and transitive axiom audits.

The separate [factor-trace cover](../3-formalized/riac-finite-field-orientation-counts.md)
retains polynomial Möbius signs but uses established Möbius degree sums
for its aggregate count. Its defining invariant has not been identified
with the root discriminant.

## Remaining comparisons

1. Present the root equation by one polynomial in coefficient coordinates.
   The existing integral symmetric discriminant polynomial is a candidate.
2. Prove equality with Mathlib's `Polynomial.discr`, including collisions;
   then transfer the root-cover count to `D_n(F)` and settle its two small degrees.
3. Identify Frobenius cycles with irreducible factors to derive the
   factorization-sign/Pellet comparison from these same objects.

No equality in this list is claimed merely from equality of aggregate counts.

## Integer target

The governing target remains `Σ_p index_p(N)=1−M(N)` with
`Oε(N^(1/2+ε))` cancellation; a literal `O(√N)` estimate is stronger.
The finite-field construction controls a full coefficient space. No
compatible realization or estimate for the integer conductor cutoff has
been constructed. It supplies no integer cancellation bound.

## Literature boundary

Pellet's identity and its Frobenius proof are classical:
[Afshar, §§1–2](https://arxiv.org/html/2001.05641v1).
The stabilizer-weighted ramified-cover framework is treated by
[Gadish, Definition 1.1 and Corollary 1.4](https://arxiv.org/html/1703.01710v2).
The contribution is a dependency-closed formal construction and independent
count, not a new classical point-count theorem.
