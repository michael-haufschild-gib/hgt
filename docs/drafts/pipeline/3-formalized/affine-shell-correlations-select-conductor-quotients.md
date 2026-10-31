# Affine shell correlations select conductor quotients

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md).

For positive `m,l` dividing a common period `M`, and every `k,h≥0`,

`sum_(n<M)c_m(n)c_l(kn+h)=1_(m=l/gcd(l,k)) M c_l(h)`.

A dilation retains precisely the reduced conductor `l/gcd(l,k)`; the
successor shift retains the full coefficient `c_l(h)`. For arbitrary finite
packets `A(n)=sum_(m in S)a_m c_m(n)` and `B(n)=sum_(l in T)b_l c_l(n)`,
with all conductors positive and dividing `M`,

`sum_(n<M)A(n)B(kn+h)`
`=M sum_(l in T)1_(l/gcd(l,k) in S) a_(l/gcd(l,k)) b_l c_l(h)`.

## Proof

Primitive Fourier expansion reduces the mean to root pairs `z w^k=1`.
The power `w^k` has exact order `l/gcd(l,k)`; when that order is `m`,
its inverse supplies the unique matching primitive root. Summing the
remaining `w^h` gives `c_l(h)`. Expanding finite packets gives the second
identity, retaining every mixed entry.

## Lean

`SuccessorShellArithmetic/Conductor/AffineShellConductorSelection.lean`:

- `sum_range_ramanujanLagCoefficient_mul_affine`;
- `sum_range_ramanujanLagCoefficient_mul_affine_of_coprime`;
- `sum_range_ramanujanPacket_mul_affine`.

Final direct `lake --old env lean` check passed. All three capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
The finite logarithmic shell boundary and complete Weil identity remain open.
