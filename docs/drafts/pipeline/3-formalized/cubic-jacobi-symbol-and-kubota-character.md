# A nontrivial cubic Kubota character

- **ID:** cubic-jacobi-symbol-and-kubota-character
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [metaplectic Möbius descent](../1-in-progress/metaplectic-mobius-descent.md)
- **Statement:** On the principal congruence subgroup `Γ(3)⊂SL₂(O)`, `κ([a b;c d])=(c/a)₃` is a character onto the cubic roots. Its kernel has index three in `Γ(3)` and finite index in `SL₂(O)`.

## Product law

For determinant-one matrices `M=[a b;c d]`, `N=[e f;g h]`, put
`A=ae+bg`, `C=ce+dg`. Then `aC−cA=g`. First assume `(a,g)=1`, so
`(a,A)=1` and `(a/A)₃` is cancellable. Reciprocity and numerator congruence give

`(a/A)₃(C/A)₃=(g/A)₃`,

`(a/A)₃(c/a)₃=(g/a)₃`.

Since `3|b,g`, the difference `A−ae=bg` is divisible by both nine and `g`.
The ramified denominator law gives `(g/A)₃=(g/a)₃(g/e)₃`. Cancellation proves
`κ(MN)=κ(M)κ(N)`.

For general `g≠0`, choose `t` as the product of prime factors of `g` that do
not divide `a`. Then `(a+3tc,g)=1`: primes dividing `a` divide none of `3,c,t`,
while other prime divisors of `g` divide `t`. Replace the upper row of `M` by
itself plus `3t` times the lower row. The denominator law preserves its
multiplier and the multiplier of the product. Apply the coprime case. If
`g=0`, the primary unit `e` equals one and the identity is immediate.

## Image and kernel

Coprime cubic symbols have cube one, so `κ` takes values in `μ₃(O)`.
The explicit matrix `[[1+3ω,−3ω²],[3,1−3ω]]` belongs to `Γ(3)` and has
multiplier `(3/(1+3ω))₃=ω`: use `3=−λ²ω²` and the supplementary values
at the norm-seven prime. Its powers attain every cubic root. The first
isomorphism theorem therefore gives kernel index three. Reduction modulo
three has finite image, so this kernel also has finite index in `SL₂(O)`.

## Lean

Module: `MetaplecticMobiusDescent/TheCubicKubotaMultiplier.lean`.
Endpoints: `kubota_mul`, `value_mul`, `complexCharacter_cube`,
`value_cubicGenerator`, `finiteCharacter_surjective`,
`finiteCharacter_kernel_index`, `globalKubotaKernel_finiteIndex`,
`globalKubotaKernel_mem`. Direct Lean audit passed. All eight transitive
axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella wired.

The product law and finite-index construction adapt external OpenAI proofs;
source attribution is in `NOTICE`. The explicit primitive value and exact
relative index are local extensions. The rational extension remains on
[rational-extension-of-cubic-multiplier](rational-extension-of-cubic-multiplier.md);
the actual theta function and uniform descent remain on the parent card.
