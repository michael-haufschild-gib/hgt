# APEX-C Proof Attempt: Universal Prime-Side Orthogonality

Source: `docs/consolidated/08-conjectures-required.md` §3.

Claim status: `[CONJECTURE - strongly supported]`.

## Target Claim

There is no positive-definite polarization on any object of the prime category
`M` whose positivity is equivalent to RH. RH positivity is archimedean, not
prime-side.

## Proof Attempt

Start with the rank-one prime lane. Let `e` be a basis vector and let a prime
dilation act by

```text
sigma_p e = q e,  q = p^(-1) or another multiplier with q^2 != 1.
```

If a bilinear pairing `B` is invariant under this action and pairs the object
with its dual in the naive self-dual way, then

```text
B(e,e) = B(sigma_p e, sigma_p e) = q^2 B(e,e).
```

If `q^2 != 1`, this forces `B(e,e) = 0`. Therefore no nondegenerate positive
rank-one invariant pairing exists on this lane.

This is the algebraic core of the orthogonality theorem recorded in the corpus:
prime multipliers are not self-dual under the FE polarization. The FE sends
`p^{-s}` to `p^{-1} (p^{-s})^{-1}`, which is not an automorphism of the
prime-side torus preserving the original multiplier.

## Weakened Theorem Proved Here

**Theorem APEX-C-W.** A rank-one diagonal prime lane with multiplier `q` and
`q^2 != 1` admits no nonzero invariant positive self-pairing of the form above.

Proof: the single-line invariance computation.

## Why This Does Not Prove Universal Orthogonality

The full conjecture quantifies over "any object of `M`" and "any
positive-definite polarization" admissible in the prime category. A rank-one
calculation does not classify extensions, completions, non-diagonal objects,
or hidden polarizations after changing categories.

However, it gives the obstruction a hard local form: any proposed prime-side
polarization must explain how it avoids the multiplier equation `q^2 = 1`.

## Missing Input

1. A formal category of admissible prime-side objects.
2. A definition of admissible polarization in that category.
3. A classification theorem reducing every candidate to multiplier
   self-duality obstructions, or an explicit counterexample.
4. A fake-family test showing any surviving prime-side positivity separates
   the RH-axis rather than a realization or variance axis.
