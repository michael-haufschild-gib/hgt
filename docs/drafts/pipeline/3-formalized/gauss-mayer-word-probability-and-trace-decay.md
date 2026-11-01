# Gauss-word probability and uniform trace decay

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](gauss-mayer-primitive-orbit-product.md).

## Theorem

For every actual Gauss word `a` of length `k`, let `(c_a,d_a)` be the bottom
row of its integral matrix and put `P(a)=1/[d_a(c_a+d_a)]`. Then

```text
Σ_(a∈Word(k)) P(a) = 1,
Σ_(a∈Word(k)) d_a⁻² ≤ 2.
```

Both series converge. Every even word of length `2n` has `d_a≥2^n`.
For `Re w>2`, put `q(w)=exp(−(Re w−2)log 2)∈(0,1)`. The actual even-word
fixed-point traces satisfy, for every `n≥0`,

```text
Σ_(a∈Word(2n+2)) |Tr_a(w)| ≤ (8/3) q(w)^(n+1).
```

The alphabet is unrestricted and countable. No finite-digit truncation or
spectral exclusion hypothesis enters the estimate.

## Proof

Appending digit `j+1` on the right changes `(c,d)` to
`(d,c+(j+1)d)`. Scaling the convergent reciprocal telescope gives

```text
Σ_(j≥0) 1/[(c+(j+1)d)(c+(j+2)d)] = 1/[d(c+d)].
```

All terms are nonnegative. Head/tail reindexing and induction on word length
therefore preserve total probability one, starting from the empty word's
row `(0,1)`. The actual matrix law gives `0≤c≤d`, hence
`d⁻²≤2/[d(c+d)]`; summation gives the uniform inverse-square bound.
Two successive digits change the denominator to at least twice its old
value, proving `d≥2^n` at length `2n`.

The actual fixed point lies in `(0,1)`, so its expanding multiplier
`λ=cp+d` is at least `d`. For nonempty even words, `λ≥2`; consequently
`1−λ⁻²≥3/4`. The exact principal-power norm on a positive real base gives
`|Tr_a(w)|≤(4/3)λ_a^(−Re w)`.
Writing `δ=Re w−2>0`, the inequalities `λ≥d≥2^(n+1)` imply

```text
λ^(−Re w) ≤ d⁻² exp(−δ(n+1)log 2) = d⁻² q(w)^(n+1).
```

The inverse-square sum now yields the displayed geometric trace bound.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerWordProbability.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability`.

- `hasSum_successor`, `hasSum_probability`: exact probability telescope.
- `tsum_denominator_inv_sq_le`, `even_denominator_growth`: uniform bounds.
- `denominator_le_wordMultiplier`, `decayRate_bounds`.
- `norm_even_wordTrace_le`, `multiplier_decay_le`.
- `tsum_norm_even_wordTrace_le`: actual geometric absolute trace bound.

Direct production check passed without diagnostics. All nine transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
RenormalizedIntersectionTheory umbrella imports the module.

## Scope

The branch matrices, fixed points, trace formula, and one-dimensional
reciprocal telescope already existed. The source contribution is their
exact word probability law and its trace bound uniform in word length.
[Continuation to the closed unit spectral disk](gauss-mayer-unit-even-word-determinant.md)
and [primitive-cycle logarithm regrouping](gauss-mayer-primitive-orbit-logarithm.md)
and the [Euler product](gauss-mayer-primitive-orbit-product.md) are certified.
No scattering identity or resonance exclusion is claimed.
