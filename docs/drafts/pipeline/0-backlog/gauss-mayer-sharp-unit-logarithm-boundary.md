# Sharp unit-disk boundary of the Mayer word logarithm

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Inputs:** [exact word probability](../3-formalized/gauss-mayer-word-probability-and-trace-decay.md), [unit-disk continuation](../3-formalized/gauss-mayer-unit-even-word-determinant.md).

## Candidate theorem

For every complex `w,z` with `|z|=1`, the full even-word logarithm satisfies

```text
Σ_(n≥0) Σ_(a∈Word(2n+2)) |z^(2n+2)/(n+1) · Tr_a(w)| < ∞
  iff Re w>2.
```

The positive direction is certified. The proposed negative direction has
not been formalized.

## Lower-bound mechanism to audit

For the actual bottom row `(c,d)` and fixed point `0<p<1`,
`λ=cp+d≤c+d≤2d`. When `σ=Re w≤2`, the exact even-word trace formula gives

```text
|Tr_a(w)| = λ^(−σ)/(1−λ⁻²) ≥ λ⁻² ≥ 1/(4d²) ≥ P(a)/4,
P(a)=1/[d(c+d)].
```

The certified probability identity is `Σ_a P(a)=1` at every word length.
Assumed full absolute summability would imply summability of the length
fibers, each bounded below by `1/[4(n+1)]`, contradicting harmonic
divergence. For `σ≤1`, fiber summability must be derived from the assumed
full summability; an unconditionally written totalized `tsum` cannot stand
for a divergent fiber.

## Stronger boundary candidate

Prove `D(2,1)=0` for the actual global determinant. At `w=2`, the same
denominator estimate should bound the absolute trace mass uniformly in
word length. It would continue the even-log identity to `|z|<1`, while
the harmonic lower bound forces the real exponent to diverge as `z↑1`.
Continuity gives `D(2,1)D(2,−1)=0`; certified negative-unit nonvanishing
would then identify the vanishing factor. The continuation and endpoint
limit remain unverified.

## Scope

This would classify the exact convergence threshold of the literal word
logarithm. It would not exclude complex resonances in the critical strip.
The [primitive-orbit product](../1-in-progress/gauss-mayer-primitive-orbit-product.md)
remains the active source-identification problem.
