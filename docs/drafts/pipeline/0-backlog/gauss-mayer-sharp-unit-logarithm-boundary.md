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
|Tr_a(w)| = λ^(−σ)/(1−λ⁻²) ≥ λ⁻² ≥ 1/(c+d)² ≥ P(a)/2,
P(a)=1/[d(c+d)].
```

The certified probability identity is `Σ_a P(a)=1` at every word length.
Assumed full absolute summability would imply summability of the length
fibers, each bounded below by `1/[2(n+1)]`, contradicting harmonic
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

## Stronger spectral-order candidate

Conjecture that `z↦D(2,z)` has a simple zero at `z=1`. This concerns the
spectral variable `z`, not the source variable `w`.

An improved probability estimate should give `Σ_a d_a⁻²≤7/4` at every
positive word length. Appending digit one has conditional probability
`d/(c+2d)≤1/2`. The new ratio `c'/d'` is at most one on that branch and at
most `1/2` on all other branches. Since `d'⁻²=P'(1+c'/d')`, summing gives
the proposed `7/4` bound.

For nonempty even words, `d≥2`, `a≥1`, and `λ≥d`. The characteristic
equation implies `λ²−1=(a+d)λ−2≥d²`, so the trace at `w=2` is at most
`d⁻²`. Together with the proposed lower bound, this would give, for
`0<t<1`,

```text
(1−t²)^(7/4) ≤ |D(2,t)D(2,−t)| ≤ (1−t²)^(1/2).
```

Analyticity would force the spectral vanishing order to be the integer one:
the upper bound forces a zero, while the lower bound excludes order two or
higher. Negative-unit nonvanishing would transfer simplicity to `D(2,z)`.
The improved probability estimate, determinant bounds, and order argument
all require Lean formalization.

## Scope

This would classify the exact convergence threshold of the literal word
logarithm. It would not exclude complex resonances in the critical strip.
The [primitive-orbit product](../1-in-progress/gauss-mayer-primitive-orbit-product.md)
remains the active source-identification problem.
