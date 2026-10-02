# RN-P-7k: actual source residual at a coalescing center pair

Status: main theorem and supporting limits formalized in
`ThetaTailConfluentCenterGram.lean` and `ThetaTailConfluentCenterLimits.lean`.
Both leaves passed the targeted `lake --old build`, final direct
`lake env lean <leaf>` audits, and all 16 public theorem axiom checks
(only propext, Classical.choice, Quot.sound). Both are wired into RHTower.
Repository lint still reports ten unrelated unreachable modules.
This controls the
actual residual without assuming that its two representer coefficients
are positive. It does not settle the coordinate residual or arbitrary rank.

## Corpus inputs

The actual theta source k is positive, even and Schwartz. Its logarithmic
decay p=-(log k)' satisfies p(0)=0 and `t p'(t)>p(t)` for every t>0,
by the proved strict convexity of p. The normalized kernel row
`L(0,y)=H(0,y)/(k(0)k(y))` strictly decreases for y≥0. The complete
two-node determinant is strictly positive at every distinct pair.

## Exact confluent Gram entry

Put `k₀=k(0)`, `q=p'(0)`, `J=H(0,0)`, `I=∫₀∞t k'(t)²dt`, and
`β=2I-k₀²`. Integration by parts gives

    β=∫₀∞[t p'(t)-p(t)] k(t)²dt > 0.

The identity uses `(t p k²)'=(p+t p'-2t p²)k²`,
`∫p k²=k₀²/2`, and `p²k²=k'²`. Integrability and zero tail boundaries
follow from the Schwartz derivatives: `p'k²=k'²-k k''` and
`p k²=-k k'`. Thus there is no unproved bound on logarithmic derivatives.

In the confluent basis `(k,k')`, the full-tail matrix at the center is
`diag(J,β)`, and the source endpoint vector is `(k₀,0)`.

## Actual inverse coefficients

Schwartz domination justifies differentiating the tail integral. The
exact center expansions are

    k(z)=k₀-q k₀ z²/2+o(z²),
    H(z,z)=J-k₀²z²+o(z²),
    H(0,z)=J-Iz²+o(z²).

In particular, `det M/z²→Jβ>0`. For the literal source representer
`d=M⁻¹(k₀,k(z))`, direct inversion therefore gives

    d₁ → k₀(I+qJ/2-k₀²)/(Jβ),
    d₂ → k₀(I-qJ/2)/(Jβ),
    d₁+d₂ → k₀/J.

No sign of `I+qJ/2-k₀²` is assumed. It is exactly the integrated sign
left open in RN-P-7j; it cancels in the sum needed below.

## Positive actual source residual

For fixed y>0, symmetry of M identifies the actual source residual as

    A_z(y)=k(y)-d₁ H(0,y)-d₂ H(z,y).

Continuity of H and the finite coefficient limits yield

    A_z(y)/k(y) → 1-L(0,y)/L(0,0) > 0               (z→0+).

The strict sign is exactly the already formalized ordered-row theorem.
Thus for every fixed y>0 there is δ>0 such that every
`0<z<min(δ,y)` has `A_z(y)>0`, with the actual projection equations kept.

This avoids the stronger pointwise four-point inequality (now falsified)
and the still-open positivity of individual inverse coefficients. It is
a qualitative actual-projection region, not an optimized numerical bound.
The coordinate residual, global parameter continuation, arbitrary-rank
positivity and the retained RH transfer remain open.

The public endpoint is `RHTower.ThetaConfluent.eventually_sourceResidual_pos`.
Its residual uses the literal `ThetaSturm.representerLeft` and
`ThetaSturm.representerRight`; no coefficient-sign premise is supplied.
RN-P-7l retains the next coordinate-port integral comparison.

## Search audit

The deep confluent-projection search had partial semantic coverage and
source-only metadata; it returned no matching actual first-moment-kernel
result. The argument above uses the inspected source Schwartz, convexity,
two-node determinant and ordered-row corpus, not an inferred absence claim.
