# RN-P-7d: simultaneous two-node port zeros cross together

Status: source convexity, extrapolation defects and simultaneous-zero free
derivative signs formalized and audited. The application to Schur-flow
crossing uses the paper flow identities below; no complete continuation
theorem is claimed.

Lean: `ThetaTwoNodePortTransversality.lean`, namespace `RHTower.ThetaPort`.
Public theorems: `strictConvexOn_slope`, `strictConvexOn_weightedSlope`,
`two_node_extrapolation_defects_neg`, `simultaneous_port_free_derivatives_neg`.
Targeted `lake --old build`, umbrella wiring, and final
`lake env lean GaloisForLFunctions/RHTower/ThetaTwoNodePortTransversality.lean`
passed. All four axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`.

Route RN remains arbitrary-rank positivity of the literal first-moment theta
tail kernel. This resolves one local obstruction in the proposed Schur-flow
argument, not the whole induction.

Let `k` be the literal theta source and `p=-(log k)'`. For
`0≤x₁<x₂<y`, put

    a=(x₂-y)/(x₂-x₁), b=(y-x₁)/(x₂-x₁).

Then the two strict inequalities are

    a p(x₁)+b p(x₂)-p(y)<0,
    a x₁p(x₁)+b x₂p(x₂)-y p(y)<0.

Proof: the corpus proves `(log k)''''<0` everywhere and vanishing odd
center jets. Hence `(log k)'''<0` on `(0,∞)` and `p''>0` there.
Thus `p` is strictly convex on `[0,∞)`. The corpus also proves strict
log concavity, giving `p'≥0`. Therefore
`(t p(t))''=2p'(t)+t p''(t)>0` on `(0,∞)`, so `t p(t)` is strictly
convex on `[0,∞)`. Strict adjacent-secant increase for each function gives
its value at `y` strictly above extrapolation from `x₁,x₂`, exactly the
displayed inequalities. No numerical source estimates enter.

Application to actual Schur flow: write
`A=k(y)-c₁k(x₁)-c₂k(x₂)` and
`B=y k(y)-c₁x₁k(x₁)-c₂x₂k(x₂)`.
If `A=B=0`, elementary elimination forces
`c₁k(x₁)/k(y)=a` and `c₂k(x₂)/k(y)=b`.
The existing paper identities give `A'=W` and `B'=C` at such a zero,
where

    W/k(y)=a p(x₁)+b p(x₂)-p(y),
    C/k(y)=a x₁p(x₁)+b x₂p(x₂)-y p(y).

Both derivatives are strictly negative. Thus both residuals have the same
sign sufficiently near this simultaneous zero, positive before it and
negative after it. In particular their product is positive on both
punctured sides. This removes the simultaneous-zero corner as an entry
point to a negative product for two earlier nodes.

Remaining hard gaps: crossings where just one residual vanishes, and
the corresponding projection-sign problem with arbitrarily many earlier
nodes. No unconditional three-node or all-rank positivity is claimed.

Corpus audit: `research 'thetaCuspLogDecaySlope convex' --mode lexical`
returned no hits. Dependencies verified in `ThetaTailTwoPointPositivity`
(negative third jet), `ThetaCuspLogFourthNegative` (negative fourth jet),
and `ThetaCuspGlobalReflectedRiccati` (monotone decay slope).
