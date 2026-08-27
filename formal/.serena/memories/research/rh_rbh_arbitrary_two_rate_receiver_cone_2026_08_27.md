# RBH arbitrary two-rate receiver cone (2026-08-27)

Formal module: `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatArbitraryTwoRateReceiverCone.lean`.

For every `0 < lambda < mu`, proved that `sinh(mu*t)/sinh(lambda*t)`
maps `(0,∞)` strictly increasingly and onto `(mu/lambda,∞)`. New analytic
infrastructure includes strict monotonicity of `x*cosh x/sinh x`, exact wall
limit, atTop divergence, and exact quotient range.

Complete signed classification:
`∀t, a*sinh(lambda*t)+b*sinh(mu*t)=0 ↔ t=0` iff
`(b=0 ∧ a≠0) ∨ (b≠0 ∧ 0≤b*(lambda*a+mu*b))`.
Thus first wall derivative controls exact boundary even for incommensurate rates.

Proved arbitrary real-power physical aperture factorization and RH equivalence.
Explicit irrational receiver: rates `(1,sqrt 2)`, weights `(-sqrt 2,1)`.

Verification: direct Lean, targeted module build, axiom audit passed.
Axioms only `propext`, `Classical.choice`, `Quot.sound`.

Remaining RBH boundary: ≥3 incommensurate rates, collision-grouped non-diagonal
channels, infinite/non-polynomial packets.

Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-arbitrary-two-rate-receiver-cone.md`.