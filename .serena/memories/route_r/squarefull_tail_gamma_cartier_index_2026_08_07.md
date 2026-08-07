# Route R squarefull-tail Gamma–Cartier index (2026-08-07)

Formal module: `RHTower/RouteRSquarefullTailGammaCartierIndex.lean`; formalized card: `docs/drafts/pipeline/3-formalized/route-r-squarefull-tail-gamma-cartier-index.md`.

Conjecture loop: reflected product equality falsified; reciprocal KMS cyclicity falsified; explicit level-two tail projection survived.

Let `E2 = {K | {p | 2 ≤ K p}.Finite}` for Euler activation measure `μ_σ`. Proved `μ_σ(E2)=0 ↔ σ≤1/2`, reflected balance `μ_σ(E2)=μ_(1-σ)(E2) ↔ σ=1/2` on `0<σ<1`, and off-center mutual singularity of reflected measures with `E2` or its complement as explicit witness. Important correction: center pair is `(0,0)`, not `(1,1)`.

At Xi divisor `rho`, proved `RouteREulerGammaSquarefullTailBalanced rho ↔ routeRTwoThreeGammaCartierTransportPort rho=0`, and pointwise/global arithmetic-horizon globalization iff this single source projection balance. No RH/critical-line/vanishing assumptions.

Scientific delta: full GNS/Kakutani comparison is unnecessary; remaining producer is exactly `∀ rho, RouteREulerGammaSquarefullTailBalanced rho`, to derive independently from pre-divisor Euler–Gamma Stokes structure. This work does not prove balance or RH.

Audit: targeted `lake env lean`, module `lake build`, lint passed; axioms `[propext, Classical.choice, Quot.sound]`.