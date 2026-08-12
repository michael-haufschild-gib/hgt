# Route U polynomial-Gaussian local concentration formalized (2026-08-12)

Formal module: `formal/GaloisForLFunctions/RHTower/PolynomialGaussianLocalConcentration.lean`, umbrella-wired through `RHTower.lean`.

Exact unconditional capstone `RHTower.integral_Icc_norm_routeUPolynomialGaussianDensity_le`: for every real polynomial Q, positive heat time t, and R>=0, compact native mass on [-R,R] is at most `18*R*sqrt(t*(Q.natDegree+1))*routeUPolynomialGaussianMass Q t`. Zero polynomial/degree zero included; no mass division, RH premise, coefficient premise, or computation.

Supporting exact theorems: `norm_deriv_polyGaussSchwartz_sq_le` (derivative energy <=16(n+1) mass), `norm_polyGaussSchwartz_sq_le` (point value <=9 sqrt(n+1) mass), and `integral_Icc_norm_polynomialGaussianEnergy_le`.

Structural Route-U discovery: C43-Y (24.135) does not need Mehler/projector infrastructure. Finite oscillator energy plus existing 1D Gallagher-Sobolev point evaluation yields correct sqrt-degree local concentration, then native scaling closes it.

Verification: direct `lake env lean` clean; `lake build GaloisForLFunctions.RHTower.PolynomialGaussianLocalConcentration` succeeded 8827/8827; axiom audit only `[propext, Classical.choice, Quot.sound]`; no banned declaration tokens. Global lint failure was only unrelated pre-existing unreachable modules; target is umbrella-reachable and <700 lines.

Card: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/mass-shifted-polynomial-gaussian-local-concentration.md`. Frontier map updated. Remaining parabolic wall is literal completed prime-Gamma assembly, global lower envelope, and Gamma-tail domination—not local small-ball.