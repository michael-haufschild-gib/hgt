# Interior attack on the frozen positive-measure implication

The goal remains a source proof of complete C5 compensation, followed by the remaining RH-chain steps. The existing conjecture B1 is unchanged: positive spectral-tail replacements with actual left-endpoint Laplace mass and the listed source and curvature gates should have nonnegative complete compensation. Optimization is a hostile test of that claim, not a substitute for it.

## Domain audit

The actual theorem `thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos` requires `A(u-t)≥6`. The earlier boundary scripts filtered `A(u)≥6`. Their larger-domain observations are valid numerical observations but cannot all be called observations inside the proved structural chamber. Separate cases by the left scale. The pure-lowest-atom weakest reserve at left scale `π` is outside the theorem's domain. This correction does not erase any witness or strengthen the frozen conjecture to rescue it.

## Inverse experiment

Vary positive three- and four-atom measures with support at least three, their atom weights over many orders of magnitude, left scale, displacement, and homotopy position. Work in both the extended domain `A(u-t)≥π` and the actual theorem domain `A(u-t)≥6`. Minimize the complete curvature-to-critical-curvature ratio where the first two channels are adverse. Retain all gates, including positive curvature; record any nonpositive normalized Bose slope separately. A ratio below one is a candidate counterexample requiring independent high-precision recomputation. This searches between the previously conditioned boundaries, not on either of them.

Use short differential-evolution runs with independent seeds and bounded local polishing. A finite optimizer success means only a best-found candidate, not a global minimum. Save every endpoint and its source parameters. Recompute leading candidates through the existing mpmath source helpers, independent of the floating-point objective. Use actual-mass and mass-deformed controls to distinguish a gap/support effect from a density-size effect if the first results warrant it; freeze any such additional claim before testing it.

## Corpus ideas

The starting ideas are the retained-coordinate square decomposition, the observed separation of two source boundaries, the quotient monotonicity mechanism in `ThetaCuspLikelihoodHomotopyLowerTransport`, and the separation of transverse and axial obstructions in `PositiveSourceQuadraticStability`. The latter is an example of a proof by different mechanisms, not an imported sign theorem for this source. The unresolved mathematical question is whether source realizability quantitatively prevents simultaneous shortages in both mechanisms.

All mathematical computations run on the authorized Runpod, at most eight workers, one BLAS thread per worker, and a 120-second batch cap. No numerical optimizer output enters Lean.

## Adaptive unbounded-node continuation

The interior optimizers reach the remote-node cap near 31,626 with weight about `7×10^-6` in the extended domain. The first moment remains moderate while the second moment grows with node size. The reported reserve is around 19, rather than the 82,158 seen at `r=β/2`.

**Frozen hostile continuation C1:** starting from each domain's best source, replace the negligible intermediate atom by a two-atom measure at 3 and `g`, and hold the conditional first-moment excess `c` fixed with weight `ε=c/(g-3)`. Increase `g` geometrically beyond the optimizer cap, keeping actual mass, geometry, and homotopy position fixed. Test complete compensation and curvature at high precision. This directly attacks B1; it does not add a new assumption to it. Locate separately the first complete-compensation sign crossing and the curvature crossing, if present. If compensation crosses first, independently validate an interior witness with all B1 gates.

**[BRIDGE] analytic mechanism to investigate:** at fixed geometry and homotopy parameter zero, a remote atom with weight proportional to `1/g` has bounded first moment and diverging second moment. The second-moment contributions to `H'` and `H''` have different coefficients. Derive their exact affine dependence before claiming any source counterexample theorem. A numerical counterexample to this enlarged source class still does not disprove the literal theta inequality or RH.
