# Route N C34: arbitrarily sharp residual localization

Date: 2026-08-10.

Module: `formal/GaloisForLFunctions/RHTower/XiMassTimelikeGlancingResidualCriterion.lean` (umbrella-wired).

Results:
- Defines exact timelike/glancing residual finite-cone line-bound criterion.
- Proves full Route T centered-cone line bound iff residual line bound, by adding/subtracting C33's uniformly bounded sharp-spacelike contribution.
- For every `alpha > 1`, constructs legal `a = alpha / sqrt(alpha^2 - 1)` with `a > 1/2` and `xiMassSpacelikeSharpSlope a < alpha`.
- For every `alpha > 1` and `sigma > 0`, constructs legal Route T parameters `a,c,d` and proves exact equivalence `RiemannHypothesis ↔` height-uniform boundedness of residual centered finite sum supported on `log n < alpha*u`.
- Direct `lake env lean` and explicit olean compile pass. Scratch `#print axioms` audits expose only `propext`, `Classical.choice`, `Quot.sound`.

Interpretation: all strict spacelike directions can be discharged with cone slope arbitrarily close to 1. Open arithmetic obstruction is intrinsic to true timelike-plus-glancing causal incidence, not a contour-optimization loss or fixed mass choice. Next conjecture: identify Route T critical mass profile as a non-diagonal Deninger cross-current, matching the corpus-wide failure of diagonal positive forms.