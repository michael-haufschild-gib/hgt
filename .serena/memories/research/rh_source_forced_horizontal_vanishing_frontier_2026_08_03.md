# RH source-forced horizontal vanishing frontier (2026-08-03)

New module: `formal/GaloisForLFunctions/RHTower/RiemannSourceForcedHorizontalVanishingFrontier.lean`.

Exact unconditional chain:
- canonical source parameter `riemannSourceGammaCoPoissonHorizontalParameter rho := -riemannReflectedSourceEntropy rho`;
- parameter equals real Green fracture;
- constructed Gamma/co-Poisson polarized boundary defect is faithful in parameter;
- reflected Gaussian line Wronskian equals parameter times nowhere-zero positive Hermitian pair scale;
- real multiplicity-weighted centered Xi outer charge equals `-m/2` times parameter;
- `XiSourceForcedHorizontalVanishing` is equivalent both to literal vanishing of reflected prime-tail entropy on every Xi divisor fibre and to vanishing of every unsquared Gaussian Wronskian;
- `XiSourceForcedHorizontalVanishing ↔ RiemannHypothesis`;
- hence `riemannHypothesis_of_sourceForcedHorizontalVanishing` has exactly one premise.

Hostile interpretation: all reporter/transport/factorization gaps in this reduction are closed. This is not an RH proof. Remaining premise is exactly source-forced vanishing itself, logically equivalent to RH; future work must derive it from a genuinely independent arithmetic source identity.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/RiemannSourceForcedHorizontalVanishingFrontier.lean` passed.
- `lake build GaloisForLFunctions.RHTower.RiemannSourceForcedHorizontalVanishingFrontier` passed (11086 jobs).
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- full lint no longer flags this module; repo lint still fails on unrelated concurrently-added unreachable modules.
- no stale Lean process from this task.
