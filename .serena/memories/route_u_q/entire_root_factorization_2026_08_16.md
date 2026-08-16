# Route U entire root factorization (2026-08-16)

Closed prior global squared-variable root quotient seam.

Lean:
- Modified `formal/GaloisForLFunctions/HTGeometry/AnalyticRootFactor.lean` with `GaloisForLFunctions.HTGeometry.exists_positive_pow_factor_of_entire_root`: a root of a nonzero entire function has positive finite order and global entire quotient nonzero at root.
- Added `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeEntireRootFactorization.lean`.
- `routeUHardEdgeSquaredAngularApprox` has only possible pole `-a²`.
- `analyticOnNhd_routeUHardEdge_angularLocallyUniformLimit`: if `a_n>0`, `a_n→∞`, and approximants converge locally uniformly, poles escape each fixed unit ball, eventual local holomorphy gives entire limit.
- `norm_routeUHardEdge_strongLimit_eq_one`: strong limit of unit-normalized packets has norm one.
- `exists_ne_zero_routeUHardEdge_angularLocallyUniformLimit`: same-subsequence L² representative identity plus norm one excludes identically-zero entire limit.
- `exists_positive_entireRootFactor_routeUHardEdge_angularLocallyUniformLimit`: every physical root `F(r²)=0` has automatically supplied `m>0`, entire `H`, `H(r²)≠0`, and global `F(u)=(u-r²)^m H(u)`.
- `routeUHardEdge_angularLocallyUniformLimit_root_has_literal_compact_factorization`: supplies exact literal compact L¹∩L² source and multiplicity-preserving Fourier factor without assuming entireness/continuity/factorization.

Verification:
- Both leaf files passed direct `lake env lean`.
- Exact leaf builds passed; no umbrella build.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- New module wired into `formal/GaloisForLFunctions/RHTower.lean`.
- Card: `docs/drafts/pipeline/3-formalized/route-u-entire-root-factorization.md`.

Universal principle: L² compactness prevents state collapse while singularity evacuation to infinity forces global analyticity. Together they make root quotient automatic. Route U remaining bridge is incoming PSD/strictness or equivalent pre-wall exclusion of nonzero null state; quotient/admission is closed.