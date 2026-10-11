# Finite raw convex order — formalized 2026-10-11

User constraint: mathematical sources ONLY local Lean corpus and installed Lean dependencies. NO WEB, external papers, or numerics. Do not reread papers. Endless research goal remains ACTIVE; this increment is progress, not completion of whole goal.

Card: docs/drafts/pipeline/3-formalized/finite-weil-raw-convex-order.md. Five new RHTower leaves, 17 public theorems, 0 definitions, all native compiled sequentially with empty logs. Native final scratch audit includes all 17 axiom checks and 21 explicit API witnesses; all axioms exactly propext, Classical.choice, Quot.sound. Metadata issues []; 10 direct import records; 9 incoming edges; all 5 umbrella imports present once. Scoped git diff --check passed. Local lexical search refresh returned all 5 principal/companion roots.

Mathematics: n=r+1, A=k+2, m canonical edge mass, X_i=i-E[i], Y_i=n(T_i-E[T]). Existing residual F(i)=nT_i-i has F'=A²/((A+x)(A+x+1))-1 in [-1,0] for x>=0. Thus Y and X-Y are increasing and centered. Every globally convex real phi has increasing right derivative and supporting slopes. Weighted Chebyshev gives E[phi'_+(Y)(X-Y)]>=0, hence E phi(Y)<=E phi(X). All r,k, no width/asymptotic premises, no smoothness assumption. Convex function encoded as structural subtype {f : R->R // ConvexOn R univ f}.

Sources under formal/GaloisForLFunctions/RHTower/, namespace RHTower:
- WeilLogShiftRawOrder (8): finiteWeilEdgeCorrectionProfile_hasDerivAt; finiteWeilEdgeResidualProfile_antitoneOn; finiteWeilEdgeCorrectionProfile_monotoneOn; finiteWeilCanonicalRawCorrectionValue_monotone; finiteWeilCanonicalRawDefect_monotone; finiteWeilCanonicalRawIndexValue_mean_zero; finiteWeilCanonicalRawCorrectionValue_mean_zero; finiteWeilCanonicalRawDefect_mean_zero.
- WeilLogShiftLawCovariance (2): finiteWeilLaw_covariance_pairwise exact weighted two-copy covariance identity; finiteWeilLaw_monotone_covariance_nonneg for arbitrary finite linearly ordered Law and OrderHom observables.
- WeilLogShiftConvexRightSupport (2): finiteWeilConvex_rightDeriv_monotone; finiteWeilConvex_right_support. Uses local Mathlib.Analysis.Convex.Deriv one-sided derivative bounds.
- WeilLogShiftRawConvexOrder (2): finiteWeilCanonicalRaw_convex_sum_le line13; finiteWeilCanonicalRaw_convex_integral_le line46, actual probability laws from prior RawTransportLaw.
- WeilLogShiftRawConvexMoments (3): finiteWeilCanonicalRaw_even_moment_le line12; finiteWeilCanonicalRaw_variance_le line19, n²*Var(T)<=Var(i) all r,k; finiteWeilCanonicalRaw_exponential_moment_le line33, all real tilts a.

API notes: convexOn_exp is GLOBAL, not Real.convexOn_exp. Even.convexOn_pow valid. Monotonicity from derivative is in Mathlib.Analysis.Calculus.Deriv.MeanValue. Beta-reduce the instantiated correction-profile monotonicity inequality with `dsimp only at h` before rewriting finiteWeilEdgeResidualProfile_at_index; rw alone could not find profile under applied lambda.

Artifacts /tmp/hgt-raw-convex-{api.lean,api.log,metadata.py,metadata.json,declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,roots-search.json,lint.log,close.py}; individual /tmp/hgt-<Leaf>.log. All owned Lean, search, lint, metadata, close processes terminal.

Global lint at snapshot failed with 11 foreign errors and 367 warnings; no diagnostics in five new leaves. Foreign unreachable RHTower modules CCMPolarOddPrimeJumps, PaperHurwitzCompactCharacter, PaperHurwitzEnergyDomain, PaperHurwitzPowerRegularization, PaperHurwitzSourceIdealBridge, PaperHurwitzWallApproach, WeilLockSpectralSystem, XiSliceHeatLargeHeightPositivity; HTGeometry PaperDiagonalStrongConvergence, QKrawtchoukCompanionTriangular. One sorry CCMPolarOddPrimeJumps:104 ccmPolarOddSource_eq_core_add_atoms. Do not edit unrelated active files. Foreign set changes; rerun lint only for next increment final audit.

No coupling optimality, rawGap=W1, or primal-dual equality proved; these remain separate potential next bridges. Do not claim global novelty. No new research topic started after closure.