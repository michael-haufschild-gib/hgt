# Route TT C75 — exact nonlinear-boundary source core

Goal ACTIVE: unconditional Lean RH proof/falsification. No global source-slope sign or RH result proved. No subagents, full/umbrella builds, numerical sampling/CAS, raised heartbeat/recursion limits, commits/pushes. One owned foreground Lean at a time; all current jobs finished. Use corpus research search; no training-based frontier assumptions.

Production (both final direct lake --old env lean audits pass, wired RHTower umbrella):
- formal/GaloisForLFunctions/RHTower/ThetaCuspRatioNonlinearBoundaryParameter.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspRatioNonlinearBoundaryCore.lean
Nine imported capstones in /tmp/tt_c75_production_axioms.lean use exactly propext, Classical.choice, Quot.sound.
P3: docs/drafts/pipeline/3-formalized/tt-exact-nonlinear-boundary-core.md.
Working log: docs/drafts/pipeline/1-in-progress/tt-third-slope-nonlinear-cone.md.
TT frontier map updated.

Let b=1/12-7h/72, R(h,s)=s*(1-h²*b*s), T=b*s, V=9-R*h², Z=(1-h*T)/3. Every admissible exact E=0 boundary state has s=t/b, 0<s<(6/5)*(361/25), with exact inverse recovery. Uses corpus failure_small_branch; no slope-sign premise.

J=b*s³*(2-h²*b*s)*(1/144-7h/432)+49*s²/5184. Exact gap T-B_cubic(h,R)=h⁴J. With existing full transverse core A and cubic core L, define C(h,s)=L(h,R)+h*J*A(h,R,h⁴J). Production nonlinearBoundary_scaledSlope proves Q(h,R,T)=h³C for all complex h,s. nonlinearBoundary_sourceSlope proves h^16*S(V,h⁻¹,Z)=C for h≠0. C(0,s)=1944*axisMinorMass-63*principalMass*s². Complete source derivative retained; never differentiate a boundary-substituted minor.

NEXT HARD TARGET: positive complete boundary core on physical domain, then interior/transverse positivity. First retain/remove the forced V factor correctly. C vanishes at V=0, so strict positivity on an enclosing rectangle is NOT the correct conjecture for C itself. Candidate quotient could be positive on the whole compact rectangle. Polynomial factor strategy: substitute R,T into scaledSlope=driftSquare*reducedScaledSlope and Q=h³C. V=9-h²R is coprime to h using the same Bezout/coprimality argument as ThetaCuspRatioScaledDriftFactor. Cancel h³ divisibility. Then attack quotient's actual global sign, not another axis/tail result. Full source quadratic, fourth Schur gap, join/all rank/RH remain open.

Large C75 exact affine-boundary scratch chain remains verified and cached, but was NOT promoted because the new minimal parametrization reuses C73 directly. /tmp/TTC75BoundarySlopeCoefficients.lean pass4 reconstructs full reduced source A+ZB in 19 V-columns. /tmp/TTC75BoundaryColumnNorms.lean has 38 standard3 capstones; /tmp/tt_c75_boundary_column_expressions_pass1.log is complete pure scalar RHS data. V^18 columns cancel, max K powers22/21. CompactRe pass2, CompactIm pass1 and CompactAssembly pass1 prove h^22*mass^-1*S=V*(A75+h*Z*B75). CompactZero pass1 proves A75(0,r)=0, B75(0,r)=268435456/2187>0. Generic negative-norm/B-positive root criterion also proved. Do not claim original positive-A/positive-norm conjecture formally refuted: A first sign/norm sign not proved. Polynomial parametrization avoids constraining the nonphysical conjugate branch.

Normalization lesson: full 5-product sum timed out despite balanced literals. Group by V-power, prove each product column reconstruction by simp/AC, then normalize 38 univariate K columns separately and reassemble. Default limits unchanged. Avoid post-raw norm_num cleanup on long sums. Failed caches always removed. Seven superseded temporary generators removed; audited .lean and expression logs retained.

Final formal lint exit1: 21 unrelated umbrella omissions and unrelated active sorry at formal/GaloisForLFunctions/RHTower/LiClockThetaGeneratorLogSlope.lean:280. No new-leaf findings; do not report repository-wide lint green. Scoped diff --check pass. No owned processes live.