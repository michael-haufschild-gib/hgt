# Unconditional finite Weil triangle correction with sharp edge count

Persistent user goal is RH proof via arithmetic conservation/Noether and sustained conjecturing. RH NOT proved or falsified; goal stays active. Previous turn actual prime triangles was verified progress. Current turn extends beyond isolated three-source families to every finite family, with all new couplings included.

Repo /Users/michael/Documents/code/hgt/formal. One own foreground Lean build at a time, final leaf commands lake --old env lean ... -o corresponding .olean. No full/umbrella builds, no numeric experiments, no sorries/new axioms/heartbeat hacks, no commits/agents. Other chats change/commit/build concurrently. Preserve their files. Existing tracked deletion TriangleAxiomAudit.lean is our prior scratch cleanup, do not restore it.

## New bound (verified in four new leaves)
For any finite real symmetric M and real coefficient vector x, let O_ij=0 if i=j, otherwise M_ij. Edge penalty E(p,x,y)=|p|(x²+y²)+2pxy = max(p,0)(x+y)²+max(-p,0)(x-y)² >=0.
Triangle gain g(p,q,r) is max of four minima, using positive parts of sign patterns (+++), (--+), (-+-), (+--). Always nonnegative; strictly positive for strict (-,-,+); zero if any entry zero. Unconditional g*(x²+y²+z²) <= E(p,x,y)+E(q,x,z)+E(r,y,z).
Define L=Σ_i (M_ii-Σ_j|O_ij|)*x_i² and C=Σ_ijk g(O_ij,O_ik,O_jk)*(x_i²+x_j²+x_k²)/(6*max(1,n-2)), n=card index type interpreted real. Then L+C <= Σ_ij M_ij*x_i*x_j.
Normalization is SHARP distinct edge count n-2 (max1 handles degenerate empty/small families). Initial version used n, then strengthened; use latest denominator everywhere.

Exact count proof: sum all ordered triangle edge penalties =3n ΣorderedEdges E. Gain terms vanish with repeated vertices. Add back repeat penalties pointwise: if i=j then2Eik, if i=k then2Eij, if j=k then2Eij. Each summed refund=2ΣE, so sumTriangleGain+6ΣE <=3nΣE. Compare n-2<=max1(n-2) using E>=0, divide. No full inequality assumed.

For actual CCM form, M_ij=ccmWeilRealPolar a (u i)(u j), symmetric unconditionally. Proved full finite real Gram expansion and universal finite triangle bound for EVERY finite family u in actual form domain, no support/sign/positivity premises.

Constructed prior genuine prime triangle persists under EVERY finite extension by arbitrary other CCM form-domain vectors, with every coefficient x:Fin3⊕ι→ℝ. Selected gain m>0 survives as m*(x0²+x1²+x2²)/(6max1(card(Fin3⊕ι)-2)). Added arbitrary couplings are inside separate lower bound; the total bound is NOT asserted nonnegative.

## Four files and symbols
1 SignedTriangleCollectiveGap.lean: signedEdgePenalty, eq into two positive-part squares, nonneg, pos_part, neg_part; signedTriangleGain, nonneg, eq_zero_of_zero, pos_of_neg_neg_pos, signedTriangleGain_lower. Uses four gauge versions of prior frustratedTriangle_weighted_gap.
2 FiniteSignedTriangleBound.lean: finiteSignedOffDiagonal, finiteSignedQuadratic, finiteSignedSeparateLower, finiteSignedTriangleCorrection; correction_nonneg; quadratic_diagonal_off; quadratic_edge_decomposition; sum_triangle_edges; sum_triangle_edges_distinct_bound (generic T vanishing repeats, symmetric E zero diagonal); finiteSignedTriangle_lower; single_triangle_le_finiteSignedTriangleCorrection.
3 CCMFiniteTriangleBound.lean: ccmWeilRealPolar_symm/self/zero_left/add_left/smul_real_left/right/sum_left/right; ccmRestrictedWeilSourceQuadratic_real_sum; ccmRestrictedWeilSourceQuadratic_finite_triangle_lower.
4 CCMPrimeTriangleExtension.lean: ccmWeilTriangleExtension = Sum.elim (Fin3 if0u if1v elsew) extra; ccmWeilTriangleExtension_lower; exists_cofinal_ccmPrime_triangle_extension_gain (N) constructs actual primes p>=N,q>2p, supports at0/logp/logq,r>0,m>0, then arbitrary finite extra family and all real coefficients bound.

All four final leaf audits PASSED clean, .olean outputs current. They are wired immediately after CCMWeilTriangleNoether in umbrella. No full build. Source scan no sorry/admit/axiom/maxHeartbeats/#eval/native_decide; diff --check clean.

## Current final gates in progress
Combined TriangleExtensionAxiomAudit.lean PASSED exit0: eight key results only propext, Classical.choice, Quot.sound; no added axioms or sorryAx. Scratch removed afterward. Index refresh PASSED exit0 (5 changed,0 removed). No own Lean process remains. Lint --check-generated FAILED only on unrelated ongoing unwired modules MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, WildSaddleAdaptiveDepthRelocation, XiGaussianRootOrientationBound, ZetaZeroDensityPowerSaving, plus generated metadata raced with concurrent source edits. Final index refresh PASSED exit0 (4 changed,0 removed), clearing generated files at final refresh. All own processes terminal; scratch removed. No full build, no commit. Do not wire others' unfinished modules. All four new imports confirmed, diff --check clean.

## Lean details
- max_mul_of_nonneg requires TWO operands before proof: max_mul_of_nonneg _ _ hm.
- `if_pos rfl` in simp only failed on if True; use ite_true after reflexivity simplification.
- Finset.card_univ needed to equate univ.card with Fintype.card.
- Unqualified add_le_add_left is shadowed/opposite convention in corpus; use `apply add_le_add le_rfl`.
- sum_triangle_edges does not need DecidableEq; `omit [DecidableEq ι] in` avoids warning.
- Scalar inner simplification needs explicit E:=CCMArchimedeanFormDomain a and E:=suzukiApertureHilbert a (from prior turn). Finite polar expansion via add/scalar/sum lemmas audited first attempt.
- Fin3 source indexing `Sum.elim (fun i=>if i=0 thenu else ifi=1 thenv elsew) extra`; simp resolves 0/1/2 and off-diagonal values without enumerating source families.

## Next mathematical frontier
Need prove nonnegative full global lower bound in a suitable decomposition, not merely a nonnegative correction. Generic corrected Gershgorin rows cannot be assumed positive in every presentation. Promising diagnostic, not yet formal: positive rank-one constant matrix Mij=p>0 on n>=3 has L=(2-n)pΣxi² and triangle correction ((n-1)/2)pΣxi², hence combined lower=((3-n)/2)pΣxi². For n=4 this is negative although Q=p(Σxi)²>=0. Thus even sharp triangle averaging can lose higher-order coherence; a larger-clique identity should improve it: Σ_{i<j}(xi+xj)²=(n-2)Σxi²+(Σxi)². Formalize this obstruction and higher-clique correction rather than pretending triangle bound alone suffices.
Actual many-prime packet construction may supply full cliques after hub sign flip: negative prime hub edges and positive atom-free leaf edges, with primes pairwise ratios>2. Need finite prime selection/common radius infrastructure, no pivot just because absent.
Also immediate Noether continuation: extend two-channel phase energy to arbitrary finite families. Real-bound cos/sin sum makes total triangle phase correction angle-independent: 3Σg/(6max1(n-2)). Common phase shift remains exact symmetry; derive finite force balance/total momentum. Literal single complex phase energy requires real-imag bridge when appropriate; don't conflate with two-channel definition.
Search tool `research "clique quadratic"` found0; "signed complete graph" found only unrelated modules (MobiusBoundaryOppositeSignTransport, PrimeCoherenceTailReconstruction, CCMActualHeadMatchedQuantileLorentzGraphWall, XiGammaSixWoldJordanSignedMarginal, CCMFUSuzukiCompletedRieszGraphEnergy). No source theorem duplicate identified.

Prior memory: `mem:research/noether_actual_prime_frustrated_triangles_2026_09_27`.