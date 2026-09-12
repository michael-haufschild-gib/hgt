# Exact common-base real spectral-jet frame, 2026-09-12

## Goal remains OPEN
Full Brown–Susskind same-static-local-Hamiltonian growth–plateau–first-return, complete-circuit continuous post-ramp exclusion, and black-hole interior-volume interpretation remain unproved. The missing decisive bound is the quenched return-excised incidence action with growing replicas, occupied target image and source-fibre multiplicity, small enough for the circuit-budget-dependent post-ramp cutoff and the whole circuit union. No external novelty claim established this turn.

## New verified module
`formal/GaloisForLFunctions/HTGeometry/TwoLocalStarSpectralJetFrame.lean` (297 lines at creation), namespace GaloisForLFunctions.HTGeometry. Imported in HTGeometry.lean immediately after TwoLocalStarSpectralJetDetection (line11495 at audit). Depends only on TwoLocalStarSpectralJetDetection and FiniteWalshObservationCapacityLaw, whose cached oleans were present.

Eight public theorems compiled and new-only axiom audited:
- sum_sq_realStarWalshPacket
- orderedStarCouplingDeriv_realAction
- realStarWalshPacket_edge
- one_le_abs_commonReferenceStarJetAmplifier
- commonReferenceSpectralJet_eq_packet
- commonReferenceSpectralJet_empty
- commonReferenceSpectralJet_parseval (line218)
- balanced_real_character_commonBase_starJet_detection (line263)
All depend only on propext, Classical.choice, Quot.sound. No new axiom/sorry/admit/unsafe. No numerical experiments/native_decide. Scratch passed, final tree leaf compiled with `lake env lean ...TwoLocalStarSpectralJetFrame.lean -o .lake/build/lib/lean/...TwoLocalStarSpectralJetFrame.olean`. No lake build, full/umbrella builds, git or subagents. One owned foreground Lean at a time.

## Exact mathematics
For real k on Boolean n-cube, raw Walsh packet W_B=sum_x k_x product_{j in B}sign(x_j).
Actual common-reference star action = sum_p k(edgeEquiv i p)*blockSplitRoot(mean,starGap(c),p,u), with common h_i=3^i/3^n from previous certificate. Real action, no integrality restriction.
Literal mixed derivative in squarefree spectator S of second u derivative at c=u=0 = A_iS * W_{S union {i}}, A_iS=(-1)^|S| |S|! h_i^(-|S|-1). |A_iS|>=1.
For each nonempty B choose i=min B, S=B.subtype(j!=i). Define compensated actual derivative J_B=derivative/A_iS; J_empty=0. Proved exact actual derivative-to-Walsh equality, not an assigned jet.
Unconditional identity for EVERY real k and n:
  sum_B J_B(k)^2 + (sum_x k_x)^2 = 2^n * sum_x k_x^2.
Then for nonzero CENTERED real k, a literal star-slice derivative of order <= n+1 has magnitude >=sqrt(sum k^2). Lower bound is relative to unnormalized Euclidean coefficient norm, hence genuine normalized real-covector detection. Base independent of k and replica order.
This closes the previously recorded integer-to-real normalization gap in `mem:quantum_recurrence/common_base_star_jet_detection_2026_09_08`.

## Limits / next exact step
This is local at one explicit simple diagonal reference. It is NOT a quenched/generic-draw estimate, common quantitative neighbourhood, actual iteratedFDeriv nondegeneracy theorem, global analytic-chart estimate, or circuit exclusion. Star directions use ordinary two-local couplings, NOT a prescribed nearest-neighbour path graph. High-order jet frame is NOT a first observer-Jacobian pseudodeterminant bound.
Next step has existing applicable infrastructure: `HTGeometry/ParametricSpectralBranch.lean:199` simpleDiagonalMatrix_eigenvalueBranch constructs analytic branches for arbitrary matrix perturbations about the simple diagonal base; :218 simpleDiagonalMatrix_root_germs_unique applies to ANY topological parameter P and continuous characteristic roots converging to same simple base. `BlockSplitBranchEscape.lean:155-188` uses precisely that uniqueness to match 1-parameter explicit roots to analytic branches.
Proposed next proof: choose ONE family of branches from common starJetReferenceEnergy (injectivity already proved), define star-slice matrices with P=(spectator couplings, transverse scalar), reindex blockSplitMatrix with edgeEquiv. Both explicit roots and chosen matrix-chart roots converge to same simple base; use root_germs_unique for full P. Get eventual equality of real weighted action, then transport nested derivatives via product-neighbourhood/germ locality. Finally connect these actual restricted derivatives to full-family iteratedFDeriv. Do not assume matching branches or the desired nondegeneracy as a premise. Quantitative neighbourhood/global coarea estimate still harder after this.

## Search / external checks this turn
Used documented direct commands only (no help/source): three 300-second natural-language DEEP searches for core covariance suppression, Walsh all-real spectral coercivity, and common analytic-chart transfer; a hybrid spectral jet frame search; read candidate_lemmas/source_arguments/proof methods/ingredient_sets. New tool returned partial=false/errors=[] but semantic coverage NOT measured (reporting_budget); do NOT infer exhaustive corpus absence. Results proposed invalid bridges (Montgomery sieve occupancy to circuit suppression; coercivity_le_diagonal backward; unrelated Wu energy upper bounds). Rejected based on actual statements. Useful hits supplied genuine characteristic-root chart and uniqueness.
Broad June–September arXiv searches dephasing, observability, Walsh, small-ball. Verified primary sources:
- arxiv2608.29650, Aug30, On Number of Observation Nodes in RNNs: finite-state vs real-valued observability and activation rank loss; not a quantum source bound.
- arxiv2608.20190, Aug20, Small circumference in regular sublinear expanders: expansion alone need not give long cycles; analogy not transfer theorem.
- arxiv2607.17109, Jul19, Microscopic Origin of Dephasing in Solids: numerical/TDDFT setting not static circuit-hardness proof.
- arxiv2604.03294v2 (outside preferred recent window), Expressibility of neural quantum states: Walsh-complexity perspective. Explicit one-layer disjoint-CZ dimer state can be Walsh-flat: direct Walsh complexity cannot certify gate complexity. Read abstract and HTML proof; our use is spectral RESPONSE only, not gate complexity. No external novelty conclusion.

## Build/lint/cleanup
Axiom audit scratch `/tmp/hgt-star-frame.Uo59MS/Audit.lean`, API check scratch Check.lean. They are scheduled for deletion after recording this memory. Final .olean retained for caching. Global lint failed on FIVE UNRELATED concurrent modules unreachable from umbrellas: RHTower.ThetaCuspHawkingBMHorizonModeOuterUniformBound; RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensity; RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensityBound; HTGeometry.JetCoefficientUniqueness; HTGeometry.SecondEndpointMellinLaurentInterchange. No error about new leaf; did not modify those modules.
Requested hgt-fields-medalist skill absent; explicitly stated. Used l7 skill investigate/hostile-critique/synthesis before edits; it imposed no mathematical assumption. Session docs architecture/testing absent. No subagents, no git.

Lean details: local Fintype.ofFinite Boolean cube instance must have unique name (existing finiteBoolCubeFintype imported!). `simp_rw edgeEquiv_zero` under ite can break DecidableEq proof instances: change explicit full sum to edgeState false/true first, then rewrite sign products. Cast real signs into complex via sum/prod congr and Bool cases; plain simp leaves cast ite. Single scoped maxHeartbeats800000 for action derivative unification. Never infer math novelty from a successful compile.
