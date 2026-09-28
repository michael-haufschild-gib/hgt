# Common analytic chart and real-covector jet law — 2026-09-28

Goal remains ACTIVE. Brown–Susskind same-draw growth–plateau–first-recurrence and black-hole interior-volume claims are NOT proved. Decisive return-excised quenched incidence-action bound retaining complete occupied circuit image and fibre multiplicity remains OPEN. Initial cutoff must depend on circuit budget.

## Verified new mathematics
New leaf `formal/GaloisForLFunctions/HTGeometry/TwoLocalCommonSpectralChartJetLaw.lean`, 283 lines, namespace `GaloisForLFunctions.HTGeometry`. Imports only TwoLocalStarSpectralJetFrame. Wired in HTGeometry umbrella immediately after that import (currently line11679). Builds NOT run on umbrella or whole project.

Constructs `commonReferenceSpectralBranch n x` from existing simpleDiagonalMatrix_eigenvalueBranch at bounded ternary reference matrix. Analytic branch is on full complex matrix space, independent of selected spin, covector, and replica order. No analytic branch/root premises in its public specification: constructed and proved.

`commonReferenceStarMatrix i (c,u)` is explicit two-level star matrix reindexed to common computational basis. `commonReferenceStarRoot` is its explicit real square-root root; continuity, base equality, characteristic relation proved.

`commonReferenceSpectralBranch_star_germ` (line132): one joint neighborhood in ALL real star parameters `(c,u)`, all eigenvalue labels agree with common matrix-space chart. Uses simpleDiagonalMatrix_root_germs_unique, not separate axis matching.

`commonReferenceChartAction_star_germ` (164) transfers every real spectral covector action. Private transverse_secondDeriv_germ uses mem_nhds_prod_iff to obtain product neighborhood, then EventuallyEq.deriv and .deriv_eq. `commonReferenceChartAction_star_jet` (190) transfers literal mixed derivatives; no jet-matching hypothesis.

`commonReferenceChartJet_parseval` (223) is unconditional for all n and real k:
 sum_B ChartJet(k,B)^2 + (sum_x k_x)^2 = 2^n sum_x k_x^2.
Jets are compensated literal derivatives of the SAME analytic chart on actual star slices. Only omitted mode is uniform/global-shift covector.

`commonReferenceChartAction_balanced_detection` (231): for every nonzero balanced REAL k, exists i,S with |S|+2 <= n+1 and magnitude of literal mixed chart derivative >= sqrt(sum k²).

`commonReferenceChartAction_not_flat` (252): every nonzero balanced real k fails to be locally constant on at least one star slice through common base. Exact local-flatness obstruction removed; not approximate tube control.

## Validation and optimization
All new source checked in `/tmp/hgt-common-chart.58GXf7/Main.lean` using lake env lean, default heartbeat and recursion limits. 13 new public theorems audited with #print axioms in scratch: ONLY propext, Classical.choice, Quot.sound. No new axioms/sorry/admit/native_decide. Final tree source confirmed byte-identical to successful scratch after removing audit commands. No olean needed/created for new leaf. Scratch files and directory removed; final owned Lean PIDs52437,52506 confirmed gone. No git, no subagents.

User explicitly corrected: 'optimize lean code. no raising heartbeats hacks.' An intermediate scratch maxHeartbeats800000 override was REMOVED. Cause was unresolved type of q in continuity proof: explicit `q : ({j : Fin n // j != i} -> Real) x Real` removes inference blowup; full module now default limits. Also use explicit derivative-of-constant FUNCTION equality before second derivative; simp on partially applied deriv does not progress. Root/tendsto comparisons needed `simpa only ... using!` to handle definitional instances. No performance speedup measurement claimed.

Global scripts/formal_tools.py lint EXIT1 due unrelated concurrent unwired modules (20): RHTower CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroClassCardBound, ZetaZeroDensityPowerSaving; HTGeometry ArcsineLogIntegral, ChronologicalTensor.ArcsineMixturePotential, CubicRecoveryExponentialRate, CubicRecoveryRateConstants, CubicRecoveryRateLower, CubicRecoveryRateUpper, RecoveryDensitySeries; PhasePacketOrderReflection, RateMobiusInversion. Also existing large-file warnings. None in new leaf. Do not change others' wiring.

## Frontier next
Common-chart identification is now CLOSED. Next must quantify finite-type source suppression on actual ordinary local-ensemble parameters, then occupied-image/multiplicity-preserving coarea bound. Do not conflate high-order spectral jet frame with FIRST observer-Jacobian pseudodeterminant. Still no actual full-family iteratedFDeriv certificate, explicit n-controlled chart radius, ensemble probability, global sheet bound, or full circuit exclusion. Star slices need star edges, not fixed nearest-neighbor chain.

KleinbockMargulis.NonDegenerate.prop_3_4 already proves finite-type local (C,1/(d*l))-goodness for smooth maps with REAL covector iteratedFDeriv separation. Constants/neighborhood existential. Its FiniteOrderNondegeneracy compactness result also exists. Neither gives required global quenched incidence bound. PolynomialSublevelSphere.volume_sublevel_le_of_direction and PolynomialLineSlice.volume_polynomial_sublevel_le retain degree-dependent exponent; they do not solve this transfer. Do not re-prove general IFT or these known sublevel results.

## Search / external audit
Custom hybrid/deep searches used methods/source_arguments. Initial deep branch-chart query partial:false but semantic coverage unmeasured; best exact applicable theorem was existing ParametricSpectralBranch.simpleDiagonalMatrix_root_germs_unique (P arbitrary topological, enabling joint real parameter). Reranker offered irrelevant Bottcher/Fokas candidates; actual applicability checked. Later deep finite-type-to-tail query and broad single-word sublevel query PARTIAL due Qdrant timeout/local-worker disconnect; not exhaustive. Broader sublevel found above polynomial slicing modules.

Broad arxiv searches June–Sept2026: current 2606.17762 v3 Aug19 title 'Horizon-Uniform Sensitivity and Decay of Terminal Reward Perturbations in Discrete-Time Pontryagin Systems' assumes hyperbolic reduced map and endpoint transversality; cannot transfer hyperbolic contraction to compact quantum recurrence. 2609.04084 boundary transversality optimal-control necessary conditions, not source-tail estimate; 2608.31026 toric integral transversality. Further broad oscillation queries returned 2606.22444 adiabatic time-varying beam and 2609.13286 atmospheric Kelvin-wave scale analysis, no applicable proof extracted. No external novelty established, no paper/Nature claims made.

Fields-medalist requested skill file /Users/michael/.codex/skills/l7/hgt-fields-medalist/SKILL.md absent. Announced fallback, read available l7 skill fully and followed adversarial implementation review; maintain user conjecture/proof/fail loop. No scientific-method-specific tools available beyond ordinary tools. User requires every turn proof chain, obstacle, last progress, next attack; concise updates and no heartbeat overrides.

See mem:quantum_recurrence/real_covector_spectral_jet_frame_2026_09_12 for prior frame source.