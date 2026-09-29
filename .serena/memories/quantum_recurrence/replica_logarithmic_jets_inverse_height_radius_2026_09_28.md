# Replica logarithmic jets and inverse-height radius — 2026-09-28

## Status
Two new verified leaves; Brown–Susskind and complete-circuit exclusion remain UNSOLVED. No paper edits, git, subagents, full/umbrella builds, resource-limit changes, computations or new axioms. Requested hgt-fields-medalist skill path absent; fallback L7 protocol was followed. Prior optimization is separate: mem:quantum_recurrence/weighted_sublevel_proof_optimization_2026_09_28.

## Files / exact results
1. formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetDepthLaw.lean
- integerStarWalshPacket_subcube_sum: sum of Walsh coefficients over subsets B equals 2^|B| times integer subcube marginal.
- integerStarWalshPacket_dvd_of_proper_subsets_zero: first surviving coefficient divisible by 2^|B|.
- exists_integerStarWalshPacket_degree_mass: nonzero integer character has minimal-degree B with 2^|B| <= natAbs coefficient.
- integerStarWalshPacket_le_replica_mass: realized r-replica character has every Walsh coefficient <=2r.
- pauliReplica_logarithmic_jet_detection (line154): zero alternative or actual full-Pauli Frechet star-direction jet with S satisfying 2^|S|<=r, order <=min(n+1)(Nat.log 2 r+2), magnitude>=2^(|S|+1) at0.
- pauliOrderedReplica_logarithmic_jet_detection (223): unconditional ordered tuple form; equal multiplicities retained, no assumed nonresonance.
- pauliOrderedReplica_uniform_logarithmic_jet_detection (254): fixed n,r positive common full-source ball, genuine real characteristic roots, detectors selected before source p, magnitude>=1. Radius initially existential.

2. formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetRadiusLaw.lean
- pauliOrderedReplica_inverse_height_jet_detection (159): for each n, exists c_n>0 BEFORE all r, all ordered r-replica characters either equal multiplicities or have one fixed logarithmic-order detector of magnitude>=1 everywhere on full source ball c_n/(r+1). Actual real characteristic-root chart on same ball. No premises beyond n; main theorem is closed.
- Proof: finitely many elementary spectral jets are differentiable at0; differentiability gives IsBigO_sub; finite sums bound all elementary local Lipschitz constants by M_n. Establish jet linearity in real covector on common smooth neighborhood. Variation<=sum|k_x| M_n norm(p). Ordered replica coefficient mass<=2r; origin magnitude>=2; choose c_n=min(rootRadius,variationRadius,1/(2M_n)).
- General perturbation argument is standard, not claimed as novel physical principle. No estimate on n-dependence; source neighborhood shrinks with r. Not high-probability for ordinary ensemble, not growing-replica coarea/circuit exclusion.

Both wired into HTGeometry.lean adjacent to TwoLocalPauliSpectralJetLaw at lines11683-4 at time of work.

## Verification
Scratch /tmp/hgt-replica-depth.lrH8Zo/ReplicaDepth.lean all7 public declarations checked exit0, standard axioms only [propext,Classical.choice,Quot.sound], session64927.
Built only needed depth leaf olean via lake env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetDepthLaw.olean GaloisForLFunctions/HTGeometry/TwoLocalPauliReplicaJetDepthLaw.lean; exit0 session36308, needed for second scratch import.
Radius scratch initial check had annotation/syntax errors; corrected batch passed exit0 session21961; new public theorem standard axioms only. Repository copies preserve checked proof bodies; only new explanatory header in radius, audits excluded from tree. No Radius olean built (not needed).
Global scripts/formal_tools.py lint run once through run_guarded600, exit1:17 unrelated unwired modules (10 RHTower,7 HTGeometry). No new leaf lint failures. Do not claim global lint green. No owned Lean/search processes left; scratch copies cleaned after integration.

## Provenance / novelty
Minimum-volume Boolean-trade mechanism classical: https://arxiv.org/abs/1810.02296 (Ghorbani/Kamali/Khosrovshahi/Krotov; min trade volume2^t). Generic arithmetic mechanism NOT a new discovery. Exact specialization to existing full Pauli spectral jet certificate is formal progress; no literature-wide novelty claim established.
Newest relevant inspected https://arxiv.org/abs/2609.26885 https://arxiv.org/html/2609.26885v1 Lee/Pilatowsky-Cameo/Choi sustained complexity growth (Sep22 2026): late-time almost-all exponential complexity, explicitly not linear growth; finite-time argument uses replica minimum gaps and heuristic scaling SecVII.2. Does not supply required same-draw continuous first-circuit-return estimate.
Custom hybrid/deep/method searches used repeatedly (Walsh/depth, incidence action, uniform jets, factorial analytic bounds, differentiable local Lipschitz, replica height radius). Most source_only; latter deep searches partial with semantic_coverage_unavailable. Do not infer exhaustive novelty/no-duplicate results. StarUniformJetDetection is only a star slice; no promotion to full ensemble.

## Frontier / next meaningful step
Actual missing estimate unchanged N_inc*A_exc < [c (eps_w-eps_n)/(vT)(1-eps_w^2)^r]^2, retaining occupied complete-circuit endpoint image, every source fibre sheet, growing replicas, removing circuit-budget-dependent initial easy interval. Minimum gap anti-concentration not substitute.
RHTower/StaticChoiCarrierWeightedPurityLaw (104) bounds return-excised action by r!d^-r + weighted near action mass +exp(-(Tdelta)^2/2), given maximal projectivity. It loses occupied carrier by replacing with full replica purity.
RHTower/ReturnExcisedResidualOverlapFirstReturnLaw (209) remains receiver with required haction premise, not producer.
New local jets alone do NOT solve this. Need actual occupied-image/action estimate and system-size/ensemble control; avoid another cosmetic corollary. Potential use of logarithmic order in oscillatory bounds must confront shrinking source ball and r-dependent constants, not silently claim global or ordinary-ensemble result.
