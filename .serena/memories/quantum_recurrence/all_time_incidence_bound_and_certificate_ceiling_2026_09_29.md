# All-time static incidence bounds and certificate ceiling

Goal still open: full same-draw Brown–Susskind growth/plateau/first-complete-circuit-return for ordinary fixed-q static local H, with maximal complexity and permanent local/Haar separation. User updated goal 2026-09-29: keep conjecturing, no paper detours; `lake --old env lean` final audit; no full/umbrella builds, no heartbeat hacks, no git, no subagents.

## Verified new source
`formal/GaloisForLFunctions/HTGeometry/PauliAllTimeCircuitExclusionLaw.lean`, wired in HTGeometry umbrella after PauliReturnExcisedCircuitContinuumLaw. Ten theorems + two event definitions. No added hypotheses, axioms, or proof debt in new source.
- Any finite unitary family, union over ALL real times of target-specific energy-normalized tubes has SAME static Gaussian incidence partition upper bound as one fixed time.
- Exact occupied endpoint-image equality retained, so duplicate circuit words not charged.
- Existing return-excised polynomial window event strengthened: remove energy-box tail and 649*n^(k+7) grid factor entirely; also removes n>=1 condition. Explicit bound cardinality of return-excised occupied image times exp(-a*(6n-4)*delta).
- Complete nonidentity Pauli dictionary avoided at these energy-normalized radii for all real times with probability->1 as n grows, same compensated binomial expression as fixed time.
- Incidence <= number m of boundedLocalPauliLabel n 2 directions.
- Certificate floor card(C)*exp(-a*m) <= sum_c exp(-a*incidence(Uc)), a=gaussianIntervalActivationMass^2/2. Apply to occupied endpoint subtype for distinct-image cardinality. THIS IS NOT A RETURN-PROBABILITY LOWER BOUND. Only shows this static certificate cannot beat arbitrary target image entropy, even without time-grid loss. Not a Brown counterexample or externally established new physics.

## Verification
Scratch AllTime.lean first-pass exit0; Ceiling.lean first-pass exit0. Four headline axiom audits cover helpers: propext/Classical.choice/Quot.sound only. Final combined integrated source `lake --old env lean GaloisForLFunctions/HTGeometry/PauliAllTimeCircuitExclusionLaw.lean` session69475 exit0 no warnings. No oleans/builds/limits changed. Owned Lean/search jobs terminal; /tmp/hgt-alltime-incidence.qLyDiA scratch files deleted and empty directory removed. Source preserved. Lint exit1, 15 unrelated unwired RHTower modules; no new-leaf wiring/debt error.

## Exact remaining frontier
Still need growing-replica quenched N_inc*A_exc suppression on initial-easy-interval complement strong enough for all circuits and continuous horizon; retain occupied endpoint image and fibre multiplicity. Do not pretend static weighted probability estimate closes it.
`StaticEvolutionProjectiveWardTrichotomyLaw.lean` ALREADY has operator-norm all-time reduction to static double-commutator Ward tube; no need rediscover. No probability bound for that decisive tube established here.
`PauliWeightedCommutatorCarrierLaw.lean` controls design-weighted mass >= kappa. Single adaptively selected captured target DOES NOT yield dimension-independent lower kappa. Missing source-conditioned occupation/coarea estimate still actual core.
Potential normalization lead: hsNorm([H,U]) <=2 hsNorm(H) opNorm(U-exp(-itH)); with frobSq_realActivePauliHamiltonian =2^n*norm(x)^2 this gives self-normalized Gaussian cone event. NOT formalized here. Would improve fixed-error high-incidence sector only, not growing circuit union. Corpus GaussianCovarianceStableRankLowerTail covers positive quadratic lower tail, not automatically self-normalized/indefinite quadratic. Search found greedyBump_integral_norm_sq_stdGaussian mean only; no verified chi-square upper tail located.

## Work log / search
`docs/reports/quantum-recurrence-working-log.md` authoritative working log created, includes conjecture/proof/boundary loop and remaining gap.
Hybrid/deep/method searches used, source arguments checked. Semantic coverage statistics unavailable, older-generation warnings. Long deep Hamiltonian query falsely matched Hamiltonian graph paths; discarded. Broad arXiv commutator hits 2609.05386 (2x2 determinantal algebra) /2609.14585 (single commutators C*-algebras), no valid probabilistic transfer. No external novelty claim.
Named hgt-fields-medalist SKILL.md absent; available l7 workflow used before edits. No update_goal complete/blocked calls.
