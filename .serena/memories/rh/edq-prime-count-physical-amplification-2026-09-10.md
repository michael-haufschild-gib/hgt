Goal ACTIVE, RH unproved. Chain Euler deletion -> cofinal subpower full signed physical source ceiling -> exclude off-line zeros -> RH. Frontier map READ ONLY (other agents edit it). New result directly refutes the candidate of uniform prime-count damping contraction on actual EDQ source, with a quantitative positive survivor.

New verified leaf formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeCountAmplification.lean (288 lines), namespace RHTower.PrimeCountDamping. Imports Sieve.FullPrimeCofactorBoundary, EulerDeletionWeightedPrimeCancellation, SqrtTelescopeSums, FiniteFamilyObstruction.
Definitions:
source N u = sum_(1<=n<=N) (mu(n)*u^omega(n):C) smul bdGen(1/n)
primePacket N = sum_(p<=N,p prime) bdGen(1/p)
aperture N = norm(primePacket N)/(8 sqrt N)
amplificationConstant = 256*(8*32768^2)^2.
source N 1 = -bdMobiusModularApproximantVec N.

15 public theorems verified:
source_one; generator_norm_le; sum_generator_norm_le; primePacket_norm_le;
source_add_prime_norm_le; aperture_mem; aperture_norm_lower; aperture_energy_lower;
packet_energy_le; amplificationConstant_pos; aperture_energy_eventually_lower;
aperture_source_norm_eventually_pos; source_relative_energy_log_pow_tendsto_zero;
eventually_amplifies; not_exists_uniform_damping_budget.

Proof mechanism:
nonzero nonprime mu with n!=1 implies squarefree and >=2 distinct prime factors; b1=0.
sum norm(b_n)<=4 sqrt N from diagonal <=2/n and reciprocal-root telescope.
Full tail retained: norm(H_N(u)+u P_N)<=4u^2 sqrt N for u in[0,1].
aperture in[0,1/2], P_N^2<=16 sqrt N norm(H_N(aperture)), hence P_N^4<=256N energy.
Every integer-generator Gram entry nonnegative, so P_N energy >= upper-half packet energy.
Existing upper-half lower bound N/(8*32768^2 log^2N) gives eventual energy >=N/(amplificationConstant log^4N).
Existing unconditional raw energy*log^qN/N ->0 implies raw energy*log^qN/damped energy ->0 for every q.
For every real K, eventually K*raw energy < damped energy at selected aperture. Thus NO fixed uniform damping budget over all u,N. This is actual arithmetic source, not generic matrix toy. It does NOT exclude endpoint forcing-aware estimates or any particular schedule near u=1. No new raw subpower upper bound.

Paper-only auxiliary identity: sum_(d|n) mu(d)u^omega(d)=(1-u)^omega(n) for n>=1; integrate u in[0,1] to get divisor convolution of fullPrimeCofactor =1/(1+omega(n)). Prime-count term cancels this positive bulk, but truncated-divisor/tail estimate remains open. Do not claim this auxiliary identity formalized in new leaf.

Current attack card docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md section 'Prime-count damping: actual physical amplification' line1793 documents proof, methods and recent papers. Frontier and STATUS not edited by us.
Four deep requests (180s, maxrounds2,no-refresh) inspected both candidate and method lanes, 100 occurrences all current stripped declaration hashes; compiler source_only. First deadline in retrieval/ranking; last incomplete filter/judgment; other source/semantic gaps. Generated groups irrelevant/insufficient. Source-text follow-up provided actual prime floor, raw saving, squarefree prime-power classification, sqrt telescope.
Recent broad arXiv commutation/coagulation search intake (all September2026) recorded in card:
2609.09938 commutator theorem permits free factors, prescribed diagonal obstructed; not physical prime-count sign.
2609.09453 Mellin sampled-ratio product HS theorem requires finitely many jumps/weighted BV; kappa(v)={1/v} fails.
2609.02960 tagged coagulation uses approximate local scale covariance/stationarity; no EDQ law.
2609.09599 BKM quantum Markov curvature requires stationary metric and retains dissipative/transport activities; no coefficient-to-physical-adjoint identity.

Validation COMPLETE: scratch lake env lean passed; final lake build --old ...EulerDeletionPrimeCountAmplification compiled ONLY new leaf,181s, warning-free. Missing dependency InteriorSquare was separately built(104s); PolarCoordinates leaf target resolved second missing olean. No full/umbrella rebuild. All15 new public #print axioms via/tmp: only propext,Classical.choice,Quot.sound. Umbrella wired near16349. index refreshed, lint passed. No numerical computation or commit. All owned Lean/build sessions terminated normally; temporary cleanup performed at turn end. Shared foreign processes/changes untouched.

Next useful mathematical target is endpoint full-covariance control with retained higher-factor cancellation; do not retry generic prime-count contractivity or merely present this obstruction as RH progress sufficient for closure. A potential consequence to analyze is the negative integrated count-energy flux between aperture and endpoint, but it alone gives only relative cancellation, not absolute subpower control.