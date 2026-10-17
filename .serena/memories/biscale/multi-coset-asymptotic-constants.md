# Multi-coset asymptotic constants: active research frontier

Independent BiScaleUncertainty; no RH research, hgtl7, numerical experiments, added axioms, heartbeat increases, full/umbrella builds, commits/pushes. Full active objective is 100 significant packages toward sharp monotone source-energy constants combining physical signed collars, clique spheres, and Schur residual coupling. Count packages, not helpers or old dependencies. User attachment /Users/michael/.codex/attachments/14cea3d2-a6f6-463f-bcd2-5d8a6947ba60/pasted-text-1.txt reread this turn. Goal NOT complete.

Authoritative owned card: docs/drafts/pipeline/1-in-progress/multi-coset-asymptotic-constants-2026-10-17.md. Crisp facts: docs/reports/BiScaleUncertainty/MultiCosetAsymptotic-FACTS.md. Full proofs, statuses, hashes, and next candidates there. User relocated and rewrote field context: authoritative README is formal/GaloisForLFunctions/BiScaleUncertainty/README.md, explicitly READ-ONLY for this agent. Initially read all 242 lines; SHA-256 80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507 was unchanged through package10 verification. User then revised README to260 lines and supplied Trap10. Read the full new260-line version; current SHA256 dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933. External revision, never edited by this agent. Do not edit it. Old docs/reports path is obsolete. Updated guidance requires general signed correlations, not hidden blind-grid premises. Grid constants remain specialized theorems; add unconditional actual-source receivers retaining measured signed Gram data. Stay on multi-coset asymptotic/source-energy topic; do not adopt separate RH/prime-polar objectives. docs/architecture.md and docs/testing.md absent (rechecked). No subagents authorized/spawned. update_plan unavailable; card tracks plan. Serena ignores formal Lean paths; use narrow shell reads after symbol-tool failure. Do not modify other agents' work.

## Certified progress: 15/100 significant packages

1. PhysicalCollarSourceEnergy.lean: exact arbitrary-partition signed ENNReal transport; source-energy bound for actual compact continuous grid sources including infinite energy; allocation supremum bound without attainment; normalized actual compact C2 nonzero-source bound; positive monotone envelope/finite limit. All19 theorem axiom audits and final direct leaf pass, only standard3 axioms. SHA256 423ca0e7d1957c5898bac5ff228e6989d255c98e2fe24ec621775f76d3574792. Logs /tmp/bsu-physical-source-{final,axioms,index,lint}.log and scratch /tmp/bsu_physical_source_axioms.lean.

2. PhysicalCollarCutoffMonotonicity.lean + PhysicalCollarCutoffStability.lean ONE package. Exact physical extension, zero-padding, and retraction prove P_N itself monotone, equal to running max, and
0<=P_infty-P_N<=integral_(logN-delta,infty)w<=4*2^(1/4)/(sqrt(N)*(1-2/N^2)), N>=2, delta=log2/2.
J(f)/h(0)>=P_N. Trial certificate uses rho.gap plus cutoff bound, no attained optimizer. All35 theorem axiom audits and final direct leaf pass, only standard3. Hashes: monotonicity e9ebaca82b8d817c28826c64ac54fb77e81dc5823f71b3329fea4110e0eb6586; stability b3d464f73df171bc2e7f8a062697c15518a63df9a8c9b3bdc2ff3ed940264246. Evidence /tmp/bsu-cutoff-check.log, /tmp/bsu-cutoff-stability-check.log, /tmp/bsu-cutoff-{axioms,final,index,lint}.log, /tmp/bsu_cutoff_axioms.lean.

3. PairedCosetSphereDuality.lean + SignedCosetProductCoupling.lean + ProductCoupledCollarHierarchy.lean ONE package. Paired spheres u0^2+||u_p,false||^2+||u_q,true||^2<=R^2 have exact support R sqrt(W^2+A_false^2+A_true^2), A_sign=sum within-sign block l2 weight norms. Choose maximizing correlation block each sign then 3D Cauchy; explicit parallel-block attainment for W>0. Finite-vector sharpness only.
Actual source pinned through N has paired spheres through K if K^2<=N: same-sign odd cosets use divisibility zeros, opposite signs use h(log(jk))=0. Actual-source subtype + arithmetic cutoff only, no unproved analytic interface. Square-grid specialization uses source index n*(n+4)+2 (literal cutoff (n+2)^2).
PhysicalCollarPartition.signBlockNorm, pairedKernel, pairedCoefficient; paired kernel >=independent. Exact gain 2*A_false*A_true/(sqrt(W^2+(A_false+A_true)^2)+sqrt(W^2+A_false^2+A_true^2)). Measurable/integrable, bounded by physical mass. sourceFibre_eq_ofReal and exact transport give extended/normalized energy bounds. Q_K=pairedOptimalCoefficient=sup paired coefficients, positive finite, >=P_K. C_N=productCoupledCollarCoefficient=max(P_N,max_(K^2<=N)Q_K), empty max0, positive monotone bounded by collarTailMass and valid for actual smooth N-grid sources. Limit limitingProductCoupledCoefficient.
Allthree direct checks and all41 theorem axiom audits pass standard3; final direct hierarchy exit0/no diagnostics. Hashes geometry 377bf1eef09bb7190e186f533bc5e8c80cc0bd25e426648e219a103c0ff19d9f; source c26fc3d7f4f1d4e4ad123135d733a59fae96c940ddc9c5821a27c4b0eff029dc; hierarchy e78c3e45cc9bcd200840dbfcb40d1a41fa3ff49396b875f98a05850eca6b3156. Last two hashes rechecked current turn. Evidence /tmp/bsu-paired-geometry.log, /tmp/bsu-signed-coupling.log, /tmp/bsu-product-hierarchy.log, /tmp/bsu-product-coupling-{axioms,final,index,lint}.log, /tmp/bsu_product_coupling_axioms.lean.

4. NEW PairedCollarCapacity.lean + PairedCollarCutoffStability.lean ONE package. 30 public theorems, both direct compilations exit0/no diagnostics, all30 axiom/signature audits pass only propext/Classical.choice/Quot.sound, final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PairedCollarCutoffStability.lean exit0/no diagnostics.
- collarBlockSize_monotone_bounds uses existing canonical block direction/remainder. logarithmicSignNorm aggregates one sign. pairedRadial_monotone_bounds proves norm(W,A,B) coordinate monotonicity and unit l1 capacity. logarithmicPairedArrayKernel coordinate addition raises kernel by 0..added mass, for ANY real W. Unordered error bound requires a,b,e nonnegative and b<=a+e. Padding preserves both signs; derive single-sign padding from existing signed padding with identical arrays on both signs.
- Reuse actual PhysicalCollarPartition.extend/retract and retentionFibre: Q_K is monotone and Q_M-Q_K<=collarCutoffTailMass(K-2). No desired comparison supplied as input.
- limitingProductCoupledCoefficient_eq_iSup_paired identifies C_infty=sup_K Q_K>=P_infty. Q_K tends to that limit, and 0<=C_infty-Q_K<=4*2^(1/4)/(sqrt(K)*(1-2/K^2)).
- productAdmittedCutoff n=Nat.sqrt(n+2)-2. For N=n+2>=4, C_N=max(P_N,Q_floor(sqrt N)) exactly. productCoupled_quantitative_saturation_floor proves
0<=C_infty-C_N<=4*2^(1/4)/(sqrt(s)*(1-2/s^2)), s=floor(sqrt N).
- productCoupled_quantitative_saturation gives simpler 0<=C_infty-C_N<=16*2^(1/4)/N^(1/4), N>=4. productCoupled_limit_sub_error_le_normalized_energy gives actual J(f)/h(0)>=C_infty-that error. Only n>=2 and actual SmoothLogarithmicGridSource n in capstone. This is an upper error bound, NOT a sharp exponent or sharp source constant.
Hashes capacity 215adfa612eb4e9eef6d1025d51de02109b3d2b0a157828441b4068c83030863; stability e2f4d2b569d6df1efd3e4e65444f9e025408ee34d1c9fe83973e273334eec19c. Evidence /tmp/bsu-paired-capacity.log, /tmp/bsu-paired-stability.log, /tmp/bsu-paired-cutoff-{axioms,final,index,lint}.log, /tmp/bsu_paired_cutoff_axioms.lean.

5. Exact full-grid capped support (three leaves, ONE package). CappedBlockSupport.lean defines F(L,H,t) as the maximum over s in [0,1] of L*t*s+H*sqrt(1-(t*s)^2), proves continuity, disk attainment, support bound, cap monotonicity, F<=sqrt(L^2+H^2), and exact division-free formula: F=sqrt(L^2+H^2) if L<=t*sqrt(L^2+H^2), else L*t+H*sqrt(1-t^2). Handles all zero weights.
CappedCosetSphereDuality.lean defines pairedCap(t,false)=t, pairedCap(t,true)=sqrt(1-t^2), cappedCosetSupport=max_[0,1] sum of all signed capped block supports. Proves compact attainment/continuity, <=sum whole-block norms, exact upper bound from whole-block spheres plus all low opposite-sign paired spheres, common-origin support R*sqrt(W^2+Z^2), amplitude and finite-block-vector attainment. Parallel canonical low/high directions handle zero subvectors; no autocorrelation realization claim.
FullGridCappedCollarEnergy.lean splits logarithmicCosetNodes n p into low k and high set difference, constructs physical low/high norm arrays, cappedAngularSupport/cappedKernel/cappedCoefficient, proves measurable/integrable kernel and old coefficient <= capped coefficient. Literal source zeros derive whole and paired low spheres for (k+2)^2<=n+2. Exact signed physical transport gives ENNReal energy over the FULL interval (0,log(n+2)), including infinite energy/zero source. Actual smooth-source capstone PhysicalCollarPartition.fullGrid_capped_energy (line251), n>=2, chooses productAdmittedCutoff n; no unproved analytic interface.
Allthree direct compiled leaves, all41 public theorem axiom/signature audits, and final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarEnergy.lean passed exit0/no diagnostics. Only standard3 axioms. Hashes block 3004dced418ed93f074aa177cd75cf7bd841200f6af3328538e5cd2863355406; cosets b6e3bd890950ae1874e4c4ef87a30d383d1d4360768ffdad607e2b8505d811c5; source 6a8bcfaba9f2647cdeadc59abc68a5cf7724c4a3c58e049120c7922553503b0d. Evidence /tmp/bsu-capped-block.log, /tmp/bsu-capped-cosets.log, /tmp/bsu-fullgrid-capped.log, /tmp/bsu-fullgrid-capped-{axioms,final,index,lint}.log; scratch /tmp/bsu_fullgrid_capped_axioms.lean. All8 older hashes rechecked unchanged.

6. CappedSupportComparison.lean + CappedCollarArrayComparison.lean + CappedCollarCutoffComparison.lean + FullGridCappedCollarHierarchy.lean ONE package. All four compiled cleanly; all 58 public theorem axiom/signature audits pass only propext/Classical.choice/Quot.sound. Final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarHierarchy.lean exit0/no diagnostics.
Mathematics: scalar F weight addition changes support by 0..deltaL+deltaH using attained disk coordinates in [0,1]. At fixed L²+H², increasing nonnegative L decreases F: inactive cap uses norm bound; binding cap uses tangent inequality L deltaL+H deltaH<=0 and binding slope L sqrt(1-t²)>=Ht. Finite sums/max/radial capacity yield kernel increase between 0 and added coordinate mass. Increasing the low cutoff strengthens kernel; all-low support exactly paired. Zero-padding preserves low/high block norms, extra coset labels have zero weight. Actual physical extension then gives B_(N,K)<=B_(M,L) for N<=M,K<=N,K<=L<=M.
Here B_(N,K)=sup partitions cappedCoefficient. P_N<=B_(N,K), Q_K<=B_(N,K)<=Q_N, with all-low B_(N,N)=Q_N. Set B_N=B_(N,floor sqrt N) for N>=4, P_N for N=2,3. Then old C_N<=B_N<=Q_N<=Q_infty, B_N positive and actually monotone, tends to Q_infty, and 0<=Q_infty-B_N<=16 exp(delta/2)/N^(1/4), plus sharper floor formula. Actual compact continuous source ENNReal bound uses full interval (0,log N), includes zero/infinite-energy cases. Smooth actual-source capstone fullGridCapped_quantitative_source_certificate at line229 combines quantitative error and B_N<=J_arch/h0, with only n>=2 and actual source domain. No analytic interface premise. Added full-grid retention weakly improves finite certificate but has same limiting value; strict finite gain, sharp error exponent, actual autocorrelation realization, and general nonzero Schur remain open.
Hashes: support comparison 4f6f50c1f75d890d7f06a891dcca531c103eb15c01bbe2cf5cc13b276c1ccca3; array comparison 9656cd0ce211de779e6dbfefd70a35950e7d761b65c93e6418b1be80a200fd43; cutoff comparison d597b18ce4c9910cccfb22975c72ad6646ff8113781471dbb0795fcd460ec4ec; hierarchy 72320630cda08587f8830f795984fb6c44ab1c98904049f64ec7817f789a8ffa.
Evidence /tmp/bsu-capped-{support-comparison,array-comparison,cutoff-comparison,hierarchy}.log, /tmp/bsu-capped-hierarchy-{axioms,final,index,lint-final}.log, /tmp/bsu_capped_hierarchy_axioms.lean. Static coverage check confirms all58 public theorem names exactly once. All11 earlier source hashes unchanged. Search /tmp/bsu-capped-capacity-search.log: 156 matches45 modules,68 after cap; useful existing support/capacity hits, partial older index/source coverage, semantic unmeasured; no exhaustive novelty claim.

7. CappedSupportActivation.lean + PhysicalCappedActivation.lean ONE package. Exact activation and quantitative physical gain. Both direct compilations, all26 public theorem axiom/signature audits, and final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PhysicalCappedActivation.lean pass exit0/no diagnostics, only propext/Classical.choice/Quot.sound. Full goal remains active.
Scalar: for U=sqrt(L²+H²), an attained disk point satisfies 2U(U-F)=(Ux-L)²+(Uz-H)². Binding tU<=L gives (L-tU)²<=2U(U-F). F=U iff L<=tU for nonnegative weights. Define cappedLowFraction L H=L/U (zero blocks give0 by total division), and cappedSignLowFraction as finite maximum on each sign. Nonempty M (actual grids always nonempty): angular Z equals independent S=sum whole norms iff alpha_false²+alpha_true²<=1, strictly smaller iff >1. Allzero/empty caps lemma and zero subblocks handled; no attained optimizer premise.
Physical maxLowFraction/cappedActivationIndex are constructed from actual low/high weight norms. cappedKernel=kernel iff index<=1; kernel<cappedKernel iff index>1, for every real y. For y>0, cappedCouplingGain=(S²-Z²)/(sqrt(W²+S²)+sqrt(W²+Z²)) exactly equals cappedKernel-kernel, nonnegative and integrable over (0,delta). Old coefficient+integral gain=cappedCoefficient. Equality of coefficients iff inactivity index<=1 holds almost everywhere; strict improvement iff that almost-everywhere condition fails. Mere positivity on both signs does NOT certify gain; high weights can absorb coupling. Isolated activated offsets do not ensure integrated strictness.
Actual-source extended bound retains full (0,log N), zero and infinite-energy sources. fullGrid_activation_source_certificate line188 uses only n>=2, actual PhysicalCollarPartition and SmoothLogarithmicGridSource, chooses floor(sqrt N), and proves oldCoefficient+integral gain<=J/h0 together with exact inactivity iff. No hidden energy/analytic interface. Does not establish strict inequalities between optimized suprema or actual-source realization.
Hashes finite activation 1625673ef2d59453edef68fa71f6422b5904c90106d5d0b77e91ce1fb492bce3; physical activation 6495929af4fe9b23b2853cca2c355002b73e5755d3473695f040f9beef3e4d4b. Evidence /tmp/bsu-capped-support-activation.log, /tmp/bsu-physical-capped-activation.log, /tmp/bsu-capped-activation-{axioms,final,index,lint}.log, /tmp/bsu_capped_activation_axioms.lean. Audit coverage all26 exactly once; printed capstones/gain/source definitions inspected. All15 previous hashes unchanged. Corpus search /tmp/bsu-capped-activation-search.log:213 matches56 modules,82 after cap; partial text/source retrieval, older source coverage, semantic unmeasured; no exhaustive novelty claim.

8. Exact two-column Schur geometry/support, optimized dyadic physical refinement, monotone hierarchy, and general full signed-Gram receiver (SIX leaves, ONE package).
Modules: TwoColumnSchurGeometry, TwoColumnSchurSupport, DyadicSchurSupport, DyadicSchurCollarEnergy, SchurCappedCollarHierarchy, SignedPhysicalGramEnergy.

For finite u,v, U=sum u²,V=sum v²,D=sum uv. If U,V<=R² and (Rc-D)²<=(R²-U)(R²-V), every direction satisfies sum(ru+sv)²<=R²(r²+s²)+2Rc rs. At c=0 the full feasible domain is rotation invariant. For weight columns a,b, A=sum a²,B=sum b²,C=sum ab, exact zero-lag support is R*nu, nu=sqrt(A+B+2sqrt(AB-C²)); finite-vector maximizers include degenerate blocks. nu<=sqrt A+sqrt B, equality iff C=0. Polynomial IVT q(t)=(1-t²)C+t(B-A), t in [-1,1], gives orthogonalizing rotation (1,t)/sqrt(1+t²). No autocorrelation realization or general nonzero-lag exact support claimed.

Actual N>=4 sources supply frame {0,d,2d}, d=log2, and target columns (h(y),h(d-y),h(2d-y)), (h(d+y),h(y),h(d-y)). Optimize nu((lambda W,mu a,b),(c,(1-lambda)W,(1-mu)a)) over [0,1]²; compact minimum continuous/attained, between W and W+a+b+c for nonnegative weights. Actual physical weights are origin, node2 left, node4 left, node2 right. Max the resulting kernel with existing capped kernel. T_N is partition supremum (P_N at N=2,3); H_N=max_(K<=N)T_K. B_N<=H_N<=J/h0, 0<H_N monotone, H_N->H∞, Q∞<=H∞<=tailMass. Raw T_N monotonicity NOT proved; strict optimized improvement, rate to H∞, and sharp source infimum NOT proved. Symbolic finite-cone example W=a=b=1,c=0, lambda=mu=1/2 gives support²=2+sqrt3/2<3; not a physical-optimum strictness theorem.

README steering led to general signed extension using existing translationPacket_correlation_le, not a new claim for that dependency. For arbitrary f:C_c(R,R), origin R=h(0), nonnegative weights a, mass A=sum a, and anchor W, keep full Gram G=R W²+2W sum a h(t)+sum_ij ai aj h(tj-ti). Deficit K=R(W+A)-sqrt(RG) bounds actual weighted increments. Pointwise envelope gives K>=0. Packet Cauchy at y=0 gives K<=sum a(R-h(t))<=2RA: exact origin singularity cancellation, no derivatives/cutoff/clipping. Use every signed physical node ±log(k+2), retaining all signed cross-coset entries. signedGramCoefficient_source_energy takes only rho and f:C_c, with no zero-grid or caller-supplied Gram/energy premise, includes zero/infinite-energy sources. C² gives real/normalized bound, including total division at R=0. measuredGram_and_schur_source_certificate takes max(H_N, signedGramCoefficient/R) on the grid-blind domain. General signed coefficient depends on actual source data, NOT a positive uniform constant over unrestricted sources.

All SIX leaves compile cleanly. All85 public theorem audits pass exactly once: 69 in /tmp/bsu_schur_pair_axioms.lean and16 in /tmp/bsu_signed_physical_gram_axioms.lean; only propext, Classical.choice, Quot.sound. Printed general source signatures and actual Gram/kernel definitions inspected. Final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedPhysicalGramEnergy.lean exited0, empty diagnostics log /tmp/bsu-schur-pair-final.log. No full/umbrella build. Evidence /tmp/bsu-schur-pair-axioms.log, /tmp/bsu-signed-physical-gram-axioms.log, /tmp/bsu-schur-pair-final-{manifest,integrity}.json. Source hashes:
TwoColumnSchurGeometry 91e66c439bb52ef3cc5f0fb32fc15e47c2614949a8d10d23620e90ae46c29ab9
TwoColumnSchurSupport 249f9bea751b9ba8c5a5ce8c88fd1c6b3c3cab292266c8cbf95bba37be9e7980
DyadicSchurSupport 37f23f952324a5bc85b3a628e4b2994ccbc99a94a80c6e1cbd2fdf884327ef30
DyadicSchurCollarEnergy c120590bca4fb721c66ea317804b9631cc90d7e582d7ddbb2664da08212fd5a9
SchurCappedCollarHierarchy 8ef01a80da29ed464c42d9df631539908297b10158cb6c5606967ecf855ee573
SignedPhysicalGramEnergy 9dc409594e17bd54b97b38b351addc11dd869ebea53f14d4c1087c3151383c33
Corpus searches /tmp/bsu-schur-pair-search.log (669 declarations67 modules117 after cap) and /tmp/bsu-signed-schur-search.log (930 declarations90 modules162 after cap) partial, older snapshots/semantic unmeasured; no exhaustive novelty claim.

All23 owned leaves wired exactly once; all17 prior source hashes rechecked unchanged. Index refreshed and new signed/general capstones discoverable; scoped whitespace clean. At the package8 audit, scripts/formal_tools.py lint exited1 for FIVE unrelated concurrent unreachable modules: AnnularCorrelationSource, HyperbolicGaugeChebyshevEnergyRepresentation, MultiNodeSignedCliqueWeilCoercivity, SignedPrimePolarCoherentSchur, WeilFullFunctionalAndPrimitiveHyperplaneBridge (/tmp/bsu-schur-pair-lint-final.log). Do not modify foreign work to clear it. Earlier six of seven failures were concurrently fixed; this historical five-module list is superseded by package9 below. All owned Lean/search/index/lint sessions terminal; no live job. Temporary /tmp/bsu_schur_pair_api.lean and /tmp/bsu_signed_schur_api.lean removed with apply_patch; successful audits/logs retained. README unchanged. No policy/approval blockers.

## Package 9: full signed-Gram cutoff hierarchy, verified

Three leaves: SignedGramCapacity.lean (8 public theorems), SignedGramCutoffComparison.lean (7), SignedGramCutoffHierarchy.lean (19). One significant package, not34. Full measured Gram packet yields 0<=K(a+b)-K(a)<=2R sum b for b>=0, with arbitrary incumbent weights and arbitrary real anchor W. kernel_mono, nonnegative-cover error bound, exact finite subset/padding follow. No zero-grid or correlation sign assumptions.

Actual PhysicalCollarPartition.extend increases K; retract loses <=2R*retentionFibre. Integrate exact physical transport to get coefficient loss <=2R*collarCutoffTailMass. signedGramOptimalCoefficient f n=sSup of physical signedGramCoefficient f; limitingSignedGramCoefficient f=iSup n. Fixed actual source f:C_c, R=h_f0:
0<=S_N↑S∞<=2R collarTailMass;
0<=S∞-S_N<=2R tail_N;
0<=S∞/R-S_N/R<=8 exp(delta/2)/(sqrt(N)*(1-2/N²)), N=n+2>=2.
Zero source included via total division. limitingSignedGramCoefficient_source_energy takes ONLY f:C_c and bounds ofReal S∞ by full ENNReal increment integral, including infinite energy. Compact C² gives S_N/R<=S∞/R<=J/R. Source-dependent certificate, not uniform positive constant, not sharp-rate/matching-asymptotic claim.

All3 leaves compile cleanly. All34 public axioms audited exactly once with only propext/Classical.choice/Quot.sound; printed source signatures and packet/sup definitions inspected. /tmp/bsu_signed_gram_cutoff_axioms.lean and /tmp/bsu-signed-gram-{capacity,comparison,hierarchy,axioms}.log. Final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramCutoffHierarchy.lean exit0 empty log /tmp/bsu-signed-gram-final.log, durable /tmp/bsu-signed-gram-final.exit. Original interrupted session69447 was missing after user pause/resume; process inventory showed no live Lean, then fresh final session69502 exited0.

Hashes:
SignedGramCapacity 95469f4664f01de5dd302d81a58445005f8d4d020dbe993fb2bc8e85101da435
SignedGramCutoffComparison 6be920f79c818fa42fdde188b73593c1bed983a76d0e52c9f5d8c23321ec4a2e
SignedGramCutoffHierarchy 7a0da76505f74745f800ee50fe6323540464d74274095fc051209cb46782327d
Manifests /tmp/bsu-signed-gram-{manifest,integrity,audit-coverage}.json, prior23 hashes /tmp/bsu-signed-gram-prior-hashes.json. All26 own imports once; prior23 unchanged; read-only README hash unchanged. Index refreshed,17 new hierarchy declarations discoverable; no stale own outputs. Temporary API probe /tmp/bsu_signed_capacity_api.lean deleted viaapply_patch; audits retained.

At the package9 audit, global lint exited1 for FOUR foreign concurrent unwired leaves: ChebyshevGaugeNyquistCellQuadrature, DistantCopyCorrelationTopology, DistantCopyEnergyTopology, SignedCoherentMomentReceiver. /tmp/bsu-signed-gram-lint-final.log supersedes earlier four/five lists. Do not modify foreign work. No full builds, numerical experiments, heartbeat raises, commits or pushes. All owned Lean/search/index/lint jobs terminal. Package9 brought progress to9/100; current total15/100 and goal remains active.

Proof repairs: normalize sqrtR*(sqrtR*A) with rw [←mul_assoc,←pow_two,Real.sq_sqrt...] before nlinarith; it will not automatically multiply square identity by A. Before integral_sub, explicit change to pointwise subtraction to remove function subtraction wrapper. Signed finite product sums use sub_eq_add_neg and add_comm, not reverse subtraction rewrite.

## Package10: full measured-Gram trial certificate, verified

SignedGramDualSupport.lean (11theorems), SignedGramPhysicalPrices.lean (17), SignedGramTrialCertificate.lean (21). Full actual signed Gram retained. P_a=W T0f+sum a_i T_tif; H_a=sqrt(R)||P_a||; q_i=Re inner(P_a,T_tif)/H_a with total division; p_i=(1+q_i)/2 in[0,1]. At zero packet q=0, no positivity hypothesis. Norm support yields r=H_b-H_a-R sum(b-a)q>=0. Exact kernel difference Kb-Ka=2R sum(b-a)-2R sum(b-a)p-r.
Measurable prices pulled back through signed physical collar offsets; masked inactive price1 and finite active minimum. Slack(ρ,η)=integral(η physical cost-w*minPrice)>=0; Gapρ=2R Slack(ρ,ρ). Exact identity Cρ+Gapρ-Cη=2R Slack(ρ,η)+integral r. Remainder integrability uses combined kernel/mass/cost, never integrates singular anchor alone.
0<=S_N-Cρ<=Gapρ; Gap0 certifies finite optimality. Gap0 iff R0 OR a.e. positive incumbent shares have minimum active price. This is factorization with R0 explicit, NOT a claim R0 is a genuine exception to complementarity; NOT necessity of canonical gap for all optimizers.
0<=S∞-Cρ<=Gapρ+2R tail_N; normalized error <=Gapρ/R+8exp(delta/2)/(sqrt(N)*(1-2/N²)). Extended-energy source capstone takes onlyρ,f:C_c. Smooth normalized capstone additionally ContDiffℝ2 f, proves Cρ/R<=S∞/R<=J/R and same error. No grid zeros, optimizer, supplied transport/Gram/energy premise.

All3 final dependency checks exit0 empty logs. Final DIRECT lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramTrialCertificate.lean exit0 emptylog, /tmp/bsu-signed-dual-final.exit. All49 public theorems audited exactly once, only propext/Classical.choice/Quot.sound; six printed capstones and six concrete definitions inspected. /tmp/bsu_signed_gram_dual_axioms.lean, /tmp/bsu-signed-dual-{support,prices,trial,axioms,final}.log.
Hashes:
support a082cd5a304a9c32d550f5bc55afdad2bd202fb8d65751ac1c871c90321a2396
prices f241f55eda32e59665150b4bae5a0e9feba0d4dc701e3ecac2d336fcdd0c75e3
trial fd195d5c55de946103bb41e241f335655d30f0aabaf535c33f58b90ac883ca8b
/tmp/bsu-signed-dual-{manifest,integrity,audit-coverage}.json. All29 ownimports once,26priorhashes unchanged. Index refresh/discovery pass. API probe deleted; audit/logs retained. At the package10 audit, global lint reported12 foreign unwired leaves: CausalExponentialResponseAndLaplaceEnergy, DistantCopyCompactness, DistantCopyCorrelationTopology, DistantCopyEnergyTopology, DistantCopyPolarTopology, DistantCopySharpness, FiniteGridRunLength, FoldFreeKernelGramAndFranelGcdCancellation, RealizedCoherentCancellation, SignedPrimePolarOptimalCollar, SignedPrimePolarScaledCollar, SuccessorSequenceHilbert. /tmp/bsu-signed-dual-lint-final.log. Do not modify foreignwork. No fullbuilds/numerics/heartbeat hacks/commits/pushes. Package10 counts once; cumulative total at that audit10/100. Current total15/100, goalACTIVE.

Lean repairs: broadsimp may turn complex-real scalar into real action before inner_smul_left/right matches. Expand packets with simp only then simp_rw inner_smul then simp. re_inner_comm unavailable; explicit packet expression and inner identities avoid it. Common denominators: ←mul_div_assoc and ←Finset.sum_div. Measurable.div_const at root namespace. Name packetScale nonneg before abs simplification. Explicit types for nonnegative scalar products prevent unresolved numeral metavariables before nlinarith. Integral add/sub use explicit integrands to avoid function subtraction wrapper.

## Package11: explicit smooth dyadic producer and sharp anchored minimum, verified

Four leaves in formal/GaloisForLFunctions/BiScaleUncertainty/: DyadicDifferenceSource (14 public theorems), DyadicAnchoredProducer (19), DyadicTriangularOptimality (6), DyadicGramConditioning (16). Namespace DyadicDifference. ONE significant package, cumulative11/100 at that audit; current total15/100, goal remainsACTIVE.

Set d=log2. Literal ContDiffBump at0 with inner radiusd/8, outerd/4 defines smooth compact g; g(0)=1 and Rg>0. Fixed actual source f(u)=g(u)-g(u+d) is C∞ compact, Rf=2Rg>0. e_j=T_(jd)g are orthogonal with norm²Rg. Full lattice correlation: hf(zd)=Rg(2·1_(z=0)-1_(z=1)-1_(z=-1)), z integer.

For arbitrary real sequences a,b, P_m=edge0+sum_(k<m)[a_k edge(-(k+1))+b_k edge(k+1)], edgej=T_(jd)f. Explicit producer Q_m=(m+1)^-1 sum_(k=0)^m chain_k, with chain_k all-one anchored packet, telescopes to (m+1)^-1 sum_(k=0)^m(e_(-k)-e_(k+1)).
Exact minimum/defect: ||P_m||²=Rf/(m+1)+||P_m-Q_m||². Thus every finite anchored packet is strictly positive. Triangle_m(k)=(m-k)/(m+1), k<m, lies in(0,1]; it attainsQ_m. Prefix atom tests prove equality iff every active a_k=b_k=Triangle_m(k).

Actual full AnchoredGram on signed integer nodes ±log(2^(k+1)), k<m, with origin coefficient1 equals ||P_m||². Its normalized minimum is1/(m+1)=log2/(log(2^m)+log2), antitone and tending0. No positive cutoff-uniform anchored bound even for nonnegative weights and this one fixed smooth source. Strong positive survivor: sharp actual-source minimum, constructive attainment, exact remainder, unique coefficients. Do not infer uniform coercivity from fixed-source smoothness and positive weights alone.
Scope: anchored minimum, NOT least eigenvalue/condition number. No polar admission, physical collar partition realization, sharp S_N tail rate, or J_arch lower bound inferred. Original tent formulation and anchor-W scaling remain paper consequences; formal capstone uses literal smooth source and anchor1.

All four dependency checks and final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/DyadicGramConditioning.lean exit0 with empty logs. All55 public theorem axiom audits exactly once, only propext/Classical.choice/Quot.sound. Printed concrete source, packet, producer, weights and full-Gram signatures inspected. /tmp/bsu_dyadic_gram_axioms.lean and /tmp/bsu-dyadic-{source,producer,triangle,gram,axioms,final}.log; durable final.exit; manifest/integrity/audit-coverage JSON. All33 ownimports once,29priorhashes unchanged. README unchanged atdda7a67... above. Index/discovery pass. API probe removed, all owned jobs terminal. No fullbuilds/numerics/heartbeat hacks/commits/pushes.
Hashes: source46205aa0c5a389ec04fedafa6f8d2e4e6c5ee5b1e9d7e73169b0fa1056b7704a; producer24c9734e4a331075063fe8116e929ef05156554baf3a710dd98adda855f11fe0; uniquenesse10da9d59fc6c1a32f3f5993e13a869cab781ae3d7854685c5343723b942f00d; cutoff11fd46aeb8bc791b3883de96a0a3cf4754f47d2bde872df0da8e80af9a614960.
At the package11 audit, global lint exit1:11 foreign unwired modules, listed in facts and /tmp/bsu-dyadic-lint-final.log. No own failure; no foreign source modified.
Prior discovery /tmp/bsu-dyadic-producer-search.log:387decl98modules, partial/source-only/older snapshot, semanticunmeasured. FiniteTranslationTrains and RealizedCoherentCancellation audited; no exhaustive novelty claim.

## Package12: actual minimum-price response and monotone cutoff producer, verified

Three leaves in formal/GaloisForLFunctions/BiScaleUncertainty/: SignedGramMinimumResponse (12 public theorems), SignedGramResponseOptimality (14), SignedGramResponseLadder (17). ONE significant package, total12/100 at that audit; current total15/100 and full goal ACTIVE. Namespace PhysicalCollarPartition.

For actual f:C_c and incumbent rho at cutoff n, E_k consists of active physical points with k<=n and gramPhysicalPrice_k=gramPriceFloor. F_k=E_k minus union_(j<k)E_j are measurable disjoint cells covering the physical interval. gramMinimumResponse has shares exactly1_(F_k), with unique selected index at every physical point. Exclude inactive collars BEFORE tie-breaking: masked inactive price1 can tie an active minimum1. All measurability, support and exact mass conservation are discharged; zero source included.

The response eta attains pointwise and integrated incumbent linear cost. gramSlack rho eta is exactly excess over that attained minimum. All minimizers are precisely allocations to active minimum-price collars almost everywhere, including fractional sharing among ties. gramGap_isGreatest_linearizedGain realizes the canonical gap G as the attained greatest feasible linearized gain. Actual gain C(eta)-C(rho)=G-D, D=integral gramRemainder>=0, retaining the full measured signed Gram data.

gramResponseStep accepts eta iff its actual coefficient is at least incumbent. Exact gain=max(0,G-D); exact old dual deficit=C(rho)+G-C(step)=min(G,D). Hence 0<=S_n-C(step)<=min(G,D), and 0<=S_infty-C(step)<=min(G,D)+2R*collarCutoffTailMass n. No supplied curvature/error bound or coercivity hypothesis.

gramResponseLadder f 0=equalMultiplicity0; successor extends the previous physical partition and applies gramResponseStep. A_n(f)=gramResponseCoefficient f n is monotone, 0<=A_n<=S_n, and tends to produced finite L(f)<=S_infty(f). Normalized A_n/R is monotone; compact C2 sources have A_n/R<=L/R<=J_arch/R. Every actual compact continuous source has the extended-energy bound. Error S_infty/R-A_n/R<=gap(ladder_n)/R+8*2^(1/4)/(sqrt(N)*(1-2/N^2)), N=n+2. Successor has the sharper min(G,D) certificate from the explicit extension. NO assertion L=S_infty, vanishing gaps, strict ascent, or error to unrestricted source infimum. Do not confuse A_n with specialized blind-grid C_N or identify S_infty/R with H_infty.

All three dependency checks pass without diagnostics; final direct lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramResponseLadder.lean exit0, empty log, current source checked. All43 public theorem axiom audits exactly once, only propext/Classical.choice/Quot.sound. Concrete selection, response, cost, accepted step and ladder definitions and capstone signatures inspected. /tmp/bsu_minimum_response_axioms.lean; /tmp/bsu-minimum-response-{selection,optimality,ladder,axioms,final,index}.log; final.exit; manifest/integrity/audit-coverage JSON. All36 own imports once,33 prior hashes unchanged, read-only README unchanged. Index and all3 requested capstone discoveries pass. API probe removed; all owned jobs terminal.
Hashes: selector 2f409903d0f7e1e62e3767d985a58e567c5e59bd4eabed71e09d4c7cd000e9db; optimality ea4d38d015470d288fb2ee6b7bcf009ac573c722e1aa832045a77cfdbc080ec9; ladder 1a5cb7a77fe22c3a88b0ebef726e29561a87b95cd8f02210baf31ca21faa824b.
At the package12 audit, global lint exit1 for6 foreign unwired modules: AntitoneDyadicStencil, BandLimitedLaplaceEnergy, ClampedExponentialRamp, FiniteFilterSchurResidual, NyquistResidualMass, SignedPrimePolarContinuousFactorialLift. /tmp/bsu-minimum-response-lint-final.log; no own failure, no foreign edit.


## Package13: quantitative regularized full-Gram producer, verified

ONE significant contribution; cumulative13/100 at that audit, current15/100, full goal ACTIVE. Seven new leaves under formal/GaloisForLFunctions/BiScaleUncertainty/: RegularizedGramGeometry (13 public theorems), PhysicalCollarMixture (10), PhysicalPriceResponse (15), RegularizedPhysicalGram (14), RegularizedGramDescent (7), RegularizedGramIteration (5), QuantitativeGramProducer (13): total77 public theorems.

For actual compact continuous real f, R=h_f(0), delta=log2/2, N=n+2. H=sqrt(R)||P_a||. H_e=sqrt(H²+(eR)²), K_e=R(W+mass)-H_e. For e>=0, 0<=K-K_e<=eR, and coefficient loss 0<=C-C_e<=e delta R. Every signed measured Gram entry remains. For e>0, regularized remainder D_e=H_e(b)-H_e(a)-R sum_i(b_i-a_i)cov_a(t_i)/H_e(a) obeys
2H_e(a)D_e=R||P_b-P_a||²-(H_e(b)-H_e(a))² and 0<=D_e<=||P_b-P_a||²/(2e). Zero source and zero original packet are included; no Gram conditioning assumed.

Actual physical mixtures share=(1-tau)rho+tau eta. Packet displacement=tau(P_rho-P_eta).
M_n=2(n+1)*logarithmicCollarWeightBound n>0; T_n=transportedMass n=integral_(delta,log(n+2))w>=0, both source-independent.
Actual squared displacement<=2R M_n(mass_rho+mass_eta); exact mass transport gives integrated bound4R M_nT_n.
Thus integrated regularized mixture remainder<=B tau² with B=2R M_nT_n/e.
Only combined kernels, bounded costs/differences are integrated; never singular origin weight alone.

CollarPrice encodes actual bounded measurable prices. Mask inactive price1 but minimize only active collars. minimumResponse uses equal sharing among all active minimizers, yielding a measurable exact physical partition and attained linear minimum. Instantiate with actual regularized source prices (1+cov/H_e)/2 in[0,1], not a supplied analytic oracle. Generic response is fractional on ties; package12 pure least-index response unchanged.
Actual regularized gap G_e>=0 dominates every competitor objective difference; damped gain>=tau G_e-B tau².

regularizedIterate starts equalMultiplicity, successor mixes with its actual minimum response using tau_t=2/(t+2). No inner acceptance test required; regularized coefficients need not be monotone. For every actual competitor eta, C_e(eta)-C_e(iterate(t+1))<=4B/(t+3). Original error adds only e delta R.
Choose e_k=1/(k+1), gramProducerIterations n k=ceil(8M_nT_n(k+1)²), quantitativeGramProducer f n k=iterate(...)(ceil(...)+1).
Then 0<=S_n(f)-C(producer)<=R(delta+1)/(k+1).
Work count depends only on cutoff and accuracy, not f. This is a finite functional construction, not a numerical computational-complexity claim.

quantitativeGramLadder f0=producer f0 0. At successor keep larger ORIGINAL coefficient between fresh producer f(n+1)(n+1) and physical extension of previous ladder. A_n=quantitativeGramCoefficient f n is monotone, 0<=A_n<=S_n, allocation error<=R(delta+1)/(n+1), A_n tends to S_infty, iSup A_n=S_infty. Normalized monotonicity and convergence include R=0.
0<=S_infty/R-A_n/R<=(delta+1)/(n+1)+8exp(delta/2)/(sqrt(N)*(1-2/N²)).
All compact continuous f have actual finite-window ENNReal source-energy bound; compact C2 f have A_n/R<=S_infty/R<=J_arch/R.
DO NOT transfer equality L=S_infty to older gramResponseLadder; its equality/gap decay still open.
DO NOT identify source-dependent S_infty/R with blind-grid H_infty or unrestricted sharp source infimum.

Search: /tmp/bsu-regularized-curvature-search.log deep partial100.31s, irrelevant generic Gram/spectral candidates. Rephrased lexical all60hits14modules inspected across /tmp/bsu-regularized-lexical{,-page2,-page3}.log; old packet/remainder dependencies reused. Source-only, semantic completeness unmeasured; no exhaustive novelty claim.



### Package13 evidence

Seven leaves, respectively 13, 10, 15, 14, 7, 5 and 13 public theorems:

- `RegularizedGramGeometry`: `c70f58673b66f62b8eaa10a5a9388875b59b71c159f0248bf083cfe68a69fabf`.
- `PhysicalCollarMixture`: `59e5a05dd8abb8ed2a943fad03a934664ee6a918734c2a2a51429627f5ef811f`.
- `PhysicalPriceResponse`: `19332c0ba583e30daeb39d12bd726b7e37c83d8615eaf2a0c28242b66fe50336`.
- `RegularizedPhysicalGram`: `037a3ecc363d2a919a8ae47f476d9f1b908d275a72ae33ad692996ac59b9aa2e`.
- `RegularizedGramDescent`: `7bb77eb3e38a5a7b302dbec8062b92f2c19211942e7d04049388f74a3d71f65c`.
- `RegularizedGramIteration`: `14b0fb7387867441fb31ee3d1bd1e5d0342a32630e127068e45cd6494df16e2d`.
- `QuantitativeGramProducer`: `1941ad65cb071a04258ae520efbf53f43432e400b3d59e338d76d4dc75e2c111`.

All seven dependency compiles pass with empty logs. All 77 public theorems were
axiom-audited exactly once; only `propext`, `Classical.choice`, and `Quot.sound`.
Nine capstone signatures and eight concrete definitions were printed and inspected.
Audit: `/tmp/bsu_regularized_axioms.lean`, `/tmp/bsu-regularized-axioms.log`, and
`/tmp/bsu-regularized-audit-coverage.json`.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/QuantitativeGramProducer.lean`;
exit 0, empty log, no `-o`. Evidence `/tmp/bsu-regularized-final.{log,exit}`.
Dependency logs: `/tmp/bsu-regularized-{geometry,mixture,response,physical,descent,iteration,producer}.log`.

Index refresh exits 0. Three requested exact capstones are discoverable:
`quantitativeGram_source_certificate`, `iSup_quantitativeGramCoefficient`, and
`quantitativeGramProducer_error`. Evidence `/tmp/bsu-regularized-index.log`,
`/tmp/bsu-regularized-discovery.json`, and discovery-coverage JSON.
All 43 owned imports occur exactly once, all 36 prior source hashes remain
unchanged, all seven current hashes match the manifest, and scoped whitespace
passes. Read-only README is byte-identical at
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Global lint exits 1 for the 15 foreign unwired modules listed in the facts ledger
and `/tmp/bsu-regularized-lint.log`; no own failure or foreign edit.
Integrity evidence: `/tmp/bsu-regularized-{manifest,integrity}.json`.
Temporary API probe and two obsolete drafts removed; successful audit scratch
and logs retained. All owned jobs terminal. No full/umbrella build, numerical
experiment, heartbeat increase, commit or push. This construction counts once:
At the package-13 audit: **13/100**; current total **15/100**, full objective active.

Reusable repairs: unfold `IntegrableOn` explicitly when transporting a pointwise
integrable sum. Give real integrands and integration functions explicitly before
`integral_nonneg`, `integral_sub`, and `integral_add`. Normalize successor casts
with selected `Nat.cast_add`, `Nat.cast_one`, `Nat.cast_succ`, and `add_assoc`
lemmas before recurrence inequalities. Annotate old/fresh dependent partitions
in recursive ladder branches; normalize final scalar order using `ring`.

At package13 the sharp-tail candidate was paper-only; package14 below now certifies it. Its right-node tail
extension must assign the endpoint x=log N to old node N and truncate each new
cell by the open log M window. This repairs the exact partition law while leaving
old fibres unchanged for y>0. The candidate leading law concerns independent
P_N only, not the full signed-Gram optimum or unrestricted source infimum.

## Next frontier: paper-only, uncounted

Package10 now certifies full measured signed-Gram trial gaps. User Trap10 steering: prioritize explicit producers with unconditional error bounds, not receiver-only reformulations with unresolved hypotheses. No pre-floor subtraction of discrete counterterms. Stay on multi-coset quantitative source-energy topic; no RH work. Existing ExplicitNyquistPolarAndChebyshevFactorialProducer.lean source states nyquist_cell_polar_producer_l2_error_le (integral squared error<=1/(16n²)), abs_chebyshevAlternatingProducer_sub_linear_le (|T2N-2TN-2Nlog2|<=2log(2N+1)+1), abs_chebyshevBiNullProducer_le (|T4N-4T2N+4TN|<=5log(4N+1)+1). Important correction: raw first stencil is NOT O(logN), only its centered error. Cell bound is squared L2 norm, not norm. Source proof bodies inspected; scratch import audit FAILED solely because this foreign module's .olean is absent. No fresh Lean-verification claim. /tmp/bsu-trap10-reference-audit.log; failed probe deleted. Existing producers not counted as this agent's contributions. Trap10 search /tmp/bsu-trap10-stencil-search.log:22 declarations1module, partial/source-only/older/semanticunmeasured.

NEXT PRIORITY: formalize the paired leading tail and exact delayed fourth-root saturation law. Package15 now proves explicit uniform g>0 with Q_N≥P_N+g for N≥3 and Q∞≥P∞+g; eventual paired-branch selection is also Lean-certified. Reuse actual concentrated extension/retraction from package14. Define paired array norm R=sqrt(A²+B²), prove its padding and unit l1 perturbation properties using paired radial capacity at W=0, and instantiate the same8192/N and12288/N radial budgets. Target |Q∞−Q_N−4/sqrtN|≤12289/N forN≥8; then eventual C_N=Q_floor√N plus floor arithmetic should yield |Q∞−C_N−4/N^(1/4)|≤24586/sqrtN and scaled limit4. These paired tail and floor-normalization claims remain paper-only and uncounted. Do not transfer to full S_N(f), H_N or unrestricted source optimum.

Search /tmp/bsu-minimum-response-next-regularization-search.log completed57.84s; proposed Sobolev curvature ingredients are not this packet problem. Rephrased lexical search2 unrelated origin-regularization hits; field text search finds source averaging, no augmented-packet norm implementation. Source-only/older/semanticunmeasured, no exhaustive novelty claim.

Secondary structural route: signedGramShift is fixed in fibre y, only weights/anchor vary. Arbitrary finite translates of a nonzero compact source should be independent, yielding actual fixed-cutoff anchored Gram residual and curvature control; do not assume cutoff-uniform coercivity (package11 forbids it). Deep search /tmp/bsu-minimum-response-next-coercivity-search.log completed91.43s; both lexical pages next-independence{,-page2}.json inspected,31hits14modules; no generic field LinearIndependent/PosDef source implementation. Fresh concurrent FiniteFilterSchurResidual.lean uses support supremum to prove escape for a PARTICULAR finite hyperbolic filter and a strict two-projection residual. Its first100lines/proof and declarations inspected, not freshly Lean-audited here. Reuse that mechanism; do not count or edit the other agent's result. Generic independence alone should not be counted without connecting to actual signed-node Gram/curvature consequences.

Secondary structural candidate, paper mechanism only: distinct finite translates of nonzero compact continuous f are linearly independent. Choose smallest active shift, supremum of support, source value in final interval shorter than shift gap; all other terms vanish there. Continuity gives positive L² norm. With fixed positive anchor, norm equality would imply identical weights and strict kernel concavity; optimizer existence/converse not proved. Corpus deep independence search irrelevant; lexical translate independent 156decl mostly special-function differential independence. No formal claim/count.

Further open: exact nonzero-lag multi-column support, unequal-size product-zero constraints, strict H∞ versus Q∞ separation, paired matching leading laws and full measured-Gram sharpness. The Q∞ versus P∞ strict gap is closed by package15. Do not identify S∞/R with blind-grid H∞.

The formerly paper-only activation criterion is now fully certified in package7. Finite-vector sharpness still does not assert actual autocorrelation realization.
The sandwich and same-limit hierarchy route is now proved via new capacity, padding, and actual constraint inclusion. Uniform low cutoff still ignores valid products with unequal node sizes; these may yield a sharper hierarchy. Strict B_N>C_N is not proved.

Package14 certifies the independent leading law with explicit rational remainder12289/N forN≥8; the older finer constants atN≥4 remain paper-only. Package15 now proves the formerly conjectural uniform first-node paired gap and eventual paired-branch selection. Only the paired leading tail and exact delayed fourth-root law remain unproved in that route; see the dependency-closed paper argument below.

Corpus logs /tmp/bsu-paired-sphere-search.log, /tmp/bsu-capped-block-search.log, /tmp/bsu-paired-cutoff-search.log: hybrid useful source-only hits, no exact lexical hits, semantic coverage unmeasured; not exhaustive absence or novelty. Product-zero activation caution: -log2/+log3 first pinned at N=6; old-node Gram constraints can change with cutoff. Do not transfer local allocation tail laws to full Gram cone without new proof.

Read current biscale/infinite-grid-tail-rigidity memory this turn: other agent certified exact distance-to-grid classification for separated canonical polar copies, cost proportional to -log distance. This constrains that family, not the global finite-source infimum; do not count or modify their results.

## Toolchain repairs

One owned foreground Lean process at a time. Imports can take 5–8 minutes under shared memory pressure; poll the existing handle, never restart for an observation timeout. No full/umbrella builds, heartbeat increases, numerical experiments, commits or pushes. Verify new mathlib names in /tmp scratch with this toolchain; #print axioms only in /tmp. Final audit is lake --old env lean <leaf>, without -o. Targeted dependency compiles may use -o and -j 1. Remove API probes after audits; retain audit/log evidence.

Use explicit function compositions and change before measurability proofs across actual-source subtype coercions. Avoid broad unfolding that triggers default-heartbeat defeq failures. Expose beta-redexes before rewriting supremum or antitone goals. Complex packet sums need explicit Finset.sum lambdas for both signed terms; force real inverse before complex coercion; use explicit real-valued change for RCLike.re. Normalize Nat casts with selected simp lemmas instead of norm_cast when it moves a real expression back to Int. Bare simp only reduces reflexive ifs before push_cast/ring.

Global tendsto_atTop_ciSup exists; Monotone.tendsto_atTop_ciSup does not. Fintype.sum_bool exists, Finset.sum_bool does not. Finset.exists_mem_eq_sup'/inf' give finite attainment, while sup'_mem is closure under sup. Nat.pow_le_pow_right takes positive base then exponent inequality. MeasurableSet.iInter/iUnion are the actual names. For measurable selection cells use an explicit set equality before applying intersection measurability; broad simp can change the target to measurability of a Prop-valued function. Scratch API checks need matching open namespaces. Further verified API/proof repairs and all historical hashes/logs are in the owned facts ledger/card; do not reconstruct names from memory.


## Package14: exact leading independent allocation tail [Lean verified]

For N=n+2≥8, |P∞−P_N−4/sqrtN|≤12289/N and sqrtN(P∞−P_N)→4. P_N is PhysicalCollarPartition.optimalCoefficient n, the independent signed-coset sphere allocation optimum. Actual smooth nonzero grid sources satisfy normalized energy≥P∞−4/sqrtN−12289/N. This does not identify the full measured signed-Gram optimum S_N(f), blind-grid Schur hierarchy H_N, or unrestricted source infimum.

Actual rightNode uses ceil(exp x) above log4 and equalMultiplicity below. concentratedExtend splices the old extension below logN with rightNode above; retains old fibres and adds nonnegative rightTailWeight supported at0<y≤1/N. concentratedRetract keeps old shares and fills missing fraction1−oldShareSum with rightNode; rightRepairWeight is supported at0<y≤2/N. Uniform fibre mass≤32sqrtN, mesh mass≤64/sqrty, and1≤2y*w(y) yield integrated radial penalty increments≤8192/N and≤12288/N. Coefficient=physicalMass−integral(radialPenalty); never integrate singularW alone. No optimizer attainment or external error premise.

For M≥N≥8, T_N−T_M−8192/N≤P_M−P_N≤T_N−T_M+12288/N. Endpoint tail0≤T_N−4/sqrtN≤(8/5)exp(−5logN/2)≤1/N. Limit passage gives exact leading4. The remainder constant12289 is not claimed optimal. All10leaves79theorems form ONE significant contribution; cumulative14/100, goalACTIVE.

## Sharp leading tail verification (package 14)

Ten leaves, respectively 7, 11, 11, 7, 11, 8, 2, 11, 6 and 5 public theorems:

- `RightNodeCollarPartition`: `2ef65f8ca21433139874a1868f9c6e8844b9b54c4f457755331478bd52c7755e`.
- `CollarRadialPenalty`: `86e653c91eba37ecd30bb05ef095d3ceb5b28b45cd52b670f2869a0902ea9cff`.
- `CollarMeshBounds`: `4c10614e6aed7f4ed8317f3b77a33df417617ef1ea6ebc703f8d8d7d713bf1e4`.
- `ConcentratedCollarExtension`: `682ebcb4cd195af5904532559d7a36b2003f429fcc3944c45d5d059fa7236b98`.
- `ConcentratedCollarRetraction`: `6f8fbf9e9eed5355f370295d7940428c2e2dbfc3be372a3bb4978dba8a281601`.
- `LogarithmicArrayRadialComparison`: `ef77a033b9b06bb8415850a44301f98c622c85ee03bcdd06402850d466ee6c38`.
- `ConcentratedCollarPenalty`: `64b40713473a99f38b425cb1f7ea8b9a281b688003a2a0be82201ff0f062d074`.
- `CollarEndpointTailMass`: `16497c3494a18caa9bea3d138ddb7ef61624e7777e8cc9dcda312215898110f7`.
- `SharpCollarCutoffComparison`: `a77cff7e890162f37c6e0d17a0ef4aa583399406e9a9d13016a521c8968ff1da`.
- `SharpCollarAsymptotics`: `10e62be5a9f9bc0ab4d26910bb20cf353666ef9f9fa458c035b53cfebc4408a2`.

All ten dependency compiles pass with empty logs. All 79 public theorems were
axiom-audited exactly once; only `propext`, `Classical.choice`, and `Quot.sound`.
Ten capstone signatures and seven concrete definitions were printed and inspected.
Audit: `/tmp/bsu_sharp_tail_axioms.lean`, `/tmp/bsu-sharp-tail-axioms.log`, and
`/tmp/bsu-sharp-tail-audit-coverage.json`.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SharpCollarAsymptotics.lean`;
exit 0, empty log, no `-o`. Evidence `/tmp/bsu-sharp-tail-final.{log,exit}`.
Dependency logs: `/tmp/bsu-sharp-tail-{right-node,radial,mesh,extension,retraction,array,penalty,endpoint,comparison,asymptotics}.log`.

Index refresh exits 0. The three requested exact capstones are discoverable:
`optimalCoefficient_sharp_leading_error`, `optimalCoefficient_sharp_saturation_limit`,
and `sharpCollar_source_lower_bound`. All five declarations returned in the
restricted module search were inspected. Evidence:
`/tmp/bsu-sharp-tail-index.log`, discovery JSON and discovery-coverage JSON.
All 53 owned imports occur exactly once, all 43 prior source hashes are unchanged,
and the ten current hashes match the manifest. Scoped whitespace passes.
Read-only README remains byte-identical at
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Global lint exits 1 for twelve foreign unwired modules, listed in the facts ledger
and `/tmp/bsu-sharp-tail-lint.log`; no own failure or foreign edit.
Integrity: `/tmp/bsu-sharp-tail-{manifest,integrity}.json`.
Temporary API probe and three obsolete drafts removed; successful audit scratch
and logs retained. All owned jobs terminal. No full/umbrella build, numerical
experiment, heartbeat increase, commit or push. One significant contribution:
**14/100**, full objective active.

Reusable proof details: abstract exponential-denominator algebra to real variables
before clearing denominators. Supply constant-integrability arguments through
`exact` so automatic finiteness arguments elaborate. Expose pointwise function
differences with `change` before rewriting integrals. Expand composed limits
before simplifying square roots. Avoid redundant tactics after `field_simp`.

The forced first-node gap proposed at the package-14 audit is now certified in
package 15 below, including eventual paired-branch selection. The paired leading
tail and the exact fourth-root saturation law remain the next uncounted candidates.


## Package15: uniform paired gain and strict limiting separation [Lean verified]

Let e=log3−log2−δ>0, a=e/3, b=2e/3, W0=2/(1−exp(−2a)), g=(b−a)/(W0+2)>0.
For all physical cutoffsN≥3 and every admissible partitionρ, pairedCoefficientρ≥coefficientρ+g. Thus Q_N≥P_N+g and Q∞≥P∞+g>P∞. Exact share conservation forces node2 share1 on both branches at offsetsy∈(a,b]; later collars cannot cover either point. Their weights≥1 force both whole-sign normsA,B≥1. WithW≤W0, the rationalized paired gain≥1/(W0+2). Integrate and take suprema/limits without optimizer attainment.

The product hierarchy C_N eventually equals Q_floor(sqrtN), and eventuallyC_N>P∞+g/2. Every actual smooth nonzeroN-grid source has normalized energy≥P∞+g−16exp(δ/2)/N^(1/4) forN≥4, and eventuallyenergy>P∞+g/2 uniformly over all sources. For each admitted frameK≥8,K²≤N, the stronger inherited bound isP∞+g−4/sqrtK−12289/K. This excludes asymptotic sharpness of the independent limiting certificate for actual growing-grid sources. The constantg is not claimed optimal, and there is no identification with full measured-Gram or unrestricted source optimality.

All3leaves25theorems form ONE significant contribution, cumulative15/100; goalACTIVE. All53 prior owned sources remain unchanged. This turn made verified progress.

## Uniform paired gap verification (package 15)

Three leaves, respectively 10, 7 and 8 public theorems:

- `ForcedFirstCollar`: `a06b3ca66acb31311f88a0d97822b31f1d1e834df2582d215c0606488493802a`.
- `UniformPairedCollarGain`: `7d788a7d463068841fd81d712f957aa6ef413556ab9eb11a13cdfe3d123025cc`.
- `StrictPairedCollarLimit`: `136b5da409462a77805ce5b82548c84d77692f770bf269f49b03419dd6ebc31c`.

All three dependency compiles pass with empty logs. All 25 public theorem axiom
audits pass exactly once, using only `propext`, `Classical.choice`, and `Quot.sound`.
Twelve signatures and six explicit constant definitions were printed and inspected.
Evidence: `/tmp/bsu_paired_gap_axioms.lean`, `/tmp/bsu-paired-gap-axioms.log`,
and `/tmp/bsu-paired-gap-audit-coverage.json`.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/StrictPairedCollarLimit.lean`;
exit 0, empty log, no `-o`. Evidence `/tmp/bsu-paired-gap-final.{log,exit}`.
Dependency logs: `/tmp/bsu-paired-gap-{first,uniform,limit}.log`.

Index refresh exits 0. All three requested capstones are discoverable:
`limitingCollarCoefficient_lt_limitingProductCoupled`,
`eventually_productCoupled_eq_paired`, and `uniformPaired_source_fourth_root_bound`.
All eight returned declarations were inspected. Evidence:
`/tmp/bsu-paired-gap-{index.log,discovery.json,discovery-coverage.json}`.
All 56 owned imports occur exactly once; all 53 prior source hashes and all three
current hashes match their manifests. Read-only README is unchanged at
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Scoped whitespace passes. Global lint exits 1 for five foreign unwired modules
listed in the facts ledger and `/tmp/bsu-paired-gap-lint.log`; no own failure.
Integrity: `/tmp/bsu-paired-gap-{manifest,integrity}.json`.
API scratch removed; successful axiom scratch and logs retained. All owned jobs
terminal. No full/umbrella build, numerical experiment, heartbeat increase, commit
or push. This is one significant contribution: **15/100**; full goal active.

The first and final leaves passed on their first check. The uniform-gain leaf
needed only removal of a redundant `ring` after `field_simp` had already closed
the goal. Existing physical partition conservation, single-coordinate norm bounds,
and paired radial rationalization suffice; no optimizer-attainment interface was added.

## Next paired leading-tail candidate [paper proof; uncounted]

Write A,B for the whole-sign norms and R=sqrt(A²+B²). The paired kernel equals
physical mass minus r_W(R), with r_W(R)=sqrt(W²+R²)−W. R≤A+B≤mass.
The existing paired radial capacity theorem at W=0 gives monotonicity and a
unit l1 perturbation bound for R; signwise zero-padding preserves R. Therefore
the actual concentrated extension and retraction from package 14 should satisfy
the same radial budgets 8192/N and 12288/N, now with R in place of A+B.
The same endpoint tail and supremum argument would give

    |Q∞−Q_N−4/sqrt(N)|≤12289/N,   N≥8.

Exact obligations: define the paired array norm and integrable physical radial
penalty, prove padding and unordered perturbation comparisons, specialize them to
both actual constructions, then integrate and pass through the paired suprema.
None of these new paired tail statements is yet Lean-certified.

Package 15 already proves C_N=Q_K eventually, K=floor(sqrt N). Once the paired
tail law is verified, floor arithmetic gives K≥sqrt(N)/2 and 0≤sqrt(N)−K<1.
Hence 0≤1/sqrt(K)−1/N^(1/4)≤1/K for K≥1. For sufficiently large N,

    |Q∞−C_N−4/N^(1/4)|≤12293/K≤24586/sqrt(N),
    N^(1/4)(Q∞−C_N)→4.

This is a dependency-closed paper route to the exact coupled saturation exponent
and leading coefficient. The floor normalization and paired tail estimate both
remain formal obligations. It concerns the delayed paired hierarchy only, not
full measured-Gram or unrestricted-source optimality.
