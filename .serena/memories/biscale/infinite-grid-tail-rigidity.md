# Infinite-grid tail rigidity — certified frontier

Goal ACTIVE: 100 significant mathematical packages in independent BiScaleUncertainty, not RH. Certified **7/100**. Count connected results, not helper lemmas. Read attachment `/Users/michael/.codex/attachments/ec12590a-2ebd-4912-837b-1b97ebc4e121/pasted-text-1.txt` each continuation. No hgtl7, numerical experiments, heartbeat hacks, full/umbrella builds, unproved analytic interfaces. One owned foreground Lean process at a time; final audits `lake --old env lean <leaf>`. No subagents requested.

Authoritative ledger `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity-FACTS.md`; parent card `docs/drafts/pipeline/1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`. Papers and formalized cards linked there. Read current files, preserve concurrent agents' research and umbrella edits.

## Certified results
1. `InfiniteGridTailRigidity.lean`, `LogarithmicIncrementEnergy.lean`: 22 theorem audits. ceil(exp T) lag in [0,exp(-T)], separated-copy detecting sample=-a h_f(lag). Fixed-source polar copies eventually violate the infinite grid; arbitrary changing compact C² seeds preserving the sample pay E>=exp(-1/2)T/4, seed and copy. Quantitative logarithmic increment theorem and local/error-sensitive variants.
2. `LogarithmicCompressionEnergy.lean`, `InfiniteGridPolarRecovery.lean`: 17 theorem audits. Actual smooth compact polar all-grid sources at arbitrarily large logarithmic midpoints, exp(-1/2)T/4<=E<=C+T. Compression upper bound E(f(L .))<=A+log L for L>=D. Exact polar error scaling L^-1.
3. `LogarithmicGridDistance.lean` (8), `InfiniteGridDistanceClassification.lean` (7): d(T)=min(T-log floor(exp T),log(floor(exp T)+1)-T), T>=2; nearest distance attained, <=exp(-T)<=1, positive iff off-grid. Radius-half smooth canonical polar copies exist exactly off-grid, with E of order log(1/d(T)), uniform upper constant.
4. `FiniteTranslationTrains.lean` (9), `FiniteCopyTailRigidity.lean` (6): finite common-seed trains G=sum c_j f(.-jS), nonzero endpoints, S>D+1. Near origin hG=Qhf; near L=mS only endpoint pair survives. All-grid zeros force d(L)>0 and E(seed),E(train)>=exp(-1/2)log(1/d(L))/4>=exp(-1/2)L/4 despite interior cancellation. Division-free final endpoint derives support threshold from source and covers zero mass.
5. NEW `FiniteTrainActiveLags.lean` (7 public), `FiniteTrainGridClassification.lean` (5 public plus private finite-radius helper): complete active-lag criterion. For nonzero c and S>=2, an actual smooth positive-mass radius-half seed yields a positive-mass all-grid train iff every positive active center kS is off-grid, where A_k=sum_{j-i=k}c_i c_j. Inactive packets impose no grid restriction. At every active center kS>=2, arbitrary compact C² seeds with S>D+1 pay E(seed),E(train)>=exp(-1/2)log(1/d(kS))/4. Interior near-resonances can exceed endpoint cost. Constructive dilation supplies the seed. Exact finite exponential symbol multiplies source moments; symbol zero at rate1/2 gives polar balance for the same constructed source.

6. NEW `LocalCorrelationEnergyStability.lean` (4), `FiniteTrainUniformEnergy.lean` (10): uniform matching cost for every compatible finite train. Define delta=min({1} union {d(kS):positive active k}); attained, 0<=delta<=1, positive iff compatible. One C works for all packet counts, nonzero coefficients, S>=2: actual smooth radius-half positive-mass seed/train, allgridzeros, exp(-1/2)log(1/delta)/4<=E(train)<=C+log(1/delta), and polar balance if finite symbol at1/2 vanishes. Lower bound holds for every admissible seed/train with separation S>D+1. Main new tool: if normalized correlations agree on [0,a], energy difference <=2 integral_a^infinity w. For trains use a=1; compress fixed bump to delta/4. Empty active set delta=1 handled. No optimal coefficient or arbitrary-shape theorem claimed.

7. **Arbitrary-source uniform modulus and tails**: InfiniteGridUniformTail.lean (10 public theorems, one private normalization helper). For any compact C² real source, c=exp(-1/2), R=h(0), J=Levy energy: c(-log|x-y|)(h(x)-h(y))²<=8RJ for 0<|x-y|<=1. Grid-free sampling error c T(h(T)-h(log ceil(exp T)))²<=8RJ for T>=0. With all grid zeros, c|T|h(T)²<=8RJ for EVERY real T; for R>0 divide by R² to get c|T|(h(T)/R)²<=8E. Uniform family continuity radius delta=exp(-(1+8K/(c epsilon²))) for E<=K; full-grid family tail radius A=1+8K/(c epsilon²). Window c A integral_A^B h²<=8(B-A)RJ for 0<A<=B; dyadic integral decays as1/logN. No common seed/support/derivative bound/sign interval. Unweighted tail question resolved; exponentially weighted polar tail remains open. Count connected package once.

## Latest certification
Package7: direct leaf `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridUniformTail.olean GaloisForLFunctions/BiScaleUncertainty/InfiniteGridUniformTail.lean` from formal/ passed exit0 without diagnostics. Scratch /tmp/infinite_grid_uniform_tail_axioms.lean imported emitted artifact; all10 theorem audits only propext/Classical.choice/Quot.sound. Private helper audited transitively. Umbrella import and all10 generated API entries verified. Paper docs/reports/BiScaleUncertainty/InfiniteGridUniformTail.md; card docs/drafts/pipeline/3-formalized/infinite-grid-uniform-tail-2026-10-17.md. Ledger/parent card count7. Logs /tmp/infinite-grid-uniform-tail-{leaf,axioms,index,lint}.log. Global lint exit1 only4 foreign unwired modules: RHTower.FermiNymanDyadicFoldGeometry; BiScaleUncertainty.CappedCollarArrayComparison, CappedCollarCutoffComparison, CappedSupportComparison. No ownlint error. Index succeeded. All ownedjobs terminal. No claimglobalgreen.

## Exact reusable APIs
Namespace GaloisForLFunctions.BiScaleUncertainty; open MeasureTheory Set Filter Topology; open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole; open scoped BigOperators.
- `autocorr_increment_mul_log_le hf hfc hd hd1`: exp(-1/2)*(R-h(d))*(-log d)<=4J, 0<d<=1. Ceiling-lag version `autocorr_logarithmicCeilLag_energy_bound hf hfc hT0` includes zero lag/mass.
- `exists_pos_autocorr_support_radius hfc`: exists D>0, forallx,D<|x| ->h_f(x)=0.
- `exists_logarithmicGridDistance_node hT`: exists n>=2,|log n-T|=d(T).
- `logarithmicGridDistance_le_node (T:=T) hn` has NO hT argument. `logarithmicGridDistance_pos_iff hT`, `logarithmicGridDistance_le_one hT`, `logarithmicGridDistance_le_exp_neg hT`.
- `exists_sourceRescale_logarithmic_energy_bound_of_support hf hfc hR hD hsupp`: exists A forall L>0,D<=L,E(f(L .))<=A+log L. `sourceRescale f L u=f(Lu)`, `autocorr_sourceRescale f hL x=L^-1 hf(Lx)`.
- `exists_smooth_compact_source_positive_mass` in BroadSpectralCostRealization gives actual C∞ compact seed. NEW `exists_smooth_compact_source_small_correlation_support hρ` directly gives C∞ compact positive mass with h=0 outside radiusρ.
- `integrableOn_archLevySinhWeight_Ioi ha`, `integral_archLevySinhWeight_Ioi ha` exact log+arctan tail; `integral_archLevySinhWeight_Ioi_le ha ha1` bounds tail by log(6/a)+pi. See LogarithmicCompressionEnergy lines20–62.
- `finiteTranslateSource f s c t u=sum i in s,ci*f(u-ti)`; `copyTrain f c S` uses Fin(m+1) shifts i.val*S. `copyTrainMass c=sum ci²`.
- `copyTrainMass_pos_of_exists hc`, where hc:existsi,ci!=0; regularity `contDiff_copyTrain hf c S`, `hasCompactSupport_copyTrain hfc c S`.
- `autocorr_copyTrain_local hfcontinuous hfc c hD hsupp hS hx`: hG(x)=Qhf(x), |x|<=1, S>D+1.
- `copyTrainLagCoefficient c k` uses signed integer k and double sum if j.val-i.val=k. `_zero`=Q, `_neg` even.
- `autocorr_copyTrain_grouped hfcontinuous hfc c S x`: sum over integer Icc(-m,m), A_k hf(x-kS).
- `autocorr_copyTrain_near_lag hfcontinuous hfc c hD hsupp hS hk hx`: exact A_k packet, hk:k in integer Icc(-m,m), hx:|x-kS|<=1.
- `CopyTrainGridCompatible c S := forall k:ℤ,1<=k ->k<=m ->A_k!=0 ->forall n:ℕ,2<=n ->kS!=log n`.
- `copyTrain_grid_compatible_of_zeros` proves necessity from compact continuous positive-mass seed.
- `copyTrain_active_lag_energy` gives distance positivity and lower costs for seed/train, with any nonzero coefficient vector, general support D and active center>=2.
- `exists_smooth_copyTrain_grid_source c hc hS hoff`: actual C∞ compact seed radiushalf positive mass, actual C∞ compact train positive mass, allgridzeros, and (copyTrainExpSymbol c S (1/2)=0 ->polar moment=0).
- `exists_smooth_copyTrain_grid_source_iff c hc hS`: seed existence iff compatible.
- `copyTrainExpSymbol c S beta=sum_i ci exp(beta*(i.val*S))`; `integral_copyTrain_mul_exp hfcontinuous hfc c S beta` exact source moment multiplier; `integral_copyTrain_autocorr_cosh_of_symbol_zero hfC2 hfc c S hB`.

## New package6 APIs
- `normalizedArchEnergy_eq_integral f`: E(f)=integral_Ioi0 ((R-h(x))*w(x)/R), no hypotheses.
- `normalizedArchEnergy_abs_sub_le_of_local hf hfc hRf hg hgc hRg ha hlocal`: |E(g)-E(f)|<=2 integral_Ioi a w, hlocal: forallx,0<=x ->x<=a ->h_g(x)/Rg=h_f(x)/Rf.
- `normalizedArchEnergy_copyTrain_uniform_error hf hfc hR c hc hD hsupp hS`: same bound with a=1, any nonzero coefficient vector and S>D+1.
- `exists_smooth_small_support_logarithmic_cost`: exists C forallrho>0,rho<=1, actual smooth compact positive-mass f, correlation outside rho zero, E(f)<=C-logrho.
- `copyTrainActiveLags c`: integer Icc1m filtered A_k!=0. `mem_copyTrainActiveLags` iff 1<=k,k<=m,A_k!=0.
- `copyTrainGridDistances c S` inserts1 into finite image d(kS). `copyTrainMinGridDistance c S` is min'. ALL image lambdas must explicitly type `fun k : ℤ => ...`: without annotation Lean inferred real k and coerced Finset integers to reals, breaking min witness proofs.
- `copyTrainActiveLags_center_ge_two hS hk`.
- `copyTrainMinGridDistance_le_one c S`, `copyTrainMinGridDistance_le_active S hk`, `copyTrainMinGridDistance_attained c S` (delta=1 or existsactivek,delta=d(kS)), `copyTrainMinGridDistance_nonneg c hS`, `copyTrainMinGridDistance_pos_iff c hS`.
- `copyTrain_min_distance_energy hf hfc hR hc hD hsupp hS hsep hgrid`: delta>0, seed andtrain lowerbound; hS>=2 and hsep:D+1<S.
- `copyTrain_grid_zero_of_min_distance_support hfcontinuous hfc c hS hd hsupp`: delta>0 and correlation radiusdelta/4 imply allgridzeros.
- `exists_smooth_copyTrain_uniform_distance_cost`: ONE C quantified before m,c,hc,S,hS,compatible, then actual source with lower/uppercost and polar implication.
- Toolchain names: `integral_div_const` DOES NOT exist; used `simp only [div_eq_mul_inv, integral_mul_const]`. `Finset.lt_min'` does not exist; min'mem/attainment sufficed. `Finset.min'_le`, `min'_mem`, `le_min'` verified. In local-density ratio algebra field_simp closed goal directly; trailing ring caused no-goals error, removed.

## New package7 APIs
All in namespace GaloisForLFunctions.BiScaleUncertainty, file InfiniteGridUniformTail.lean.
- autocorr_difference_sq_mul_log_le hfC2 hfc hdPositive hdLeOne: global raw square/log modulus.
- normalized_autocorr_difference_sq_mul_log_le hf hfc hR hd hd1: differences of h(x)/R, bound8E.
- exists_uniform_autocorr_continuity_radius hK0 hepsilonPositive: exists delta>0, forall compactC²sources R>0 E<=K, forallx y |x-y|<delta implies normalizeddifference<epsilon; no grid.
- autocorr_logarithmicCeilNode_error_sq_le hf hfc hT0: raw grid-free sample difference.
- autocorr_sq_mul_location_le_of_infinite_grid hf hfc hzeros hT0.
- autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hzeros T.
- normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hR hzeros T.
- exists_uniform_infinite_grid_tail_radius hK0 hepsilonPositive: existsA>0, forallf hf hfc R>0 E<=K hzeros, forallT A<=|T| implies |h(T)/R|<epsilon.
- integral_autocorr_sq_window_mul_left_le hf hfc hzeros hApos hAB: cA integral_A^B h²<=8(B-A)RJ.
- integral_autocorr_sq_dyadic_mul_log_le hf hfc hzeros hN2: c logN integral_logN^log2N h²<=8log2RJ.

## Next conjecture (unproved and uncounted)
Every sequence of normalized autocorrelations from compactC²positive-mass all-grid sources with E<=K should have a subsequence uniformly converging on ALL real numbers. Limit continuous/even/positive-definite, h(0)=1, vanishes at infinity and everyloggridnode, kernelLevyenergy<=K. Common modulus+uniformtails+|h|/R<=1 suggest compactness; positivity and nodezeros pass through uniformlimit; nonnegativeintegrandFatou should preserveenergyceiling. Do not assumecompactsource or L²source realization, or closedness of exponentiallyweightedpolar moment. Need inspectinstalledAscoli/C0/FatouAPIs, completepaperproof thenformalizeexactsource-derivedendpoint. Search /tmp/infinite-grid-compactness-search.txt finished exit0; useful foundational source-only hits, oldergenerationcoverage, semanticcoverageunmeasured.
Later possibilities: sharpen inverse-square-root tail rate; independentlyshapedpackets; truepolar-tailcontrol. Symbolic four-packet cancellation example remains unformalized: r=exp(S/2), c=[1,1/r,2/(r²(r²-1)),-2/(r(r²-1))], P(r)=0,A2=0. No claims yet.

## Operational notes
Full 735-line field README read this continuation (foreign agent edits may follow). No docs/architecture.md or docs/testing.md. Formal AGENTS.md, formal/README.md and formal/LEAN_OVERVIEW.md read. Serena manual already read; symbol tools reject ignored Lean files, use rg/read/apply_patch fallback. list_memories(topic=biscale) small; NEVER print raw unfiltered list. Storedmemory may be string: never Object.keys(string) (huge output). update_plan unavailable; pipeline cards carry plans. Don't run research/index concurrently; lint/index independent. Lean commands from formal/, not repository root. One owned Lean process at a time, wait livehandle; don't restart for polltimeout. All owned jobs terminal. No fullbuilds, commits, pushes, numericalexperiments, heartbeatoverrides. Names probe passed; scratch axiom audit retained. External classical parent audit in earlier turns: Laptev–Weth https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf Lemma2.5; distinct operator/context, no exhaustive external novelty claim.
