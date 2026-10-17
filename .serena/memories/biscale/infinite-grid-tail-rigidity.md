# Infinite-grid tail rigidity — certified frontier

Goal ACTIVE: 100 significant mathematical packages, independent BiScaleUncertainty, not RH. Certified **3/100**. Count connected results, not helper lemmas. User attachment `/Users/michael/.codex/attachments/ec12590a-2ebd-4912-837b-1b97ebc4e121/pasted-text-1.txt` excludes hgtl7, numerical experiments, heartbeat hacks, full builds, unproved analytic interfaces. One owned foreground Lean process at a time; use `lake --old env lean <leaf>`. No subagents requested.

Authoritative ledger: `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity-FACTS.md`. Parent card: `docs/drafts/pipeline/1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`. Papers and formalized cards for all three packages are linked there. Read current files; other agents edit neighboring research and umbrellas.

## Package 1 — tail detection and linear barrier
`InfiniteGridTailRigidity.lean`, `LogarithmicIncrementEnergy.lean`, 22 audited theorems. Node ceil(exp T) has lag in [0,exp(-T)]; separated-copy sample is -a h_f(lag). Fixed-source polar copies eventually violate the infinite grid. For arbitrary varying compact C² seeds, a nonzero copy preserving this sample at T>D+1 pays E>=exp(-1/2)T/4, both base and copy. Main reusable theorem `autocorr_increment_mul_log_le hf hfc hd hd1`: exp(-1/2)*(R-h_f(d))*(-log d)<=4J for 0<d<=1. Local-energy and error-sensitive variants also certified.

## Package 2 — midpoint recovery, linear upper cost
`LogarithmicCompressionEnergy.lean`, `InfiniteGridPolarRecovery.lean`, 17 audited theorems. `exists_smooth_infinite_grid_polar_recovery`: for all N>=ceil(exp 2), T=(log N+log(N+1))/2, actual smooth compact nonzero k has canonical polar copy g satisfying every grid zero and exact cosh moment zero, with exp(-1/2)T/4<=E(g)<=C+T. Centers arbitrarily large.
Support-aware compression theorem `exists_sourceRescale_logarithmic_energy_bound_of_support hf hfc hR hD hsupp`: exists A, for L>0,D<=L, E(f(L .))<=A+log L. Split at D/L; near increment bound derived from regularity, tail correlation exactly zero. Radius-free A'+2log L also available. `polarEnergyErrorConstant_sourceRescale f hL D'`: P(f(L .),D')=L^-1 P(f,D'). Actual seed theorem `exists_smooth_compact_source_positive_mass` in BroadSpectralCostRealization supplies C∞ compact nonzero f.

## Package 3 — exact distance-to-grid classification
NEW certified files:
- `formal/GaloisForLFunctions/BiScaleUncertainty/LogarithmicGridDistance.lean`: 8 theorems, 2 definitions.
- `formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridDistanceClassification.lean`: 7 theorems.
Paper `docs/reports/BiScaleUncertainty/InfiniteGridDistanceClassification.md`.
Card moved to `docs/drafts/pipeline/3-formalized/infinite-grid-distance-classification-2026-10-17.md`.

Definitions `logarithmicFloorNode T = floor(exp T)`, `logarithmicGridDistance T = min(T-log floor, log(floor+1)-T)`.
For T>=2, distance is nonnegative, attained at a grid node n>=2, <=exp(-T)<=1, and positive iff every n>=2 has T!=log n.
APIs:
- `exists_logarithmicGridDistance_node hT`: exists n>=2 with |log n-T|=d(T).
- `logarithmicGridDistance_le_node (T:=T) hn`: d(T)<=|log n-T| (does NOT take hT).
- `logarithmicGridDistance_pos_iff hT`: 0<d(T) iff forall n>=2,T!=log n.
- `logarithmicGridDistance_le_one hT` and `logarithmicGridDistance_le_exp_neg hT`.

`subtractCopy_near_tail_zero hfcontinuous hfc hD hsupp hsep ha hx hz`: with D>=0,T>D+1,a!=0, |x-T|<=1 and h_copy(x)=0, concludes h_f(|x-T|)=0.
`subtractCopy_infinite_grid_distance_zero`: all-grid copy zeros imply h_f(d(T))=0.
`subtractCopy_infinite_grid_center_off_grid`: additionally positive R forces d(T)>0, ruling out exact-node centers.
`subtractCopy_infinite_grid_distance_energy`: compact C² f, positive R, correlation radius D>=0, T>D+1,T>=2,a!=0, all-grid copy zeros imply d(T)>0 and E(base),E(copy)>=exp(-1/2)*(-log d(T))/4. Local copy preservation transfers the nearest zero.

`exists_smooth_polar_source_at_off_grid_center`: exists ONE C for all T>=2 off-grid; actual C∞ compact nonzero k with correlation radius <=1/2, canonical polar copy C∞ compact positive mass, exact polar moment zero, every infinite-grid zero, and exp(-1/2)*(-log d)/4<=E(g)<=C-log d. Construction fixes seed f,D,A, takes L=4(D+1)/d, rho=d/4. Since d<=1, rho<=1/4; all three packets miss grid. Uses only derived seed/compression/error estimates.
`exists_smooth_separated_polar_grid_source_iff hT`: existence of such C∞ compact positive-mass radius-half seed with all-grid canonical-copy zeros iff T is off-grid. Complete positive survivor of exact-node no-go; no general polar-class classification claimed.

Both new leaves passed direct Lean checks with no diagnostics. Scratch `/tmp/infinite_grid_distance_audit.lean` checked all 15 theorem axioms and mathlib names: only propext, Classical.choice, Quot.sound. Both imports added to field umbrella and all 15 names verified in generated LEAN_API. Logs `/tmp/infinite-grid-distance-{geometry,classification,axioms,index,lint}.log`. Failed names probe/log cleaned; final scratch retained. No owned Lean/search/index/lint process remains active.

Global lint latest run failed on four concurrent foreign unwired modules: NonTemperedShiftedZetaPairCountermodel, WeilConeMismatchWitnesses, ZeroCountRemainderNotIntegrable, OddMultiplierLeakageFamily. Neither new module has a lint error. Do not claim repository-wide green or fix unrelated research. Other agents sometimes regenerate dependency .oleans; inspect current process/file state and wait for their builds rather than restarting or killing them.

## Next conjecture / search
Move beyond two copies: finite common-seed trains, e.g. sum_{j=0}^m c_j f(u-jS), with nonzero endpoint coefficients and S>D+1. Near the maximal span mS the endpoint pair is unique; other pair differences are at least S away. Nearest-grid pinning should force h_f(d(mS))=0, and local autocorrelation should be (sum c_j²)h_f(delta). Candidate result: full-train energy grows at least linearly in total span, with exact-grid-span obstruction, independent of interior interference. Unproved/unaccounted. Do not extend this argument to unrelated packet shapes: extremal cross-correlation need not be positive origin mass. Need paper proof and source-derived endpoint before counting.

Prior corpus search `/tmp/infinite-grid-multicopy-search.txt` (hybrid query finite translated source autocorrelation sum endpoint copy) finished exit0; semantic coverage unmeasured. Useful source-only hits: `integral_finset_sum_shift_sq_eq` in MultiCosetGramPackingAndNyquistDensity.lean:207 (integral square finite translated sum = double correlation sum), `autocorr_sourceTranslate` and `autocorr_add_of_cross_zero` in FiniteSourceEnergyScalarization.lean, `translationGramEnergy`/`autocorr_gram_leverage_remainder` in MultiChainToeplitzGramCoupling.lean. Concurrent OddMultiplierLeakageFamily has private six-packet expansion; it was unwired at audit and not inspected/dependent here. Verify all APIs and inspect source before reuse.

External primary audit: Laptev–Weth https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf Lemma 2.5 confirms logarithmic scaling is classical. Contributions are connected corpus results; no exhaustive external novelty claim. The full current field README (489 lines) was reread this continuation. Serena list_memories output is enormous: NEVER print it raw; filter structured results to relevant names. Serena symbol tools reject ignored Lean files (previously verified), so use rg/read/apply_patch fallback. update_plan is unavailable; pipeline cards carry plans.
