# CCM-FU: changing-core physical renewal, pair costs and even-core reserves CLOSED

Active unbudgeted goal remains unconditional formal proof/falsification of RH via CCM-FU. NOT achieved and NOT blocked. This goal turn is PROGRESS: 4 new checked leaves, 15 public theorems, source-derived even-core pair reserves and actual finite-cutoff transfer. Full chain: actual divisor source -> renewable signed reserve -> exhaustive selection -> uniform signed Abel bound -> RH. Previous goal turn also progress (discrete/physical release bridge).

## User constraints and shared-worktree discipline
- Frontier docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md READ ONLY, explicit override persists despite replayed goal instruction to update. Never edited it. STATUS unchanged, no new route-independent fact. Both had outside modifications already at turn start; preserve.
- No subagents, commits, pushes, numerical experiments, full/umbrella/large builds. One owned foreground Lean process at a time. No old prerequisite olean rebuilt or old axiom closure re-audited. Standard propext, Classical.choice, Quot.sound only.
- Known lake build packaging audit remains pending due broad stale prerequisite rebuild. Do not rerun a broad preflight/rebuild just for packaging. Exact-file verification separately recorded.
- Numerical experiments only prescribed RunPod, truly unpredictable/scientific method/short/multicore/download/document/cleanup. None needed or run here.
- No update_plan tool available; no special skill used. Serena prior manual read, relevant memories read. Architecture/testing docs absent. No live processes or tool sessions now.

## New checked Lean leaves
Paths prefix formal/GaloisForLFunctions/RHTower/.

1. MobiusDivisorDilationMeanRenewal.lean (about140 lines), TWO public theorems:
- mobiusDivisorContinuousHead_insert (line18): for P prime core, p prime outside, ALL real x,
  G_(P+p)(x)=G_P(x)-sqrt(p)G_P(x/p).
  Proof: source divisors indexed by subsets via Sieve.sum_divisors_prod_primes_eq; sum_powerset_insert; prime-Mobius multiplicativity; no threshold or sign premise.
- mobiusDivisorDilationMean_insert (line92): ALL positive Y,
  W_(P+p)(Y)=(1+1/p)W_P(Y)-sqrt(p)/p^2 W_P(pY)-sqrt(p)W_P(Y/p).
  Private pair identity: integral_(x>0) G_P(Ax)G_P(Bx)/x^3=B^2 W_P(A/B), B>0. Absolute integrability for A,B>0 proved by extending below1 (head zero) and dilation. Expand four terms, retain both cross scales and double copy.
  Final scratch99854 exit0; exact emission40503 exit0.

2. MobiusDivisorDilationMeanUniformRenewal.lean (about207 lines), FIVE public theorems:
- exists_bound_mobiusDivisorDilationMean line29: for fixed nonempty prime core P, exists B>=0, all Y>=1, |W_P(Y)|<=B. Bound from actual residue plus L1 entire-boundary norm, no guessed convergence rate.
- exists_bound_mobiusDivisorDilationMean_insert_ratio line51: exists C>=0, ALL primes p outside P, ALL Y>=1,
  |W_(P+p)(Y)+sqrt(p)W_P(Y/p)|<=C.
  Choose C=3B. Uniform in BOTH growing inserted prime and entire next dilation ray, original P fixed.
- continuousOn_mobiusDivisorDilationMean line118: actual W continuous on positive reals. Central contour = exp(a)/(2pi) times oscillatory Fourier integral; dominated convergence with norm-one phase; log composition.
- mobiusDivisorDilationMean_one_pos line132: W_P(1)>0 for every prime core, including empty. If integral G^2/x^3=0, G=0 ae on>1, contradict existing positive signed inverse-cube moment. No nonzero-head premise.
- exists_mobiusDivisorDilationMean_insert_negative_band line163: for nonempty P, exists eta,c>0,T, all sufficiently large primes p outside P, ALL p<=Y<=(1+eta)p:
  W_(P+p)(Y)<=-c sqrt(p).
  Continuity at ratio1 and W1>0 supply positive margin; absorb uniform C with sqrt(p)*margin. This is a joint two-scale law, not a separate fixed-core distant limit.
  Final scratch60241 exit0; exact emission40671 exit0.

3. MobiusDivisorComparablePrimeCost.lean (about250 lines), FOUR public theorems:
- exists_mobiusDivisorComparablePrime_second_cost line64: nonempty prime core P, exists eta,c>0,T; all distinct unprocessed primes p<=q<=(1+eta)p, p>=T:
  kappa_(P+p+q)-kappa_(P+p)>=c/p.
  Exact release =2rho_(P+p+q)*sqrt(q)/q^2*W_(P+p)(q). New negative band; rho_(P+p+q)>=rhoP/4. At q<=2p, sqrt(p)sqrt(q)/q^2>=1/(4p).
- exists_mobiusDivisorComparablePrime_pair_cost line126: same shape with adjusted constants, NET kappa_(P+p+q)-kappa_P>=c/p.
  Whole first release bounded above by A sqrt(p)/p^2, A=2rhoP*B_P, and large p makes it less than half second cost. No first-step term omitted.
- exists_arbitrarily_large_mobiusDivisorPrime_pair_cost line183: exists c>0, forall N exists primes p<q, p>=N, both outsideP, net cost>=c/p. Source-independent corpus prime_between ensures q in actual ratio band (not a computed prime).
- exists_arbitrarily_large_mobiusDivisorPrime_pair_energy_cost line216: such arbitrary-large pairs have ACTUAL Q_(P+p+q)(M)-Q_P(M)>=c*M^2/p for every sufficiently large integer M, with adjusted c. Subtract existing energy limits and take half strict margin. M threshold depends on pair and P!
  Final scratch79203 exit0; exact emission13147 exit0.

4. MobiusDivisorEvenCorePrimeReserve.lean (about281 lines), FOUR public theorems, constructive branch:
- exists_mobiusDivisorEvenCore_positive_ratio_ray line23: nonempty even prime core P, exists L>=1,c>0,T; all prime p outsideP with p>=T and ALL Y>=Lp:
  W_(P+p)(Y)>=c sqrt(p).
  Actual residue negative by previous source orientation and Even.neg_one_pow. Actual W limit gives W_P(lambda)<=-2c for all lambda>=L. Uniform renewal error supplies result. No analytic sign/reserve premise.
- exists_mobiusDivisorEvenCore_pair_reserve line105: even nonempty P, exists L>=1,c>0,T; all distinct primes p,q outsideP, p>=T, Lp<=q<=(L+1)p:
  kappa_P-kappa_(P+p+q)>=c/p.
  Positive wave, density lower rhoP/4, sqrt(p)sqrt(q)/q^2>=1/((L+1)^2*p) yield second release d/p, d=rhoP*c/(2(L+1)^2). First possible increase <=A sqrt(p)/p^2. Choose p large and pay full first increase to retain half second release.
- exists_arbitrarily_large_mobiusDivisorEvenCore_pair_reserve line206: exists c>0, every N admits p<q >=N outsideP with net reserve>=c/p AND Even(card(P+p+q)). Apply prime_between at x=Lp with epsilon=1/L. Thresholds avoid P.sup id. Parity preserves applicability of same source theorem to enlarged core.
- exists_arbitrarily_large_mobiusDivisorEvenCore_pair_energy_reserve line250: same selected pairs/parity with actual Q_P(M)-Q_(P+p+q)(M)>=c*M^2/p at every sufficiently large M for pair, adjusted c.
  Final scratch55664 exit0 (one stylistic warning then removed); exact emission15458 exit0 no warnings.

## Validation and cleanup COMPLETE
- All FIFTEEN public theorems audited ONCE in external /tmp scratch, audit30371 exit0. Every closure exactly propext, Classical.choice, Quot.sound. No old closure rechecked.
- All4 imports wired in RHTower.lean after MobiusDivisorPrimeCorrelationPhysical. No umbrella build.
- Global formal lint8078 exit0, unrelated existing large-file warnings only. Index91447 exit0, scoped diff--check passed.
- New4 source leaves retained untracked, no commit. Ole ans retained. No old cache prerequisites rebuilt this turn.
- All10 owned temp files REMOVED with exact paths: ccm_core_renewal_api.lean, ccm_core_renewal.lean, ccm_core_renewal_uniform.lean, ccm_core_band_api.lean, ccm_comparable_prime_cost.lean, ccm_comparable_api.lean, ccm_even_core_reserve.lean, ccm_core_renewal_audit.lean, ccm_core_renewal_lint.log, ccm_core_renewal_index.log (all under/tmp).
- Final ps scan (lake env lean|/lean |lake build) exit1, no matches. No owned tool sessions live. No remote process ever launched.

## Documentation
- New stage3 docs/drafts/pipeline/3-formalized/ccm-fu-changing-core-pair-reserves.md: full dependency-closed paper proof for all15 theorems, validation, complete precise remaining global gap. Comparable-cost obstruction's positive survivor is exact uniform ratio profile AND constructive even-core pair reserve. No route retired.
- New stage1 ccm-fu-changing-core-dilation-renewal.md: closed source laws and even-core branch, open global propagation.
- Updated stage1 ccm-fu-fixed-core-prime-correlation.md and ccm-fu-exact-successor-extension.md with exact current scope.
- Updated stage3 ccm-fu-discrete-physical-prime-release.md with new source bridge/current remaining global gap.
- Frontier READ ONLY, untouched. STATUS untouched. Generated LEAN_API/LEAN_GAPS/LEAN_OVERVIEW refreshed by index.

## Next HARD obstacle (do not repeat closed work)
We now have an actual source-derived pair reserve for EVERY EVEN NONEMPTY CORE, with parity preserved. This is stronger positive progress than only a sign limit. But:
1. Selecting arbitrary large pairs does NOT include a prescribed omitted small prime. Need forced-prime payment or another exhaustive selection construction.
2. Each new core changes B_P, L_P, c_P and threshold. A separately chosen eventual physical M for each pair does not give one bound for every cutoff or even every prefix at its own normalization.
3. Even-core first prime can INCREASE kappa and actual Q; the second repays it only at pair endpoint. Need pay intermediate overshoot from a proved common reserve. Available proof bounds entire first coefficient cost <=2rhoP*B_P*p^-3/2, so choosing far enough makes that overhead small, but no every-cutoff schedule follows.
4. Exact successor envelope Psi is maximum of Q_P and ALL immediate successor energies, NOT geometric Phi=Q+2sqrt(GD). Pair endpoint Q bounds do not bound Psi or guarantee its reserve.
5. Comparable primes cost c_P/p whereas separated ratio windows for even cores release c_P/p. Reserve propagation must retain ACTUAL ratio profile W_P(q/p), not try to pair independent distant-prime residue credits (first is only O(p^-3/2)).
6. Need initial even nonempty core under original budget if constructing path from empty; new theorem excludes empty and doesn't assume/build initial path.
Full RH receiver requires |S(M)|<=C*M for ALL integer M, with S literal square-root Abel psi-defect sum. No new experiment planned; do not run predictable convergence or repeat saved enumeration. Do not replace global task with another fixed-core limit, generic receiver, or unrelated no-go. Goal remains active.

## Lean/API lessons from this turn
- Uniform continuous head insertion: Sieve.sum_divisors_prod_primes_eq (namespace RHTower.Sieve) + Finset.sum_powerset_insert hpNotMem. Nat.Coprime.prod_right then prime_dvd_prime_iff_eq handles new-prime product. This source proof passed on first run.
- IntegrableOn.of_forall_sdiff_eq_zero extends positive-ray kernels from>1 to>0 using head zero. Explicit IntegrableOn.congr_fun is needed when hi inferred as Integrable; field .congr_fun can mistakenly resolve And.
- integral_comp_mul_left_Ioi sometimes needs the full explicit kernel lambda, cannot infer under nested A/B*(B*x).
- integral_sub creates Pi.sub applications; simplify Pi.sub_apply at local integral identity before rw. Rewriting literal subtraction directly from expression with unapplied Pi.sub can fail syntactically.
- continuous_of_dominated (MeasureTheory): all parameters measurable, pointwise ae norm majorant, Integrable majorant, ae pointwise continuity. Pure-imaginary exponential norm is1 via norm_mul,Complex.norm_exp,simp.
- Continuous.comp_continuousOn + Real.continuousOn_log.mono with positive->nonzero.
- Metric.eventually_nhds_iff gives eps>0 and implicit y: dist y x<eps ->predicate. ContinuousAt reducible to Tendsto, so hc.eventually works although #check ContinuousAt.eventually is unknown.
- eventually_lt_nhds h:a<b is neighborhood OF a with variable<b; eventually_gt_nhds h:b<a is neighborhood OF a with b<variable. Don't reverse them.
- Parser hazards: `0<mobius...` or `0≤mobius...` parses <m/≤m matroid notation! Always spaces before identifiers. `max T (x)^2` parses (max T x)^2: write max T ((x)^2).
- Explicit `Finset.le_sup (f := id) h` needed for bound on members by P.sup id.
- prime_between is ROOT theorem from GaloisForLFunctions/PNTPlus/Consequences.lean:1450, already transitively imported; positive epsilon ->eventually for realx exists prime x<p<(1+eps)x. Nat.exists_infinite_primes n -> exists p,n<=p and Prime p.
- nlinarith does not normalize arbitrary signed products around division. For rearranging complete inequalities use convert! neg_le_neg h using1 <;>ring; use field_simp for differently factored denominators. Simplify c*sqrtp*sqrtp using mul_assoc,<-pow_two,Real.sq_sqrt BEFORE multiplying inequalities.
- Previous completed memories: mem:ccm_fu_discrete_physical_prime_release_2026_09_08; mem:ccm_fu_source_residue_orientation_2026_09_08; mem:ccm_fu_physical_dilation_mean_limit_2026_09_08; mem:ccm_fu_literal_mellin_contour_limit_2026_09_08. Closed work, no repeated audits.
