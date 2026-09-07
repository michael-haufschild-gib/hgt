# EDQ complete period covariance and a quantified averaging obstruction

RH/EDQ goal remains ACTIVE, NOT achieved. This turn made verified progress: two new audited Lean leaves, exact source covariance/weighted-trace identities, and a false period-average ceiling retired only after formalizing its strongest positive survivor. No unconditional RH proof/falsification, no off-line zero assertion. Previous relevant memory: `mem:rh/edq-mobius-global-log-saving-2026-09-07`.

## Full chain and remaining gate
Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. Actual literal Möbius current / signed cross sum still needs a cofinal polynomial-log upper ceiling with actual chronological/progression weights retained. Prior unconditional actual full-source energy and absolute-cross savings are o(N/log^q N) for every fixed q; prior hypothetical off-line lower escape is beyond every log power. Neither proves the missing ceiling. This turn proves that replacing those weights by uniform complete-period averaging is quantitatively invalid as a comparable energy replacement, and its proposed log ceiling is FALSE unconditionally. EDQ itself stays live.

## Completed leaf 1: exact covariance and weighted trace
`formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusPeriodCovariance.lean`,420lines,namespace `RHTower.DeletionPeriodCovariance`; imports EulerDeletionCoprimeWordPeriodicity and EulerDeletionMobiusGlobalLogSaving. Five definitions,14public theorems (19new declarations total), set_option autoImplicit false. Wired into RHTower.lean.
Card: `docs/drafts/pipeline/3-formalized/edq-complete-period-covariance.md`, moved out of1-in-progress.

Definitions: centeredResidue m k=(k mod m)−(m−1)/2; residueCombination S u k=Σm∈S u(m)*(k mod m)/m; periodMean S u=Σu(m)*(m−1)/(2m); periodCovariance S u=(1/12)Σm,n∈S u(m)u(n)*(gcd(m,n)^2−1)/(mn); periodWeight P r=Σ'j≥0 1/((r+Pj)(r+Pj+1)), zero-index summand0, nonzero multiples in zero residue RETAINED.

Exact finite CRT argument: m=g*a,n=g*b with coprimea,b. At k=g*j+i,0≤i<g, centered residues=g*c_a(j)+c_g(i),g*c_b(j)+c_g(i). Coprime-period product factorization kills both zero-mean coordinates; surviving sum=abΣi c_g(i)^2=gab(g²−1)/12. Repetition gives EVERY common periodP: Σk<P c_m(k)c_n(k)=P*(gcd²−1)/12. Source full period mean and square moment follow with EVERY signed pair retained. Literal Möbius mean=(M_N−H_N)/2; uncentered moment=P*(mean²+variance). Covariance nonnegative from actual centered squares.

Generic bounded periodic stepGram reindexed by Nat.sumByResidueClasses yields exact full weighted trace. Literal raw norm²=Σr:ZModP norm(primitive N r.val)²*periodWeight P r.val. No uniform averaging replacement. Both moment and norm formulas have unconditional factorial-period specializations for everyN, includingN0.

Public names: centeredResidue, centeredResidue_periodic, sum_centeredResidue, sum_centeredResidue_sq, sum_centeredResidue_mul, sum_centeredResidue_common_period, residueCombination, periodMean, periodCovariance, sum_residueCombination, sum_residueCombination_centered_sq, sum_residueCombination_sq, periodCovariance_nonneg, mobius_periodMean, mobius_primitive_period_energy, periodWeight, mobius_modular_norm_sq_eq_weighted_period, mobius_primitive_factorial_energy, mobius_modular_norm_sq_eq_factorial_period.

## Completed leaf 2: positive projection, large uniform variance, weighted separation
`formal/GaloisForLFunctions/RHTower/EulerDeletionPeriodAveragingObstruction.lean`,283lines,namespace `RHTower.DeletionPeriodGrowth`; imports above leaf, PrimeCountShell, Sieve.ShortIntervalThetaEveryWindow. Four definitions,11public theorems (15newdeclarations). Wired intoRHTower.lean.
Failed shortcut card WITH exact formal positive survivor: `docs/drafts/pipeline/5-failed/edq-period-average-growth-obstruction.md`, moved out of1-in-progress.

Definitions: varianceN=periodCovariance(Icc1N)µ; upperPrimesN={p prime:1≤p≤N,N<2p}; remainingVariance masks ONLY those prime coefficients to0; periodAverageN=(Σk<N! norm(primitiveNk)²)/N!.
Every p in upperPrimes is coprime to every other m≤N, since distinct positive multiples exceedN. Full centered covariance therefore makes that channel orthogonal to EVERY other channel. Exact positive survivor:
V_N=Σp∈upperPrimes (p²−1)/(12p²)+V_remaining, V_remaining≥0.
Each prime diagonal≥1/16, so #upperPrimes/16≤V_N for EVERY cutoff, nozero/asymptotic premise.

Actual corpus window theorem `Sieve.exists_theta_window_lower` atα3/4, y=N/2,L=N/2, plus eventual N^(3/4)≤N/4 gives theta(N)−theta(N/2)≥N/32768. `primeShellCard_bounds` gives #upperPrimes≥N/(32768logN). Hence V_N≥N/(524288logN) eventually. V_N/log^qN→+∞ for EVERYq, UNCONDITIONALLY. No cofinal polynomial-log upper returns of V_N or actual uncentered periodAverageN. This is a genuine false replacement ceiling, not an RH receiver.

The actual raw norm²/varianceN→0 and raw norm²/periodAverageN→0, using prior unconditional full raw energy log-saving atq1 and the exact positive denominators eventually. This is quantitative scale separation for the SAME deterministic arithmetic source. Uniform-period covariance and actual weighted Gram are not uniformly comparable inN. A mere upper bound by the much larger uniform average cannot deliver the requested log ceiling.

Public lines:
21variance;24upperPrimes;28remainingVariance;40remainingVariance_nonneg;49variance_eq_upperPrime_diagonal_add_remaining;98upperPrime_card_le_variance;146variance_eventually_lower;173periodAverage;177periodAverage_eq;186variance_le_periodAverage;217variance_div_log_pow_tendsto;230not_cofinally_log_bounded_variance;242not_cofinally_log_bounded_periodAverage;272modular_norm_sq_div_variance_tendsto_zero;277modular_norm_sq_div_periodAverage_tendsto_zero.

## Validation DONE — do not repeat old checks
First complete scratch session83592 exit0EMPTYdiagnostics. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance` session53625 exit0,ONLYnewleaf compiled7.6s (13110graphjobs otherwisecached). First new-only axiom session12172 exit0: all19public declarations exactlypropext,Classical.choice,Quot.sound.
Second complete scratch session59771 exit0EMPTYdiagnostics. Final targeted build session18005 exit0,ONLYEulerDeletionPeriodAveragingObstruction compiled9.3s (13613graphjobs otherwisecached). Second new-only axioms session57344 exit0: all15 exactlysame3standardaxioms. No added axioms/admissions/numerical certificates. Private helper closure covered by these public audits. No full/umbrella builds.
ONE repository lint session9605 exit1 ONLY unrelated concurrent unwired module `GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation`; no newEDQlint error. Do not claim globalpass or rebuild/modify that foreign module. Last turn's3unwired CCMmodules now wired by their owner.
ONE index refresh session1592 exit0:8changed,0removed,33079files,403643decls,3951gapmarkers.
Scoped git diff whitespace plus explicit untracked-new-source whitespace, both umbrella importsunique, all34new audit entries covered, exact standardaxiomsets, no forbiddendeclarations, newdoc links/stages validated. Bothcards final no pending markers. Owned Lean processes ALLterminal; exactpsargs scan noowned Lean/lake commands. All6scratchLeanfiles removed: `/tmp/edq_period{,_api,_axioms}.lean` and `/tmp/edq_period_growth{,_api,_axioms}.lean`. Logs retained under `/tmp/edq_period.*.log` and `/tmp/edq_period_growth.*.log` (final build/check/axioms/lint/index +oldAPI diagnostic).

## Documentation updated
Frontier current-topology EDQsentence, two detail paragraphs afterglobal-log-saving paragraph, EDQtable currentresults, and new terminal table row `EDQ uniform period-average logarithmic ceiling`. No newroute labels/count changes. Actual weighted ceiling remains explicitlyopen. STATUS appended route-independent `MUST-RETAIN-THE-WEIGHTS-AFTER-AVERAGING`: compare weighted anduniform cycle energy quantitatively, retain growingperiod/nonconstantweights, orthogonalreservoirsigns cannotcancel uniformvariance. Bothcards record actual global lintfailure, notpass.

## Efficient Lean lessons
- Function.Periodic.nat_mul onNat creates a Nat-to-Nat cast; `simp only [Nat.cast_id, Nat.mul_comm]` needed.
- For periodic lambdas, `dsimp only` afterintro before `rw[hperiod...]` to expose application. Omega similarly needs explicit change of lambda application equalities.
- `tsum_mul_left` is usable without arguments in expectedtypedgoal; letfunctiong often needs`dsimp only[g]` rather thanrw[g].
- ZModP finite sums require `haveI :NeZeroP:=⟨hP.ne'⟩` IN statement whenPpositivehyp supplied. Factorial also neededexplicitNeZeroinstatement using(Nat.factorial_posN).ne'.
- After rewriting bdMobiusModularApproximantVec in inner-self identity, derive `have hGram :stepGram...=norm(originalVec)² := hi` bydefinitional equality; direct rw←hi won't match the unfoldedvector representation.
- `tendsto_rpow_neg_atTop` ROOT, notRealnamespace. For .comp limits and Pi-inverse functions, use `.congr; introN; dsimp; ring` / `change (logpow/N)⁻¹=_;rw[inv_div]`, rather than simp-only expecting function extensional normalization.
- Nat.eq_of_dvd_of_lt_two_mul firstpremise m≠0 must explicitly extract mem_Icc lower bound; omega doesn't look through membership automatically.
- field_simp often fullyclosesrational identities; avoidtrailingringNoGoals. For filtered sums use explicitsum_congr conditionalcleanup rather thanexpecting sum_ite_of_true to discharge membership.

## Next mathematical direction, not completed work
Actual weighted chronology remains decisive. Upper-half prime channels are orthogonal ONLY underuniformperiodmeasure; the actual early-time weights create cross interactions withsmaller moduli. Finite divisor inversion already forces strong early-prefix cancellation despite thelargeperiodreservoir. Seek a source estimate for the exact nonconstant W_P(r) pairing or sourcechronologicaltail; do not reuseuniformperiodvariance as apolylogproducer, invent a uniform period/weight comparison, or drop zero-residueprogression tails. The new covariance law may support exact weighted projection/deviation identities, but those estimates are NOTprovedhere. No experiment wasrun: allstatements followedpredictedpaperderivations. Any future numerical experiment must follow`docs/meta/scientific-method.md`, have uncertain discriminating outcomes relevant to thehardgap, runONLYRunPodssh root@157.157.221.29 -p27094 -i~/.ssh/id_ed25519 withmulticoreoptimizedcode, boundedruntime, resultsdownloaded/documented underdocs/drafts/pipeline/2-fully-proven/computations. No hourslong/predictablecomputations, no numericalresults inLean.
