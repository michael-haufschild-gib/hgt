Completed DR/PBM shared application batch. Authoritative ledger docs/reports/rh-current-frontier-map.md; all39 routes/candidates remain scope, no Weil priority. Overall goal ACTIVE, never mark complete for this batch. Audit tmp/hgt-openai-math/dr-pbm-audits.json complete; source pointer dr-pbm-upstream-source.json. Upstream main checked unchanged fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Proven TraceCone FiniteIdeal/IdealTransport reused through PaperCompactIdealTrace; BRIDGE, no novelty claim.

Four new leaves, 46 theorems +11 defs +1 abbrev =58 public:
RHTower/PaperPrimePowerDefect
HTGeometry/PaperDiagonalCluster
RHTower/PaperPrimeRegularizedIdeal
RHTower/PaperPrimePowerIdealChannels.

Native source RegularizedLogZetaAbscissa is namespace RHTower (not GaloisForLFunctions.RHTower). Its shifted n+1 coefficients:
logZetaRegCoeff=(Lambda(n+1)-1)/log(n+1);
primeRegCoeff=1_prime(n+1)-1/log(n+1);
difference logPrimePowerDefect.
Proved literal defect in [0,1/2], equals 1/(k+2) at p^(k+2)-1 for every prime subtype p and natural k. Raw normalized Lambda coefficient in [0,1]. paperPrimePowerIndex k n=(Nat.nth Nat.Prime n)^(k+1)-1 tends to infinity. Common paperPrimePoleCoeff=1/log(n+1) tends zero. Native logarithmic row tends 1/(k+1) along layer k; prime row tends if k=0 then1 else0.

Generic reusable PaperDiagonalCluster:
paperDiagonalCluster_le_norm_sub_compact v hC hb j hj hv K gives ||L||<=||lpDiagonalCLM v hC hb-K|| for any bounded diagonal and escaping coordinate sequence j with v(j n)->L, arbitrary compact K. paperDiagonalCluster_le_compactIdealDistance counterpart.
paperCompactIdealDistance_add_compact/sub_compact preserve exact quotient norm on lp(N,C)2.
Uses compact kills weakly-null coordinate subsequence; nondiagonal compact corrections included.

Native PaperPrimeCoefficientSpace=lp(N,C)2. Raw Lambda/log and prime-indicator operators minus SAME compact pole operator are literal regularized row multipliers, coordinate equations proved. Each regularized row has essential norm1 and infinite paper ideal cost. Full difference has operator norm AND essential norm exactly1/2, witnessed by escaping prime squares. Infinite paper trace cost unchanged by arbitrary compact addition. paperPrimeRegularized_abscissa_and_operator_gap bundles existing equivalence of DR/PBM RH convergence receivers with positive exact quotient gap. No RH hypothesis/new axiom.

All-layer channels are actual coefficient restrictions indexed by all primes. Logarithmic k-th channel has compact quotient scalar1/(k+1), essential norm1/(k+1), infinite paper cost. Prime proper-power channels compact, cost0; prime exponent1 character identity/cost infinity. At proper exponent k+2, channel difference exactly (1/(k+2))*identity, not merely modulo compacts. Logarithmic channels compact-equivalent iff exponents equal; distance absolute difference of reciprocal exponents. This preserves arithmetic grading discarded by equality of convergence abscissas, but supplies no DR global roots/convergence or PBM source cancellation.

Audits: 4 object checks and final plain lake --old env lean each leaf exit0, empty logs. /tmp/paper-dr-pbm-axioms.lean audits all58 public; only propext/Classical.choice/Quot.sound. All58 exact corpus searchback matches by full module/relpath and bare declaration name. Native/deep compact searches partialfalse/errors[]. Lexical JSON names are BARE, no compiler-freshness metadata. Initial matcher expected qualified names, fixed without rerunning existing result. Both original native/bridge file hashes unchanged. All665 owned leaves wired once into ROOT theorem-area umbrellas, including nested source ports. No source-adjacent olean/ilean. All owned handles terminal. Four workspace helpers and four /tmp API probes removed; logs/JSON/axiom witness retained. Ledger DR/PBM updated lines252/336; all-route-applications and stable-coordinate-native-port latest pointers dr-pbm-audits.json.

Global lint12 FOREIGN issues: 11 unreachable modules (CCMPolarOddPrimeJumps, WeilDirichletLockRigidity, WeilDirichletLockSpectrum, WeilLockSpectralTwist, ZetaCriticalCountControl, ZetaCriticalGoodRows, ZetaCriticalPairDecomposition, ZetaCriticalRowBound, ZetaCriticalWindowStructure, HTGeometry.BoxPartitionSums, HTGeometry.QKrawtchoukCompanionTriangular) and CCMPolarOddPrimeJumps:104 sorry ccmPolarOddSource_eq_core_add_atoms. No owned lint error. Shared busy tree; preserve others' work.
Owned totals665 leaves,5407 theorem/lemma,7339 public:3809 theorem1598 lemma1697 def61 instance123 abbrev51 structure.
Remaining focused reviews16: WL,RW,FU,RP,PA,TT,LA,TH,RN,WD,LI,PM,BAG,BSH,GTA,PTR.

Lean lessons: root one_le_pow₀ (not Nat.one_le_pow₀); Nat.Prime.not_prime_pow; Nat.le_sub_of_add_le avoids omega treating normalized exponents as distinct atoms. 1/2 vs inverse2 needs simpa only[one_div]. Specify constant limit for tendsto_const_nhds.sub. For real reciprocal coerced to complex, use explicit Complex.ofReal (((k+1:Nat):Real)^-1); annotation (realExpr^-1 : Complex) can elaborate inverse in Complex and cause isDefEq heartbeat timeout. Explicit function/convergence arguments to paperConvergentDiagonal_sub_limit_compact eliminate timeout, no heartbeat changes. Unfold operator definitions in simpa to resolve overloaded instance equalities. Do not read live Lean logs. Final leaf checks no -o; objects only .lake/build/lib/lean. No full/umbrella builds or computations or commits.