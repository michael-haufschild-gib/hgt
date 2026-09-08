# CCM-FU fixed-core profile and reserve signs (2026-09-08)

RH goal ACTIVE, not proved. Frontier map remains READ ONLY per explicit user override; do not edit/revert it even if goal text says update. Shared worktree/umbrellas contain other agents' changes. No subagents, commits, or pushes. No STATUS change: these findings are route-specific.

## Completed new source theory
New `formal/GaloisForLFunctions/RHTower/MobiusDivisorFixedCoreProfile.lean` (~379 lines), wired into RHTower umbrella. Eight public theorems:
- `mobiusDivisorSelectionFibre_product_interpolation`: for any processed P and remaining prime label R disjoint from P, r=prod R, F_P(M,R)=mu(r)*sqrt(r)*I_P(M,r), all M. I is exact adjacent-child-head square-root interpolation, with SAME processed P at both child cutoffs.
- `mobiusDivisorSelectionEnergy_eq_processedHead_scales`: full Q_P=sum_activeR r*I_P(M,r)^2.
- `mobiusDivisorSelectionEnergy_eq_squarefree_processedHead`: reindex the complete energy by all squarefree r<M with primeFactors(r) disjoint P. No coordinate omitted.
- `mobiusDivisorSelectionHead_eq_sum_divisors`: for finite prime P, D=prod P, M>=D, actual head H_P(M)=sum_(d|D) mu(d) K_d(M).
- `tendsto_divisorUnsignedDilationChannel_div_sqrt`: fixed positive d has K_d(M)/sqrt M -> c=log(2pi)/2-gamma-1/4, from existing uniform quotient-tail unsigned mean.
- `tendsto_mobiusDivisorSelectionHead_div_sqrt_zero`: every nonempty fixed prime P has H_P(M)/sqrt M ->0, using sum_(d|D)mu(d)=0.
- `exists_mobiusDivisorSelectionFibre_uniform_head_tail`: for each fixed nonempty prime P and epsilon>0, one T>=1 makes |F_P(M,R)|<=epsilon sqrt M simultaneously for every M and every remaining prime label R with floor(M/prodR)>=T.
- `exists_mobiusDivisorSelectionEnergy_quotient_tail_bound`: total energy of ALL active labels with floor(M/prodR)>=T is <=epsilon^2 M^2 for every M. Uses at most M-1 active labels. T depends on P,epsilon; NO uniformity through changing P.

Paper proof/current limits: `docs/drafts/pipeline/3-formalized/ccm-fu-fixed-core-profile.md`. Stage1 target: `docs/drafts/pipeline/1-in-progress/ccm-fu-fixed-core-reserve-sign.md`.

Validation: exact scratch checks passed, exact leaf emitted by lake env lean FILE -o leaf.olean (session34724 exit0). One external axiom audit of ONLY the eight new declarations (94659 exit0): each only propext, Classical.choice, Quot.sound. Lint17989 exit0 with existing large-file warnings. No umbrella/full build. Known Lake packaging audit remains pending; do NOT repeat expensive stale prerequisite rebuild/preflight. No additional Lean/audit reruns needed for unchanged file.

## Completed surprise-directed RunPod experiment
Frozen protocol in stage1 card above. All64 processed subsets of S={2,3,5,7,11,13}, 192 edges at every M=2^k,k9..18. r=(Q_P-Q_(P+q))/M^2. Persistent diagnostic r<-1e-8 at final3 cutoffs (65536,131072,262144). Reported parent Q_P<=B separately (NOT full successor-envelope admission). Fixed pool S NOT all available primes.

91 persistent negative-release edges, all91 parents below B at final3. 14 parents have every remaining q IN S increasing energy at final3; P={2,3} one example, Q_P/B~.143. Strongest preselected audited edge P={3,5,11,13},q7,M262144: normalized release -0.000121032242614168227602673897659683038998776056719233..., nonempty contribution -0.000121031730601652385572037544813697296193981298848094.... Parent Q/B~.34773. Full80digit source reconstruction independently computed tau andmu using prime exponents, same already-proved clipped identity. Float normalized energy discrepancies <6.3e-18. Other91-edge float results NOT individually high-precision audited.

Main eight-worker screen0.409s; TOTAL6.565s incl80digit audit, one60sec foreground deadline, exit0. All computations ran only authorized RunPod root@157.157.221.29:27094 using ~/.ssh/id_ed25519. Downloaded script, summary.json (full states/edges), stdout.log, README,SHA256SUMS in `docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-fixed-core-reserve-2026-09-08/`. Remote/local hashes matched and local SHA256SUMS verified. Remote directory /tmp/ccm-fu-fixed-core.n6DbAToo and all owned files removed after no-worker process check. No live remote job. DO NOT repeat/enlarge this screen.

No eventual sign, all-prime rejection, admissible-completion failure, or RH consequence follows from finite evidence. Reserve need not be assumed positive after every fixed-core merger. No route retired.

## Exact next obstacle and possible implementation
New profile/tail theorems supply source reduction/tightness for fixed-core quadratic energy coefficient. Remaining actual proof: squarefree density coprime to arbitrary finite prime P, weighted Riemann limit, then actual signed correlations and reserve renewal through changing P.

Proposed analytic formula NOT PROVED: continuously interpolate H_P to G_P on square-root clock, G=0 below1. rho_P=(6/pi^2)*prod_(p in P)p/(p+1). kappa_P=lim Q_P/M^2=rho_P*integral_1^infty G_P(x)^2/x^3 dx. Exact head update should give G_(P+q)(x)=G_P(x)-sqrt(q)G_P(x/q). With density factor q/(q+1), diagonal terms cancel and release coefficient is 2*rho_P*q*sqrt(q)/(q+1)*integral G_P(x)G_P(x/q)/x^3 dx. These integration/density steps and sign remain open. Do not claim this formula formally established.

Useful next simplification: for each bounded quotient block n=floor(M/r), sqrt(r)*I_P(M,r)=a_n sqrt M+b_n sqrt r, with a_n=(H_P(n+1)-H_P(n))/(sqrt(n+1)-sqrt n), b_n=H_P(n)-a_n sqrt n. Thus bounded-depth energy needs squarefree coprime density moments of 1,sqrt r,r. The new uniform energy tail handles unbounded quotient depth. This may avoid building a general weighted Riemann theorem.

Corpus sources read: RetainedPrimeTopHomothety, RetainedPrimeCoordinateHomothety (different fixed RETAINED semantics), RetainedPrimeSupportThreshold, MobiusDivisorPrimeFibreInterpolation, DivisorUnsignedChannelExactMean. Sieve/CoprimeSquarefreeDyadic and Window only handle one excluded prime. Sieve/CoprimeCounting has exact arbitrary-modulus count= sum_(d|e)mu(d)floor(z/d), but not squarefree condition. Sieve/SquarefreeCount has truncated moebius count and density6/pi^2. Sieve/LogSumFromCount handles log weights; general power moments not located. Sieve/SquarefreeDivisorProduct has divisor/subset bijection but imports Mathlib umbrella; avoided unnecessary dependency in new leaf.

Lean gotchas: opening Filter introduces Filter.mem_sdiff shadow even with reordered opens; qualify Finset.mem_sdiff. Need open scoped Topology for nhds notation. Current name tendsto_finsetSum (old snake name deprecated). abs triangle is abs_add_le, not abs_add. Let r=prodR needs `change ... M/r at hquot` before omega. Use root shell cwd for edits/search formal/paths; Lean cwd formal for lake commands. Track/clean exact /tmp paths with Python unlink, not rm.
