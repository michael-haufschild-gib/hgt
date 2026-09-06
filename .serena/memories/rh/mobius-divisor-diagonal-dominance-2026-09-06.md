# Actual source diagonal dominance: open all-scale sign

RH/all-scale producer is NOT proved. Goal remains paused; no status change.

Card: docs/drafts/pipeline/1-in-progress/mobius-divisor-source-diagonal-dominance.md.
Report/data: docs/drafts/pipeline/2-fully-proven/computations/mobius-divisor-diagonal-dominance-2026-09-06/REPORT.md.
Remote directory: /root/rh-mobius-divisor-diagonal-20260906 on authorized Runpod. Prior input /root/rh-mobius-divisor-coordination-20260906/source.npz; source archive now downloaded into its corresponding previous computation folder locally.

Frozen [BRIDGE] SD1: for literal D(q)=log(q!)-sum tau+2 gamma q and C_d(M)=mu(d) sum_(k=d)^(M-1) Delta sqrt(k) D(floor(k/d)), ask (sum_d C_d)^2 <=sum_d C_d^2 for every integer M>=1. No constant adjustment, no initial range removed. This remains unproved. Do not claim a random-sign ensemble proves the actual source.

Exhaustive O(N log N) coefficient-jump/hyperbola scan through N=2^21 (all integer endpoints) takes3.30sec,8 workers,BLAS1. No apparent SD1 violations. M1 empty,M2exact equality. Largest other ratio M17=0.77306365027833565955096010855. Ten largest ratios independently recomputed using trial-factor mu, exact integer divisor sums, original double sum at60/100digits, agreeing >50digits. All80 earlier independently computed normalized diagonals agree <8.52e-15. Full vectors41MB retained all-endpoints.npz. Finite float data is NOT interval/all-scale proof.

Last complete band[1048576,2097151] max ratio .060688530032 at1865411; band[65536,131071] max .028907935809 at128969. Thus late maxima can rise. Last bandQ/M² spans .00118438105246..00118463653069. No asymptotic claimed.

Independent stronger [BRIDGE] SD2: E=Q-S² nondecreasing at EVERY integer M>=1. Numerically rejected firstM4->5, delta=-.0131233065660142069109224977293672924 (60/100digit audit). Q drops~.00606238226050 while S² rises~.00706092430552. 21863 recorded decreases, largest absolute atM1851018: direct update~-1026.24311118; Q rises4360.32741074 but S² rises5386.57052192. No damped monotonicity was substituted. This rejects the monotonicity producer only, NOT SD1 or any whole RH route. Counterexample itself is numerical, not Lean-closed.

Positive residue formalized, file formal/GaloisForLFunctions/RHTower/MobiusDivisorAbelDiagonalBound.lean, imported into RHTower umbrella:
- sqrt_mul_abs_mobiusDivisorDilationChannel_le: sqrt(d)|C_d(M)|<=12M for d>=1.
- sum_mobiusDivisorDilationChannel_sq_le_harmonic: ALL M, Q(M)<=144M² sum_(d<=M)1/d.
- mobiusDivisorDilationChannel_succ_of_le: C_d(M+1)=C_d(M)+w mu(d)D(M/d), existing d<=M.
- sum_mobiusDivisorDilationChannel_sq_succ_sub: ALL M, Q(M+1)-Q(M)=2w sum C_d v_d+w²sum v_d².
All source checks and named leaf lake build audits pass. No umbrella/full build; required dependencies only. LEAN_NUM_THREADS=1 for lake final audit. #print axioms from /tmp shows ONLY propext,Classical.choice,Quot.sound for all4. No numerical evidence/native certificates used. index and lint --check-generated PASS with existing size warnings. Own Lean/remote computation sessions completed.

Important mathematical boundary: diagonal bound is elementary supporting infrastructure, not significant solution of cross-term problem. SD1 + harmonic diagonal yields S/M=O(sqrt(log M)); an explicit formal continuation bridge permitting this subpower loss is NOT yet wired. Do not silently feed it into existing exact uniform-boundedness iffRH criterion. Potential diagonal improvement by averaging D BEFORE abs/squaring not proved. Gcd reindex mu(br)mu(ar)=mu(ab)mu(r)^2 leaves signed orientations. Negative two-prime renewal determinant is after collapse to exp(-ax), not inverse-source norm. Searches over Selberg source, renewal contraction, gcd/additive correlations and sawtooth integration supplied no new all-scale cross sign.

Frontier ledger CCM-FU numerical paragraph updated current-state with this candidate/formal scope. Universal STATUS untouched because no new route-independent RH law was proved. No commits/pushes by this agent.