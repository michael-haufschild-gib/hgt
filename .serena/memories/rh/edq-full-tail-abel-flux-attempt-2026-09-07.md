# EDQ direct full-tail Abel and cross-sign attempts (2026-09-07)

Goal ACTIVE/unachieved. This turn did NOT prove a new arithmetic producer bound or make substantial proof progress. No Lean files/builds/audits/index/lint, mathematical computations, subagents, commits, scratch or remote jobs. Frontier map READ ONLY, untouched; foreign changes already present preserved. Only working card appended and this memory created. Scoped card diff-check passes. Do not mark goal complete/blocked for mathematical difficulty.

Prior turn memory: `mem:rh/edq-harmonic-cutoff-selection-2026-09-07`; last new Lean theorem already fully audited: `mem:rh/edq-all-gcd-head-subpower-2026-09-07`. Do not re-audit old declarations or rerun nearby selector/budget experiments.

## Actual attempted source estimate
Read HTGeometry/CenteredModularAbel.lean and SecondCenteredModularAbel.lean through line220. Their signed orientation applies to one channel with nonnegative decreasing weights (second Abel additionally needs decreasing nonnegative first differences). The weight F(k)*w(k) for the squared signed source does not inherit those hypotheses.

Let N>=1, all d positive throughN: F(k)=sum mu(d)*(k mod d)/d; H=sum mu(d)/d; c=(M(N)-H)/2; g(k)=sum_(d|k,d<=N)mu(d); P_d(k)=rem*(rem-d)/(2d); U(k)=sum mu(d)P_d(k); w(k)=1/[k(k+1)]. Corpus primitive successor gives F=c+Delta U; residue jump gives F(k)-F(k-1)=H-g(k).

Paper finite exact formula for 1<=a<=b:
 sum_(a..b)F^2 w = c sum Fw + U(b+1)F(b)w(b)-U(a)F(a)w(a)
 +sum_(a+1..b)U(k)F(k-1)(w(k-1)-w(k))
 -H sum_(a+1..b)U(k)w(k)+sum_(a+1..b)U(k)g(k)w(k).
For fixedN all fields bounded, series absolutely converge, upperboundary vanishes. a=N+1 retains actual fulltail; no periodreplacement or changedcompensator.
Unpaid flux=sum_(d,e<=N)mu(d)mu(e)sum_(j>=1,dj>=N+2)P_e(dj)w(dj). Its d=e contribution exactlyzero because P_d(dj)=0. Allunequalpairs retain bothsigns. P_e<=0 does notsign aggregate.
Directabsolute estimate |U|<=N(N+1)/16. For d<=N,q=floor(N/d)>=1, sum_(j>q)1/[dj(dj+1)]<=1/(d^2 q)<=2/(dN). Thus |flux|<=(N+1)harmonic(N)/8 =O(NlogN), insufficient. This is an obtained upper allowance, NOT a necessary lower cost or a no-go for allAbelmethods. No new receiver was formalized; identity alone does not close source bound. Retain mean/gradient/lowerboundary costs withflux.

## Sign-return attempt
Existing EulerDeletionMobiusGramCancellation.lean:176 riemannHypothesis_of_cofinally_log_bounded_cross already shows cofinalcross<=0 wouldsuffice. This condition is STRONGER than cofinalsubpower criterion (commentary initially called target weaker; card explicitly correctscomparison). No signreturn proved.
In Re(s)>1, exact cutoff transform sum_N cross(N)/N^(s+1) =sum_(d!=e)entry(d,e)sum_(N>=max(d,e))N^(-s-1). Absoluteentrymax-shell bounded by GramCauchy/diagonalG(d,d)<=2/d; innerweightO(max^-Re(s)), yieldingabsoluteconvergence. Max-indexkernel couplesindices. No identity reducingthis tosingle1/zeta transform or realpositive-axiscontinuation was produced, so scalarLandaucontinuation cannotbeassumed. Thisattempt remainsunclosed; do not claim a conjugate-pole theorem or unconditional signlaw.

## Corpus searches/reads
Research queries mertens energy, modular abel, mobius ramanujan, harmonic energy, mobius summation, mobius gram, selberg gcd, cross landau, mertens square, stationary budget, centered modular, mobius quadratic diagonal (no-refresh).
Read FirstTailMertens.lean1-120; QuotientHarmonicBound.lean1-130; MobiusBlockDefectEnergy.lean1-140; Sieve/GrahamMeanSquare.lean1-~170; GramCancellation.lean1-33,133-189; currentcard1-165,366-448 andheadinginventory/last24; STATUS lastgeneralrules; frontier EDQ textread-only. Some broadsearchresults truncated, do notclaimall corpusread.
Graham again onlyincrementmean square, alreadyauditedwrongcarrier; no newuse. Ramanujan/CGL divisorformula names located but notread/provednewrepresentation; no theoremclaim. The mentally considered genericcoefficient taildominationcounterexample was NOT proved or recordedasresult.

## Files
Appended two sections to docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md: Direct full-tail attempt: signed modular Abel flux; Direct sign-return attempt: retained two-index transform. These are explicitly paperattempts/unpaidterms, not formaltheorems or route retirement. No new route-independent STATUS entry needed; existing covariance/correction rulesalreadycovergeneralconstraints. No own processes ever started, nothing to clean.