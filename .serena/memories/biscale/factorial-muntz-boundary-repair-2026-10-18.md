# Actual factorial Müntz boundary: formalized progress (2026-10-18)

Active goal remains unconditional RH in Lean. RH is NOT proved. This goal turn made an unconditional actual-source contribution: 18 new public theorems and 5 definitions in three leaves, plus a necessary two-annotation repair of an existing dependency theorem.

## Exact result

Namespace: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar.
N=n+1, epsilon=sourceFactorialCollar N>0.
A_n(t)=factorialMuntzSum n t.
F_n(x)=factorialMuntzCompletion n x=exp(x/2)*A_n(exp x)/sqrt(N).
c_N=1/(2*sqrt(N))>0; K_N=25/(32*N*epsilon*sqrt(N)).

For y>=0, m=floor(y), r=y-m:
R(y)=sum_(k>=1) max(y-k,0)=(y^2-y)/2+delta(y), delta=r*(1-r)/2 in [0,1/8].
For positive epsilon,a,t:
S(epsilon,a,t)=sum_(k>=1)clampedRamp epsilon(k*t/a)
=a*(1+epsilon/2)/t-1/2+t/(a*epsilon)*(delta(a*(1+epsilon)/t)-delta(a/t)).
The error from the first two terms is <=t/(8*a*epsilon).
The actual (1,-4,4) combination at scales 4N,2N,N cancels 1/t and retains -1/2:
|A_n(t)+1/2|<=25*t/(32*N*epsilon).
Thus |exp(-x/2)*F_n(x)+c_N|<=K_N*exp(x), and exp(-x/2)*F_n(x)->-c_N at negative infinity.

Define F_(n,c)=F_n+1_(x<=0)*c*exp(x/2), c real.
Integrable(exp(-x/2)*F_(n,c)(x)) iff c=c_N.
Positive weighted source exp(x/2)*F_(n,c)(x) is integrable for every c.
The canonical correction therefore has both weighted moments integrable. The original completion's negative weighted source is NOT integrable.

For Re(s)>0 the corrected readout is integrable and equals
integral exp((s-1/2)*x)*F_(n,c)(x) dx = mellin(A_n)(s)/sqrt(N)+c/s.
At a right-half-plane zeta zero rho this is c/rho; for c=c_N it is nonzero.

Uniqueness is within this exponential coefficient family, not among arbitrary corrections. No full-Weil domain membership or positivity follows. The correction jumps at zero, and K_N depends on epsilon^-1, so no uniform-in-N Weil estimate has been obtained.

## Files and declarations

New files under formal/GaloisForLFunctions/BiScaleUncertainty/:
- ClampedRampLatticeSum.lean: clampedLatticeRemainder, bounds, clampedLatticeSum, summability, exact formula, error bound.
- FactorialMuntzBoundaryPole.lean: actual sum decomposition, actual boundary error, factorialMuntzBoundaryCoefficient, factorialMuntzBoundaryError, positivity, completion error and limit.
- FactorialMuntzBoundaryRepair.lean: factorialMuntzBoundaryCorrected; negative integrability and iff classification; not_integrable_factorialMuntzCompletion_negPole; corrected readout integrability/equality; positive integrability; zero readout and canonical nonzero theorem.

All three imports occur exactly once in formal/GaloisForLFunctions/BiScaleUncertainty.lean.

Existing FactorialMuntzReadout.lean required two explicit Integrable type annotations in factorialRamp_zeta_readout. Its facts had expanded exponentials while integral_sub's goal used private readoutKernel. No theorem statement or other proof changed; exact before/after comparison passed. Seed, completion and tail sources remained unchanged. Do not attribute the rest of this concurrent module to this work.

## Verification

All three new leaves passed direct lake --old env lean -j 1 checks. Required existing FactorialMuntzTail and FactorialMuntzReadout also passed. Four scratch API/analytic probes passed. New-leaf diagnostics contain only tactic-style warnings.
A /tmp audit checked every new public declaration plus repaired factorialRamp_zeta_readout: 24/24 use only propext, Classical.choice, Quot.sound. No axiom/RH premise wrapper was introduced.
scripts/formal_tools.py index passed (0), updating formal/LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md.
lint --check-generated returned 1 for two unrelated unreachable modules:
- BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer
- BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect
Also 381 large-file warnings. No lint error concerns these changes. Do not silently edit unrelated work.

Record: /tmp/bsu-muntz-boundary-verification.json.
Audit: /tmp/bsu-muntz-boundary-axioms.log.
Gate logs: /tmp/bsu-muntz-index.log and /tmp/bsu-muntz-lint.log.
Exact source hashes, object freshness, declaration coverage, dependency-fix scope and import counts are recorded. Final check confirmed four current source hashes/fresh objects, nine card links, old card paths absent, no owned Lean process active.

Checks used a pinned snapshot of 8670 existing dependency objects: six fallback objects and 133 pre-existing objects older than their source timestamps. No dependency source changed during verification. This is NOT a fresh whole-tree build. Owned /tmp/bsu-muntz-boundary-cache was safely removed by validated individual unlink/rmdir; normal compiled leaf objects remain. Saved setup maps now point at a removed cache: DO NOT REUSE them as live checks. No full/umbrella build, heartbeat increase, numerical experiment, web search, commit or push was performed. README/frontier map were not edited by this work.

## Cards / frontier

Positive survivor: docs/drafts/pipeline/3-formalized/factorial-muntz-boundary-repair-2026-10-18.md.
Retired shortcut: docs/drafts/pipeline/5-failed/factorial-muntz-boundary-pole-2026-10-18.md.
Parent remains active: docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md.
Only the naive claim that L2 completion plus zero readouts already supplies an admissible null source is retired. Strong positive survivor was paper-proved and formalized before closure. Coupled margin B_n>=2|P_n|+factorialWeilGramError n, actual full-Weil positivity, all-source RW positivity and RH remain open. Earlier polar-loss scale work is in mem:biscale/factorial-polar-loss-asymptotic.

## Concrete follow-up (source inspected, not newly formalized)

Additional partial corpus query: /tmp/bsu-muntz-rational-weil-search-20261018.json. All 20 candidate and 20 source-argument statements inspected; reranking timed out, semantic coverage unmeasured, refresh incomplete. No exhaustive-search/novelty claim.
Existing source:
- RHTower/ArchimedeanGenusZeroSum.lean, tsum_inv_zero_mul_one_sub_zero: sum over XiZeroCopy of 1/(rho*(1-rho))=poleSharpConstant=2+gamma-log(4*pi).
- LiCoefficientXi.lean, summable_xiLiPairedTerm.
- LiFirstCoefficientsNonneg.lean, re_xiLiPaired_nonneg_of_le_68.
- SuzukiCorFourSix.lean, suzukiEntireFourier_liTestFun_term and suzukiLiWeilForm_eq_xiLiPaired.
- ExpDecayTest in WeilConeXiDivisibleBlindTest.lean explicitly requires ContDiff order 2; the discontinuous canonical correction does not directly qualify.
Next substantive bridge: admissible full-Weil identity for the actual corrected source, with normalization/multiplicities audited, then quantitative passage back to the compact ramp. A zero-series identity alone does not discharge that obligation. Do not repackage an assumed full-Weil bound or reprove existing first-Li positivity as if it supplied RH.

## Useful Lean lessons

Use underlying sourceFactorialRamp properties from SignedPrimePolarCausalSource rather than adding the bundled factorialRampSource dependency unnecessarily.
Force the indicator to be real before complex coercion: (((indicator ... x : real) : complex)); an expected complex type can otherwise move coercions inside the indicator and defeat matching.
For constant integrability on an infinite half-line, apply (integrableOn_const_iff (C:=...)).mp h as a term; a simp-only attempt left the default finite-norm condition unresolved.
Use IntegrableOn.integrable_indicator explicitly after const_mul if dot notation sees the expanded And type.
Change generic Integrable.re to an explicit Complex.re integrand before simplifying real coercions.
Use a mathlib-only scratch probe for API/elaboration fixes; loading the full project import chain was slow under concurrent work. Keep exactly one owned foreground Lean process, and wait for terminal status before replacement.
