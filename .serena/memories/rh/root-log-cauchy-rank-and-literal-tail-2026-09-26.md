# Root research: logarithmic-Cauchy rank obstruction and literal theta tail bridge

RH goal remains active and unresolved. No git commands, numerical experiments, subagents, full builds, or umbrella builds. All owned Lean/Lake/research/index/lint jobs exited. One compiler process enforced; an initially parallel dependency build was stopped by its owned process tree and replaced with LEAN_NUM_THREADS=1.

## Verified new leaves
1. formal/GaloisForLFunctions/RHTower/LogarithmicCauchyRankBoundary.lean
Namespace RHTower.LogCauchyRank, 36 public theorems.
Formal kernel (L+atanh z+atanh w)/(1-zw): diagonal L; odd off-diagonals 1/|i-j|, even off-diagonals zero.
For alternating 2m-vector: Q=2m*(L+1-2*h_m), h_m=sum_(j<m)1/(2j+1).
No fixed L works in every rank; no uniformly coefficient-energy-bounded repair works.
Positive survivor: |Q-L*E|<=2*h_m*E; sufficient L>=2*h_m, necessary L>=2*h_m-1.
Alternating absolute amplitudes minimize over sign choices.
2*h_m-log m -> 2log2+EulerGamma, exact joint signed corner profile.
Real Cayley identity and separate nested PowerSeries coefficient equation proved.
No analytic positive-kernel-to-jet transfer is claimed.

2. formal/GaloisForLFunctions/RHTower/ThetaTailCauchyAsymptotic.lean
Namespace RHTower.ThetaTailCauchy, 16 public theorems.
Phi is the literal complete source; K is thetaTailFirstMomentKernel.
A=pi*(exp(2x)+exp(2y)), D(r)=exp(-2r)*Phi(x+r)*Phi(y+r).
kernel_normalized_limit: K(x+r,y+r)/(r*D(r))->1/A.
kernel_two_term_limit: K(x+r,y+r)/D(r)-(2r+x+y)/(2A)->0.
sourceMatrix_eventually_posDef: every FIXED finite injective node set becomes positive definite under sufficiently large common translation. Threshold depends on rank and all node spacings.
Source proof uses FourthTuran full first-log jets to bound |Phi'/Phi+2*pi*exp(2z)|<=7 for z>0. Every fixed polynomial multiple of the scaled score error vanishes.
Exact shift derivative K'=-(2r+x+y)*Phi(x+r)*Phi(y+r), L'Hopital, Cauchy PSD/determinant, and existing positive-definite matrix limit close proof.
The constant correction links the literal source to the model at fixed nodes only. Growing-rank coefficient transfer remains open. No RH conclusion.

## Verification
Scratch checks and named leaf builds pass; model 3132 jobs, source 11010 jobs (cached reuse; stale transitive dependencies rebuilt).
Both wired into RHTower.lean near lines19474.
All 52 public theorem #print axioms reports checked exhaustively: only propext, Classical.choice, Quot.sound; none missing.
Audit files /tmp/rh-cauchy-both-axioms.lean, /tmp/rh-cauchy-both-axioms.log, /tmp/rh-cauchy-audit-result.json.
Final index refreshed; scripts/formal_tools.py lint --check-generated exit0, existing large-file warnings.
Logs /tmp/rh-tail-cauchy-build.log, /tmp/rh-cauchy-lint-final.log.
No owned processes remain.

## Owned records
Fact log docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md F49-F54.
Live parent docs/drafts/pipeline/1-in-progress/rh-nonlocal-tail-root-2026-09-26.md.
Model no-go docs/drafts/pipeline/5-failed/rh-log-cauchy-rank-root-2026-09-26.md.
Formalized source card docs/drafts/pipeline/3-formalized/rh-theta-tail-cauchy-root-2026-09-26.md.
Own main route card updated. Do not alter other agents' logs.

## Next hard obligation
Model transition L=2r+log(u0) gives m proportional to exp(2r). This is the model scale, NOT a theta negative direction.
ThetaCuspFirstAtomAllOrderApproximation theorem124 fixes k,n before its limit; do not use that quantifier order as uniform growing-order control.
Focused corpus retrieval found existing quantitative inputs:
ThetaCuspSupportScaleReflectionApproximation theorem133:
|(Phi^(n)-first^(n))/first| <= 3*(12q)^n*epsilon, q>=6, n+3<=q.
Native reflection-jet error <= [18*(16q)^n*epsilon+9*(24q)^n*epsilon^2]*first^2.
q=thetaCuspSingleAtomReflectionScale 1 x; epsilon=regimeOneLikelihoodScale x=exp(-3*(q-pi))/399 (ThetaCuspC5RegimeOneCurvatureSigns91).
Read signatures and proofs; these are EXISTING corpus results, not new root claims.
Missing: transfer these quantitative bounds to the actual tail kernel's Cayley coefficient form/energy when rank grows. Pointwise o(1) cannot do it. Higher asymptotic corrections can amplify under growing derivatives.
Existing common-translation Loewner no-go prevents transporting far-tail positivity to seam.
Nonlocal coupling/size-biased density candidate remains paper-only in parent; no full source PSD producer.

Searches latest /tmp/rh-tail-{rank-transfer-method,kernel-frontier,second-term-method,growing-order-frontier,allorder-frontier}-20260926.json.
Broad deep queries sometimes poor; exact source-name search found quantitative candidates. Inventory complete, compiler metadata mostly pending/stale; retrieval not proof.
