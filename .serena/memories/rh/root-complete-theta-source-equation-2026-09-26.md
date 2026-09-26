# Root: complete theta source equation S1 (2026-09-26)

Active goal remains unconditional Lean proof/falsification of RH. NOT achieved. Read goal attachment /Users/michael/.codex/attachments/57626bac-f4cf-4d94-bed5-5e4426c73652/pasted-text-1.txt each goal turn.
User: no git, no heartbeat/recursion increases, no numerical mathematical experiments, one foreground Lean process with LEAN_NUM_THREADS=1 and -j1. No subagents authorized. Heavy corpus-backed conjecture/proof/fail/pivot; own fact log only.

## Verified new corpus result
Frozen derived bridge S1 is proved:
G_+(x)-P_+(x)=x*Phi(x), every real x, literal complete theta source.
G_+=-(EulerGamma+log pi)Phi/2
 + integral_(u>0) [exp(-2u)Phi(x)-exp(-u/2)Phi(x+u)]/(1-exp(-2u)) du
 + integral_(u>0) 2cosh(u/2)Phi(x+u) du.
P_+=sum_(n>=2) Lambda(n)/sqrt(n)*Phi(x+log n).
Lean literal theorem uses equivalent complex casts and tsum over all naturals (Lambda(0)=Lambda(1)=0).
Convergence is proved; Gamma subtraction remains inside the integral.

Four wired leaves, namespace RHTower.ThetaSourceWard:
- ThetaSourcePrimeAction.lean (197 lines): generic ThetaSource prime action, absolute summability, continuity, full Laplace multiplier, weighted L1. laplaceIntegrand, integrable_laplaceIntegrand live here.
- ThetaCuspGammaSourceAction.lean (426): small-u cancellation via actual derivative envelope; joint absolute Fubini for -1/2<Re(w), |Re(w)|<1; digamma multiplier; global continuity.
- ThetaCuspPolarSourceAction.lean (160): both pole actions, absolute Fubini, local dominated continuity, literal 2cosh sum.
- ThetaCuspPrimeArchSourceEquation.lean (217): actual completed-Xi symbol identity + weighted Fourier uniqueness on Re(w)=3/4; theorem literal_complete_theta_source_equation at line 204.

All four named builds pass. All 71 public declaration axiom reports standard only (propext, Classical.choice, Quot.sound), none missing. Index regeneration passes. Global lint fails ONLY unrelated unwired RHTower.CircleLinearPhaseSeamMargin. No own-leaf/stale-index error. One harmless informational ring hint at final leaf line159; proof closes.
Scratch full proof /tmp/rh-s1-full.lean exits0, component prefix /tmp/rh-s1-.
Logs /tmp/rh-s1-{prime,gamma,polar,equation}-build.log, /tmp/rh-s1-final-axioms.log, /tmp/rh-s1-index.log, /tmp/rh-s1-lint.log.
All owned Lean/build/search/index/lint sessions terminal as of final report.

## Whole-route status — do not overclaim
S1 closes an analytic source-annihilation gap, NOT the sign of K or RH.
Main card: docs/drafts/pipeline/1-in-progress/rh-full-source-sign-root-2026-09-26.md.
Own fact log: docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md through F99.
Earlier C12 exact negative-dimension bridge and C11 strict-reserve no-go complete; do not revisit their packaging.

Remaining direct target:
D_Phi(f,u)=int Phi(x)Phi(x+u)|f(x+u)-f(x)|^2 dx.
Prove or falsify for every smooth compactly supported complex f:
int_(u>0) [exp(-u/2)/(1-exp(-2u))-2cosh(u/2)]D_Phi(f,u)du
 + sum_n Lambda(n)/sqrt(n) D_Phi(f,log n) >=0.
Exact ground-state identification with the literal Weil form still needs test-function algebra/exchanges; S1 supplies the source annihilation input. Even that identification does NOT prove the sign. Next work must attack compensation itself, not another criterion/receiver or minor no-go.

Paper diagnostic for a new attempted proof: naively commuting right/left one-sided actions before compensation is invalid. Polar-polar double integrand exp((u+v)/2)Phi(x+u-v) has divergent absolute integral: v=u+s, 0<=s<=1 gives positive compact-source lower bound times exp(u). This is not a no-go for compensated operators; no positive factorization was obtained. Card records exact scope. Do not spend a new turn formalizing this minor diagnostic.

Latest deep searches /tmp/rh-s1-compensation-search.json and /tmp/rh-s1-commutator-search.json completed partial=false/errors=[]; mostly irrelevant candidates, no applicable unconditional compensation theorem. Compiler metadata predominantly source-only/pending/stale, not proof applicability. /tmp/rh-s1-ground-lexical.json also inspected.
