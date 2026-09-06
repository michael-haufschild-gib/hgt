# Literal prime action on the two pole profiles (2026-09-06)

RH goal remains ACTIVE and unproved. This turn closes actual prime action/cancellation, not Gamma action or constrained sign. No subagents, commits, computations, or added axioms. Preserve concurrent shared-tree work.

## Finished
New wired `formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPrimePolarArithmeticAction.lean`, 12 public theorems, 3 defs. Imports PrimeOuterShell, PolarGroundForcing, MertensFirst. See `docs/drafts/pipeline/3-formalized/weil-prime-pole-arithmetic-action.md` for dependency-closed paper proof and conjecture loop. Route O ledger paragraph and universal-law constraint updated, preserving other routes.

Write P for actual finite-prime operator, p±=cutoff exp(±x/2), M(X)=sum n in Icc2 floorX Lambda(n)/n. Exact AE actions on [-a,a]:
P p+ = exp(x/2)[psi(exp(a-x))+M(exp(a+x))].
P p- = exp(-x/2)[M(exp(a-x))+psi(exp(a+x))].
Single atom directions have weights 1 and 1/n; cutoffs logn<=a-x, logn<=a+x. Reflection theorem for arbitrary exponent s: P p_-s = reflection(P p_s).

`ccmPrimePolarDefect a s := P p_s - exp(a) p_-s`. Defect plus replaces psi(Y) with psi(Y)-Y; minus reflected. `inner_polar_prime_on_constrained` gives both pole moments <p±,P f>=<D±,f> for u : ccmPolarConstraintSubmodule a, f=J u. No ground assumptions.

`ccmReciprocalMangoldtError t := M(exp t)-t`; `abs_ccmReciprocalMangoldtError_le ht` bounds abs by log4+5 for t>=0, using existing elementary MertensFirst at floor(exp t) and 0<=t-log floor(exp t)<=1.

`ccmPrimePolarDefect_plus_centered_coeFn`: D+ - a p+ has exact AE representative exp(x/2)[psi(exp(a-x))-exp(a-x)+E_M(a+x)+x] on aperture. `inner_polar_prime_centered_on_constrained` removes the a p+ term. Final `inner_polar_prime_constrained_eq_arithmetic_integral` identifies the actual prime moment with integral of this real kernel times the actual complex L2 f. This is an off-diagonal source identity, not complete forcing coefficients or whole quadratic positivity.

## Validation
Scratch /tmp/hgt-prime-pole.Xhbr4D4a. `Integral.lean` is final passing body (no header), `Production.lean` exact production copy. Earlier Atom/Sum/Reflection/Defect stages have stale failures; Mertens.lean final passing without final integral.
Named final build `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePolarArithmeticAction` passed (34s;12778 cached/target jobs). All12 public `#print axioms` in Audit.lean give exactly [propext, Classical.choice, Quot.sound], actual mathlib RiemannHypothesis printed. LintFinal.txt says formal lint passed; LintWarningsFinal.txt large-file warnings only. Initial lint hit other task's new OneDimBrascampLieb unreachable; owner then wired it and final gate passed. No unrelated code changed. git diff --check passed. ALL owned Lean/build processes terminal.

## Next concrete conjecture
Open card `docs/drafts/pipeline/1-in-progress/weil-gamma-pole-boundary-action.md` has source-derived candidate, explicitly NOT proved. Start next turn full chain: exact prime-Gamma profile action -> control constrained ground forcing -> exclude zero ground -> all-aperture floor -> weighted pole exclusion -> RH.

Let R=a-x,L=a+x>0, rho(h)=exp(-h/2)/(1-exp(-2h)). Current CCMActualHeadGammaAutocorrelationEnergy proves integral rho(h)(2-2cos(2pi xi h))=2(gammaHardyPhaseRate(2pi xi)-gammaHardyPhaseRate0). HardyZ defines 2gammaHardyPhaseRate0=Re digamma(1/4)-logpi. DigammaIntegralRepresentation has exact integrable Gauss formula; EulerMascheroniGaussKernel exact Gauss/Euler integral.
Candidate A_a p+ / p+ = -R + kappa + B_a(x), kappa=-EulerGamma-log(2pi), B= -1/2 log(1-exp(-2R))-1/2 log(tanh(L/2)). Derivation uses formal physical generator ratio g0+integral rho[2-exp(h/2)1h<=R-exp(-h/2)1h<=L]. Endpoint primitives: h+1/2 log(1-exp(-2h)) and1/2 logtanh(h/2). Gauss t=2h cancels common2rho; regularized exponential integral predicts kappa. Must rigorously prove integrability/endpoint cancellation, profile domain, and actual Friedrichs weld. Existing energy identity alone is insufficient.

Predicted polar rank-two action: 2a p+ +2sinh(a)p- (verify/reuse exact Gram entries). Together predicts H p+ = p+[kappa+B-Epsi(exp(a-x))-E_M(a+x)]-exp(-a)p-. On constrained pairings all kappa/opposite terms vanish, leaving explicit boundary kernel minus arithmetic errors. This would remove the x ramp exactly but DOES NOT give a sign against a sign-changing ground. No candidate here enters Lean as assumption.

## Lean lessons
Lp.coeFn_fun_finsetSum s f exists; Lp.coeFn_sum does not. Namespace for realTranslation_measurePreserving is RHTower.MellinL2. `Real.log_le_iff_le_exp`, `Nat.le_floor_iff`, finite filter ext with floor_mono handles exact cumulative cutoffs. Exp-half-log proof via Real.log_sqrt and exp_log; no extra source import needed. For smul in aperture inner products, even `(inner_smul_left (𝕜:=ℂ))` failed rw matching: specify both vector arguments AND complex scalar explicitly. After L2.inner_def, subtype coercions may distribute through sub/smul; use explicit `change ((d:SoninL2)-(a:ℂ)•(p:SoninL2)) x = _ at hx` before rewriting AE identity. For reflected AE equality simplify Function.comp_apply. `add_neg_eq_sub` absent; use ←sub_eq_add_neg. Beware zsh guessed globs; discover file paths with rg first.
