# Quadratic likelihood moments: exact domain and exchange symmetry

Status: formalized. Mathematical sources: local Lean corpus only.

## Proved result

For actual finite quadratic tilts `P_r,Q_r` with diagonal coefficients `s,S<2`, let
`M_r(theta) = integral exp(theta * llr(P_r,Q_r)) dP_r` and `u=s+theta*(s-S)`.

If `u<2`, limit:
`exp(theta*(log sqrt(2/(2-S)) - log sqrt(2/(2-s)))) * sqrt((2-s)/(2-u))`.
If `u>=2`, `M_r(theta)` diverges to positive infinity. Thus boundedness holds exactly on that open affine half-space; every real order is bounded exactly when `s=S`, in which case every moment tends to one.

At finite depth, exchanging the two laws sends `theta` to `-1-theta` and preserves the moment. Orders zero and minus one equal one exactly. Order minus one-half is the square-root likelihood overlap `integral sqrt(dQ_r/dP_r) dP_r`. Every order in `[-1,0]` is subcritical for both subcritical tilts.

## Dependency-closed paper proof

1. Existing exact finite log-likelihood ratio is the quadratic difference plus `log Z_Q-log Z_P`.
2. Pull the constant exponential outside the integral. The variable exponent is the quadratic form with coefficients `theta*(a-A),theta*(b-B),theta*(d-D)`. Existing tilted-response theorems apply; their combined diagonal coefficient is exactly `u`.
3. Both log normalizers converge to finite values and their exponential factor has a strictly positive limit. Multiply the existing finite-response or divergent-response limit by that factor.
4. The exact finite partition formula is `Z_combined * exp(theta*log Z_Q-(theta+1)*log Z_P)`. Exchanging laws and replacing the order by `-1-theta` preserves both factors algebraically.
5. Normalization at minus one follows the Radon–Nikodym integral identity. The half-order overlap follows `exp_neg_llr` and `Real.exp_half`.
6. If `s!=S`, order `(2-s)/(s-S)` reaches the critical boundary exactly, contradicting boundedness at every order. If `s=S`, every combined coefficient equals `s` and the limiting factor and response both equal one. The interval `[-1,0]` is the convex interpolation between `S` and `s`.

## Scope and checks

Actual finite roots discharge every analytic premise; final asymptotic roots use structural subcritical parameter subtypes. No web, external papers, numerical experiments, new axioms, full builds, heartbeat changes, or subagents. Native leaf checks and final scratch axiom audit are mandatory. Wire finished modules; inspect all new declarations, dependencies, and incoming imports. Record unrelated global lint failures without changing other work.

## Working log

- Previous increment proved actual pairwise KL convergence and exact diagonal rigidity.
- Local indexed likelihood/Renyi/Hellinger search in the WeilLogShift family returned zero hits, no markers or partial coverage. Exhaustive source search found only the newly established exact LLR theorem. Related local Hellinger/Renyi constructions concern other carriers.
- New target concerns the full exponential-moment domain of actual LLR, beyond its mean.
- Native build recovery: the limit leaf's tool handle disappeared after a session restart. A fresh `.olean`, empty log, and absence of the exact native process established completion. The final scratch audit subsequently imported it successfully. A transient OS permission failure on the card update cleared on retry; no permissions were changed.

## Final closure — 2026-10-12

All three native leaves now have fresh objects and empty logs. The rigidity leaf passed after making both subcritical diagonal parameter subtypes explicit. Metadata passed: 21 declarations, four direct dependency edges, five incoming imports, exact umbrella wiring. Local index passed 21/21 with no markers or partial coverage. Scoped whitespace checks passed.

Final native scratch audit exited zero. Its validator checked every one of the 21 declarations and all 21 API `have` checks; only `propext`, `Classical.choice`, and `Quot.sound` occur. No residual diagnostics. The live audit was polled through completion without a replacement process.

There are 19 new theorems and two definitions:

- `WeilLogShiftQuadraticLikelihood.lean`: the actual likelihood-moment definition and eight exact finite identities, including positivity, partition and response formulas, normalizations, exchange symmetry, and square-root overlap.
- `WeilLogShiftQuadraticLikelihoodLimit.lean`: the finite-branch formula and five theorems establishing its factor limit, finite and divergent branches, unconditional ENNReal limit, and exact boundedness criterion.
- `WeilLogShiftQuadraticLikelihoodRigidity.lean`: six theorems establishing same-diagonal finite branch, all-order boundedness and convergence classifications, the universally admissible interval, and the actual square-root overlap limit.

All finite-law statements hold for every natural `r,k` and every real coefficient tuple. All asymptotic statements hold at depth `2*(r+1)^2+t r`, with arbitrary `t : Nat -> Nat`, and only structural subcritical parameter subtypes. Bounds for all orders quantify each fixed real order separately. The interval result discharges the combined-coefficient constraint throughout `[-1,0]`.

The global lint run reported 367 warnings and eight errors outside these leaves: unreachable `BacklundLindelofConverse`, `CCMPolarOddPrimeJumps`, `PaperThetaBoundedVariation`, `PaperThetaSourceRatio`, `PaperThetaVariationBudget`, `RiemannKernelTruncationEnergyOrder`, and `QKrawtchoukCompanionTriangular`, plus the existing `sorry` at `CCMPolarOddPrimeJumps.lean:104`. No owned leaf is flagged.

Proof lessons: keep `.pos_mul_atTop` on the same line as its receiver; specify both structural diagonal subtypes when applying the interpolation lemma; the Radon–Nikodym integral theorem is `Measure.integral_toReal_rnDeriv`; use `Real.continuous_exp` to avoid the unrelated generic `Filter.Tendsto.exp` universe parameters.

Artifacts: `/tmp/hgt-weil-likelihood-power-{metadata,index-summary,audit-summary}.json`, `/tmp/hgt-weil-likelihood-power-final-audit.lean`, `/tmp/hgt-weil-likelihood-power-final-audit.log`, `/tmp/hgt-weil-likelihood-power-incoming-imports.txt`, and `/tmp/hgt-weil-likelihood-power-lint.log`. No full build, heartbeat increase, numerical experiment, web search, external paper, subagent, commit, or push was used.
