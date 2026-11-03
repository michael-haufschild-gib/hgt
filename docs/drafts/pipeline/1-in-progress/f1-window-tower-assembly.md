# F1: positivity through the window tower

- **ID:** F1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0211/obstacles-summary.md`, §2.3 F1
- **Statement:** Prove unconditional Weil positivity on every window by a compatible stage-local payment of the frozen arithmetic form.

## Mathematical core

At level `N+1`, write `ℓ=log(N+1)`, `ε=A−ℓ`, `w=Λ(N+1)/√(N+1)`,
`C=∫collarWeight(A,ε)H²`, and `F=foldEnergy(A,ℓ,H)`. The exact identity is
`Q(H)=Q_N(H)+w(F−C)`. The proved exit bound is `Ω(ε)C≤J∞(H)` and `w≤Ω(ε)`.
The stronger loan `Q_N≥Ω(ε)C` is false already at `N=1`. The exact signed payment remains open.

## Gates

- [x] Source statements: `TheTransferAcrossAStage`, `TheExitChargePaysEveryNewFold` inspected.
- [x] Audit the base range and the exact remaining stage payment.
- [ ] Construct a lossless bridge from the nonlocal payment tools to that payment.
- [ ] Prove the remaining arithmetic inequality without an assumed positivity input.
- [x] Formalize the first-fold obstruction and positive survivor; integrate and audit both modules.

## Open conjecture

The exact signed fold cost `w(C−F)` can be paid uniformly along the tower. The sufficient costs
`wC` and `Ω(ε)C` discard the positive fold contribution and fail on the cubic witness below.

## Audit findings

- The base is already proved through length `181/250`, all real C² tests, by
  `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths` (SP). F1's `3/5` base is stale.
- ACCE `ThresholdVanishingAndCollarDominanceOfThePrimeShell` already proves the exact threshold
  ladder: every spectral drop between consecutive entrances is frozen-operator domain relaxation.
  Its ground-state collar sandwich also exists. Repackaging these is not a new bridge.
- A C² test in `[-21/20,0]` has `Q₁<0<Q`. The stronger loan is false; prime `2` repairs
  a negative frozen direction on the same test.

## First-fold test

[Signed repair](../5-failed/f1-nonnegative-collar-loan.md) gives the complete analytic proof:
the unit cubic has frozen value `<−29E/2100` and complete value `>E/100`.
Mollification and translation yield a C² witness in `[-21/20,0]`, still below `log3`.
Both modules pass individual Lean checks and standard-only transitive-axiom audits.
This disproves the sufficient collar loan while preserving a strictly positive complete test.

## Remaining bridge

Retain `Q_N+w(F−C)` jointly. Existing variable-hub and two-vertex Schur identities require
positive pivots and control of the residual Schur scalar; those signs are not provided by
exit-charge domination. Exact IMS localization and coherent collar transport already exist;
their signed errors still require arithmetic control. The established complete-form coercivity
reaches length `181/250`.

[Cubic moment payment](../2-fully-proven/f1-rank-one-frozen-odd-payment.md) has a dependency-closed
paper proof of `Q₁(F)+20M(F)²≥∫F²/125` on the full unit odd window. Lean formalization is in
progress; the bound is not yet used as a proved input to the prime-2 payment.
