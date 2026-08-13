# Mass-shifted adaptive mixed source degree coercivity

- **ID:** `mass-shifted-adaptive-mixed-source-degree-coercivity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Newborn literal adaptive mixed/completed source action strictly pays squared adjacent degree flux, with sharp coefficient `3/2` and an exact positive Jacobi reserve.

## Goal

Upgrade exact degree--mass plaquette from transport identity to source coercivity.  Produce a
single source-first action that controls degree connector without fixed reporting or an external
orientation.  This is local/common finite-grade capital, not yet a uniform infinite-grade RH
budget.

## Gates

- [x] 0 → 1 in-progress: exact claim, falsifiers, proof, and source interpretation identified
- [x] 1 → 2 fully-proven: dependency-closed proof
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and novelty review

## Conjecture → proof/fail ledger

1. **Current action `J_n` pays connector `alpha_n+alpha_(n+1)`.** `[FALSIFIED]` `J_n` has no
   `alpha_(n+1)^2` term; next diagonal is free.
2. **Symmetric action `J_n+J_(n+1)` pays connector.** `[PROVED BUT NONSHARP]` Weighted Cauchy gives
   coefficient `4/3`, but current action is unnecessary.
3. **Newborn action alone pays connector.** `[LEAN-PROVED]` `J_(n+1)` contains
   `2 alpha_n^2+alpha_(n+1)^2`; sharp weighted Cauchy constant is `3/2`.
4. **Coercivity closes RH.** `[FAILED / SHARP BOUNDARY]` It creates common finite-grade Dirichlet
   action, but an infinite/parabolic staircase still needs uniform capital or boundary decay.

## Proof `[PROVED HERE]`

Put `a=alpha_n`, `b=alpha_(n+1)`.  Exact cumulative dissipation gives

```text
J_(n+1) = D_(n+1)
          = 2 sum_(j<n+1) alpha_j^2 + b^2
            + 4 sum_(j<n+1) beta_j
            + 2(n+2)(beta_(n+1)+beta_(n+2)).
```

Separating `a` yields exact reserve

```text
(3/2)D_(n+1) - (a+b)^2
 = 3 sum_(j<n) alpha_j^2
   + (1/2)(2a-b)^2
   + 6 sum_(j<n+1) beta_j
   + 3(n+2)(beta_(n+1)+beta_(n+2)).
```

In a positive block, both terminal betas are positive and all other terms are nonnegative.  Hence
reserve is strictly positive.  Existing degree renewal identifies `a+b=F_(n+1)-F_n`, while source
flow identifies `J_(n+1)=-F'_(n+1)`.  Therefore

```text
(F_(n+1)-F_n)^2 < (3/2) J_(n+1) = -(3/2) F'_(n+1).
```

## Log

- 2026-08-13 — current-only and symmetric conjectures audited; sharp newborn action theorem proved on paper.
- 2026-08-13 — formalized exact reserve, strict source coercivity, and derivative law in
  `RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceDegreeCoercivity.lean`; direct Lean check
  and targeted module build pass. Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
