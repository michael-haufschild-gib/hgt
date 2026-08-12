# Mass-shifted strict-frontier Christoffel source wall

- **ID:** `mass-shifted-strict-frontier-christoffel-source-wall`
- **Stage:** 3-formalized
- **Type:** CANDIDATE arithmetic source law
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Statement:** Every occupied strict terminal-frontier rung annihilates next canonical admitted
  norm while leaving preceding adaptive arithmetic source strictly positive; its intrinsic
  Christoffel completion dominates reciprocal distance and has infinite local action.

## Goal

Classify exact singularity seen by admission-sensitive source-first producer at genuine terminal
frontier. No orientation map, fixed linear reporter, or external clock may enter. Target is closed
false-RH phase law: either RH, or cofinally many strict frontier rungs carry one-sided infinite
completed-source walls.

## Gates

- [x] 0 → 1 in-progress: source-pure, well-posed, corpus dependencies identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean capstones, targeted build green, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external specialist novelty audit

## Conjecture → proof/fail loop

1. **C1 — strict frontier kills next admitted norm. `[PAPER-PROVED]`** At
   `y=tau_(n+1)`, corpus gives `H_(n+2)(y)>0` and singular `H_(n+3)(y)>=0`.
   Principal-head invertibility canonically normalizes full-block null vector to terminal
   coefficient one; uniqueness of inverse-Hankel admission identifies it with degree-`n+2`
   admission. Its norm is zero.
2. **C2 — previous adaptive source also collapses. `[FALSIFIED]`** In positive chamber,
   degree-`d` Jacobi energy contains `(d+1)(beta_d+beta_(d+1))`. For `d=n+1`, previous edge
   `beta_(n+1)` tends to strictly positive boundary value while next edge `beta_(n+2)` tends to
   zero. Continuity forces boundary adaptive shear to remain strictly positive.
3. **C3 — Christoffel completion contradicts arithmetic analyticity. `[FALSIFIED]`** Literal
   adaptive arithmetic source stays finite and positive. Pole is created by dividing by vanishing
   endogenous next admitted norm. No contradiction follows without independent arithmetic
   finite-action/admission-regularity law.
4. **C4 — strict frontier is an infinite admission-action wall. `[LEAN-PROVED]`** Since source
   numerator tends to a positive value, next admitted norm tends to zero through positive values
   on right positive chamber. Their quotient tends to `+infinity`. Combine with existing cofinal
   strict-rung dichotomy to classify false-RH phase by cofinal source walls.
5. **C5 — frozen null packet linearly majorizes moving next norm. `[LEAN-PROVED]`** At boundary
   freeze terminal monic null packet `c`. In right chamber, write frozen monic polynomial as
   moving canonical admission plus a lower-degree remainder. Orthogonality gives exact
   Pythagorean decomposition, so canonical norm is at most fixed-packet energy. Corpus actual
   integral-Lipschitz theorem then gives `N_(d+1)(v) <= W(c)(v-y0)`.
6. **C6 — corpus source recession/secant budget makes completed wall locally finite.
   `[FALSIFIED]`** Those budgets control literal finite numerator inside positive chamber. They do
   not survive division by collapsing next Christoffel norm. Existing Gauss-edge completion law
   confirms quotient is intrinsic adaptive scale completion, not a fixed reporter.
7. **C7 — every wall has finite nonzero simple-pole residue. `[FALSIFIED AS UNIVERSAL]`** Delayed
   odd/even first contact permits flatter norm collapse. Universal result is one-sided lower order:
   wall dominates a positive reciprocal multiple and may diverge faster.

## Candidate paper proof

Let `N_j(y)` be actual canonical degree-`j` admitted norm and `S_j(y)` actual adaptive shear,
formed from current inverse-Hankel admission before reflection aggregation. Define

```text
Wall_j(y) = S_j(y) / (16 N_(j+1)(y)).
```

At strict rung `y0=tau_(n+1)`, set `d=n+1`. Singular PSD extension with positive principal head
gives `N_(d+1)(y0)=0`. Every `y>y0` lies in positive chamber for `H_(d+2)(y)`, hence
`N_(d+1)(y)>0`.

Inside that chamber, exact source localization and completed-square Jacobi decomposition give

```text
S_d(y) = N_d(y) E_d(y),
E_d(y) > (d+1) beta_d(y),
beta_d(y) = N_d(y)/N_(d-1)(y).
```

All three norms and adaptive shear are continuous at `y0` because relevant leading principal
blocks remain invertible there. Both `N_d(y0)` and `N_(d-1)(y0)` are positive. Passing chamber
inequality to boundary yields

```text
S_d(y0) >= (d+1) N_d(y0)^2 / N_(d-1)(y0) > 0.
```

Therefore `S_d(y) -> S_d(y0)>0` and `N_(d+1)(y) -> 0` through `Ioi y0`, proving
`Wall_d(y) -> +infinity`. Existing false-RH cofinal strict-rung theorem then gives cofinally many
such walls if RH is false.

For local action, freeze boundary admission vector `c` and let `P_v` be moving canonical monic
admission. Both are monic degree `d+1`; hence `R_v=P_c-P_v` has lower degree. Canonical
orthogonality in right chamber gives exact decomposition

```text
Q_v(c) = N_(d+1)(v) + <R_v,R_v>_v >= N_(d+1)(v).
```

At boundary `Q_(y0)(c)=0`. Actual integral-Lipschitz theorem for fixed Hankel quadratics yields

```text
N_(d+1)(v) <= Q_v(c) <= W(c)(v-y0).
```

By source continuity, eventually `S_d(v) >= S_d(y0)/2`. With `W(c)+1>0`, therefore

```text
Wall_d(v) >= [S_d(y0)/(32(W(c)+1))] * (v-y0)^(-1).
```

Thus wall is not interval-integrable on any nontrivial right interval. False RH forces such
strict rungs cofinally, so RH is exactly absence of cofinal non-integrable Christoffel-source-wall
phase. This is phase equivalence, not RH proof.

## No-go closure

- **Exact killing mechanism for direct contradiction:** Christoffel completion is a quotient by
  endogenous admission norm, so its pole need not be a pole of literal arithmetic source.
- **Strongest positive survivor:** strict frontiers are one-sided, reciprocal-dominating,
  locally non-integrable completed adaptive-source walls.
- **New insight:** remaining RH burden is not source production, positivity, analyticity, or
  ordinary source recession. It is an arithmetic admission-effectivity law proving local finite
  action/admissibility for exact Christoffel-completed producer, which would exclude every strict
  frontier.
- **Status:** dependency-closed paper proof and Lean formalization complete. Direct Lean and
  targeted module build pass. Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`. Repository lint does not flag this wired module; its nonzero exit is caused by
  unrelated concurrently unwired modules and existing large-file warnings.

## External audit

Recent deformed-Laguerre, matrix-model, elliptic-orthogonal-polynomial, Christoffel, and Toda papers
derive diagonal control only under model-specific positive-weight, Riemann--Hilbert, or algebraic
curve hypotheses. Indefinite Toda theory explicitly permits blow-up divisors. No located theorem
transports completed source through shifted-Xi terminal degree without assuming positivity being
proved.

## Log

- 2026-08-12 — created in 1-in-progress after corpus and broad recent-literature audit.
- 2026-08-12 — C4--C5 proved in Lean; C6 and universal simple-residue C7 falsified; strongest
  survivor upgraded to infinite local action and closed cofinal non-integrable phase law.
- 2026-08-12 — direct Lean, targeted module build, umbrella wiring, and axiom audit passed;
  promoted to `3-formalized`.
