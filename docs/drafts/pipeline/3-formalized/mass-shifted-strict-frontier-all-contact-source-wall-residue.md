# Mass-shifted strict-frontier all-contact source-wall residue

- **ID:** `mass-shifted-strict-frontier-all-contact-source-wall-residue`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** At every finite first contact of order `d`, the actual Christoffel arithmetic-source wall has an exact finite positive `distance^d` residue; prior infinite lower-order residues are precisely under-renormalized shadows.

## Goal

Finish local quotient step left open after all-order newborn-norm capitalization. Identify exact
intrinsic wall price at every contact and express same germ through literal current adaptive mixed
completed arithmetic source before reflection aggregation.

## Gates

- [x] 0 → 1 in-progress: exact claim, source-pure formulation, falsifiers, corpus dependencies identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted build and axiom gate green
- [ ] 3 → 4 publication-ready: standalone proof and independent priority review

## Conjecture → proof/fail ledger

1. `[FALSIFIED]` Infinite quadratic residue at flatter contact is an intrinsic infinite price.
   It only says order-two scaling is too weak. Finite first contact `d` forces an exact finite
   `distance^d` residue.
2. `[PAPER-PROVED]` Correctly scaled Christoffel wall has finite positive residue equal to previous
   positive source divided by sixteen times all-order newborn-norm coefficient.
3. `[PAPER-PROVED]` On physical square-mass germ, same scaled wall is literally current adaptive
   mixed completed rational--Gamma-minus-von-Mangoldt source divided by newborn norm.
4. `[OPEN CORE]` Local residue does not add across degrees without a common action/admission law.
   Cofinality alone permits residues and neighborhoods to shrink arbitrarily fast.

## External audit

Recent Hankel/Painlevé work studies tau zeros and recurrence-coefficient poles; positive-measure
Christoffel literature studies degree asymptotics. These supply generic quotient/pole bridge but
not shifted-Xi admission-selected prime--Gamma numerator or exact all-contact residue. Priority of
route-specific source identity remains `[NOVELTY UNVERIFIED]`.

## Dependency-closed paper proof `[PROVED HERE]`

At occupied strict frontier `y=tau_(n+1)`, put `m=n+2`, let `S(v)` be preceding canonical adaptive
source, and let `N(v)` be newborn canonical admission norm. Suppose `d>0` is first contact:

```text
delta_k=0 (k<2m+d),              (-1)^d delta_(2m+d)>0.
```

Corpus all-contact Schur law gives

```text
N(y+u)/u^d -> C_d
  := (-1)^d choose(2m+d,d) delta_(2m+d) > 0.
```

Strict-frontier source theorem gives `S(y)>0`, and analytic moment dependence gives
`S(y+u)->S(y)`. Since `N(y+u)>0` for all sufficiently small `u>0`, exact algebra gives

```text
u^d Wall(y+u)
 = (S(y+u)/16) * (N(y+u)/u^d)^(-1).
```

Taking limits yields

```text
u^d Wall(y+u) -> R_d := S(y)/(16 C_d) > 0.
```

For physical `y>1/4`, every sufficiently small positive displacement remains physical. Existing
source identity identifies `Wall(y+u)` with current adaptive mixed completed arithmetic source
at `sqrt(y+u)` divided by `32 N(y+u)`. Hence same `R_d` is exact literal arithmetic-source wall
residue. QED.

## Significance and honest residual

This replaces simple/double/infinite-scaled trichotomy by one intrinsic theorem valid at exact
first contact. It closes local wall quotient, but does not prove RH. Global burden is now sharply
nonlocal: construct common arithmetic action that makes cofinal positive residues accumulate, or
prove contact order/residue/neighborhood cannot jointly escape.

## Log

- 2026-08-13 — card opened; quadratic-infinite interpretation killed and exact all-order residue proof frozen.
- 2026-08-13 — formalized in `XiShiftedStrictFrontierAllContactSourceWallResidue.lean`; direct
  check, targeted module build, umbrella reachability, and axiom audit passed. Repository lint
  reached module but remains red only on unrelated concurrently added modules missing from
  `RHTower.lean`.
