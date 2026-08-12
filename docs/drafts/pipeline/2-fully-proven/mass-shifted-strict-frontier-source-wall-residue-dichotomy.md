# Mass-shifted strict-frontier source-wall residue dichotomy

- **ID:** `mass-shifted-strict-frontier-source-wall-residue-dichotomy`
- **Stage:** 2-fully-proven
- **Type:** CANDIDATE contact-order classification
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Claim:** Every occupied strict frontier has exactly one of two source-wall asymptotics:
  a finite positive simple-pole residue determined by the negative first omitted monic remainder,
  or an infinite scaled residue when that remainder vanishes.

## Gates

- [x] 0 → 1: exact source-first claim, corpus frontier and falsifiers identified
- [x] 1 → 2: dependency-closed paper proof survives hostile audit
- [ ] 2 → 3: exact Lean theorem, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4: standalone presentation and independent novelty audit

## Internal frontier

At a strict rung `y = tau_(n+1)`, set `d=n+1`, `m=d+1=n+2`,

```text
S(v) = canonicalAdaptiveShear(v,d),
N(v) = canonicalAdmissionNorm(v,m),
Wall(v) = S(v)/(16 N(v)).
```

The formal corpus proves `S(y)>0`, `N(y)=0`, `N(v)>0` for every `v>y`, continuity of `S`, and
the flat-face derivative law

```text
N'(y) = -(2m+1) R,
```

where `R` is the first omitted monic remainder of the terminal normalized null admission.
The existing wall theorem proves reciprocal domination but deliberately does not classify the
scaled residue.

## External frontier

- Positive-weight orthogonal-polynomial and matrix-model results identify Hankel determinants as
  tau functions and relate their logarithmic derivatives to recurrence coefficients, but retain
  positive-measure/model-specific hypotheses.
- Indefinite Toda theory permits tau-divisor blow-ups; complex/indefinite orthogonal-polynomial
  dynamics likewise do not exclude singular recurrence coefficients.
- Therefore existence of a pole is bridge material. The route-specific content is the exact
  shifted-Xi adaptive arithmetic numerator and its contact-order residue classification.
  External novelty remains unverified.

## Conjecture → proof/fail loop

1. **C1 — every strict wall has a finite nonzero simple-pole residue. `[FALSIFIED]`** If the
   first omitted remainder vanishes then `N'(y)=0`; differentiability gives
   `N(v)/(v-y) -> 0`, while `S(v)->S(y)>0`, so `(v-y)Wall(v)->+infinity`.
2. **C2 — transversal first contact has an exact positive residue. `[PAPER-PROVED]`** If `R<0`,
   put `a=-(2m+1)R>0`. Then `N(v)/(v-y)->a`, hence
   `(v-y)Wall(v)->S(y)/(16a)>0`.
3. **C3 — positive right chamber forces `R<=0`. `[PAPER-PROVED]`** Since `N(y)=0` and
   `N(v)>0` for `v>y`, the right derivative is nonnegative. The exact derivative law gives
   `-(2m+1)R>=0`, hence `R<=0`.
4. **C4 — strict frontiers have an exhaustive finite/infinite scaled-residue dichotomy.
   `[PAPER-PROVED]`** By C3, either `R<0`, giving C2, or `R=0`, giving C1's positive survivor.

## Dependency-closed paper proof

Let `y=tau_(n+1)`, `m=n+2`, and let `c` be the monic canonical null vector of the singular
positive-semidefinite `(m+1)` block. Strict-frontier face classification supplies positive
`m`-head, singular PSD `(m+1)`-extension, and `y>0`. Thus `c` is in the extension kernel,
`N(y)=0`, and the canonical flat-face norm derivative theorem gives

```text
N'(y)=a:=-(2m+1)R.
```

Every `v>y` belongs to the positive chamber for the same block, so `N(v)>0`. If `a<0`, the
definition of derivative would make `(N(v)-N(y))/(v-y)<0` for all sufficiently close `v>y`, a
contradiction. Hence `a>=0`, and since `2m+1>0`, `R<=0`.

Differentiability gives the one-sided slope limit

```text
N(v)/(v-y) -> a.
```

The preceding source is continuous and strictly positive at the frontier:

```text
S(v) -> S(y)>0.
```

If `R<0`, then `a>0`, so division of these limits yields

```text
(v-y) Wall(v) -> S(y)/(16a) > 0.
```

If `R=0`, then `a=0` and the slope is positive on the right chamber. Its reciprocal tends to
`+infinity`; multiplication by `S(v)/16 -> S(y)/16>0` gives

```text
(v-y) Wall(v) -> +infinity.
```

These cases are exhaustive by `R<=0`.

## Hostile audit and significance

- No RH premise, positivity beyond the actual right chamber, fixed reporter, orientation choice,
  or numerical input occurs.
- This does not exclude strict frontiers and is not an RH proof.
- Generic tau-function pole classification is not new. Exact adaptive-source residue and the
  identification of tangency as infinite scaled residue are `[NOVELTY UNVERIFIED]`.
- Mathematical delta: failed universal simple-residue claim is replaced by an exact exhaustive
  contact-order law. Any future finite-action renormalization must pay either the explicit
  transversal residue or an unbounded tangential residue.

## Exact next question

Can shifted-Xi arithmetic exclude the tangential branch, or force a nonsummable lower bound on
the explicit transversal residues along cofinal strict rungs? Either result would turn local wall
classification into genuine phase exclusion.
