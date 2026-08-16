# Route P fourth-depth Gamma-cyclic Julia intertwiner

- **ID:** `route-p-fourth-depth-gamma-cyclic-julia-intertwiner`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105D]`
- **Parents:** `route-p-primitive-burnol-julia-krein-matrix-completion.md`,
  `route-p-fourth-depth-copoisson-julia-krein-pivot.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePFourthDepthGammaCyclicJuliaIntertwiner.lean`

## Goal

Find source-side Gamma provenance for P-G104/P-G105's coefficient `sqrt(63)/8` and prove an actual
operator equality, without fitting a Xi zero or pretending Gamma aperture multiplier itself is
`1/8`.

## Conjecturing loop

### Conjecture 1 — existing Gamma aperture contraction equals `1/8`

Already falsified in P-G105: corpus proves that multiplier is always greater than `1/2`.

### Conjecture 2 — finite prime-cell Gamma budget has a source gauge with Cayley coordinate `1/8`

Existing prime-cell law uses running odds `a>0`, thermal ratio `T>1`, and Cayley coordinate

```text
C=(T-1)/(T+a).
```

Solving `C=1/8` gives unique

```text
T=(8+a)/7>1.
```

**Proved.** At this source-defined gauge, child energy is `a/64`, Gamma complement is `63a/64`,
and primitive Gamma/co-Poisson term plus both channels is exactly zero.

### Conjecture 3 — Gamma energy match lifts to amplitude and operator identity

Corpus's archimedean cyclic characteristic `gamma(t)` satisfies

```text
gamma(t)^4+tanh(t)^2=1.
```

At `t=artanh(1/8)`, positivity selects

```text
gamma(t)^2=sqrt(63)/8=d.
```

**Proved.** The Gamma-defined continuous linear defect operator `gamma(t)^2 I` equals P-G105's
Julia defect operator `d I`. Its co-graph pivots equal P-G105B's physical even-co-Poisson pivot and
P-G105C's half-line feature pivot exactly.

## Paper proof

For `a>0`, substitute `T=(8+a)/7`:

```text
(T-1)/(T+a)=((1+a)/7)/(8(1+a)/7)=1/8.
```

The existing Pythagorean prime-cell budget gives

```text
child=a C^2=a/64,
Gamma complement=a(1-C^2)=63a/64.
```

At `t=artanh(C)`, `tanh(t)=C`; hence `gamma(t)^4=63/64`. Both `gamma(t)^2` and Julia defect `d` are
nonnegative and have square `63/64`, so they are equal. Scalar multiplication by equal real
coefficients gives equality of defect operators. Substitution into co-graph definitions gives both
pivot equalities. `QED`

## Novelty and anti-theatre audit

Hyperbolic Pythagorean identity is standard. New route-specific result is simultaneous exact
calibration of corpus's literal prime-cell Gamma budget, Route-P fourth-depth contraction, and
Julia operators:

```text
T=(8+a)/7
  -> C=1/8
  -> gamma(artanh C)^2=sqrt(63)/8
  -> Gamma defect operator = Julia defect operator
  -> Gamma co-graphs = P-G105B/P-G105C pivots.
```

No Xi zero, target holonomy, scalar fitting, or RH premise occurs. This closes Gamma-cyclic
coefficient/operator provenance. It does not yet prove Stokes orientation, cofinal gauge sewing, or
Xi determinant identity.

## Formal status

Lean proves unconditionally:

- positivity of running odds and forced thermal ratio;
- exact Cayley coordinate `1/8`;
- child `1/64` and Gamma complement `63/64` budgets;
- Gamma cyclic amplitude square and equality with Julia defect;
- equality of Gamma and Julia defect continuous linear maps;
- equality of physical and half-line Gamma/Julia co-graph pivots;
- exact finite prime-cell Ward identity and combined capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Strongest positive survivor

Gamma cyclic channel is source-identified exactly. Next audit must compare this universal channel
with literal joint-depth Xi-landing co-source before using P-G105C's Kronecker law. P-G105E performs
that test and finds prime-log operator-valued, not scalar, relation.

## Log

- 2026-08-16 — P-G105D source gauge, Gamma--Julia amplitude/operator identity, and both co-graph
  equalities paper-proved and formalized.
