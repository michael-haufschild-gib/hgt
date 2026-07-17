# Bounded operator-presentation innovation does not force DA or holonomicity

- **ID:** `operator-presentation-bounded-innovation-stabilization`
- **Stage:** 5-failed
- **Type:** RETIRED RESEARCH PROGRAMME / EXACT PHASE BOUNDARY
- **Scientific status:** `[FALSE AS STATED] [CLASSICAL AFTER REPAIR] [POSITIVE CORPUS SUCCESSOR]`
  `[NOT AN RH RESULT]`
- **Source:** `../../../reports/rh-status-1707.md`, research programme 5
- **Statement:** Bounded differential innovation per depth, a finite cross-operator presentation,
  and strict compatible transition maps force differential algebraicity or holonomicity.

## Terminal verdict

The statement is false if "bounded innovation" means a uniform bound on the amount added at each
depth.  It becomes classical differential algebra if it means a uniform bound on the total jet
transcendence degree, and classical differential-module theory if it means a uniform bound on the
total derivative span.  Finite presentation and strictness do not bridge the gap.

The exact positive replacement is the finite-generator escape theorem in
`../2-fully-proven/not_new_scientific_knowledge/finite-generator-differential-escape-boundary.md`:
if a finite rational state packet is closed under differentiation on its generators, every
observable in the packet is differentially algebraic.  Therefore an HT observable in such a
packet forces at least one generator derivative to escape the packet.  The linear sibling is the
already formalized finite observable Koopman boundary.

## Exact hostile falsifier

Let

```text
K = C(z),
J_n = K(Gamma, Gamma', ..., Gamma^(n)),
sigma(f)(z) = f(z+1).
```

The shift equation

```text
sigma(Gamma) = z Gamma
```

is a finite first-order cross-language presentation.  Differentiating it gives

```text
sigma(Gamma^(n)) = z Gamma^(n) + n Gamma^(n-1),
```

so every finite jet field is preserved by the shift and the inclusions are compatible.  Holder's
theorem, in the Hardouin--Singer parameterized difference-Galois form, says that Gamma satisfies no
nonzero algebraic differential equation.  Hence its jets are algebraically independent over
`C(z)`, and

```text
trdeg_K J_n = n+1.
```

Every transition adds exactly one transcendence degree: innovation per depth is bounded by one,
the finite shift presentation persists at every depth, and the transitions are strict.  Yet Gamma
is hypertranscendental, hence neither differentially algebraic nor holonomic.  This meets the
headline hypotheses in their strongest natural jet-field reading and falsifies both advertised
conclusions.

Primary source: C. Hardouin and M. F. Singer, *Differential Galois theory of linear difference
equations*, Math. Ann. 342 (2008), 333--377,
`https://singer.math.ncsu.edu/papers/differential_for_difference.pdf`, especially Corollary 3.4.

## Why the obvious repairs are not new

### Bounded total algebraic innovation

For

```text
H_x(n) = trdeg_K K(x, Dx, ..., D^n x),
```

the following are equivalent in one derivation:

1. `x` is differentially algebraic over `K`;
2. `H_x(n)` is bounded;
3. the ascending jet-field chain eventually stabilizes.

The forward implication is differential elimination via a minimal differential polynomial and its
nonzero separant; the reverse implication is immediate algebraic dependence of a finite jet.  This
is the ordinary Kolchin dimension-zero phase, not a new cross-language theorem.  The project
already formalizes the HT strict-mono direction in `HypertranscendentalObservableNet.lean` and the
finite-transcendence state boundary in `FiniteAlgebraicStateBoundary.lean`.

### Bounded total linear innovation

If `x, Dx, D^2x, ...` span a finite-dimensional vector space over `K`, linear dependence supplies a
nonzero scalar linear differential equation.  This is the standard D-finite criterion, already
formalized in `FiniteObservableKoopmanBoundary.lean`.  Differential algebraicity alone cannot be
upgraded to holonomicity: `tan z` satisfies `y'=1+y^2` but is not D-finite over `C(z)` because it has
infinitely many finite poles, while a rational-coefficient linear ODE has only finitely many finite
singularities.  See R. P. Stanley, *Differentiably finite power series*, European J. Combin. 1
(1980), 175--188, DOI `10.1016/S0195-6698(80)80051-5`.

### Finite presentation

Finite presentation is too weak in both the nonlinear and linear languages.

- Levin's multivariate difference-differential dimension polynomial already measures joint jet
  and orbit growth for finitely generated mixed field extensions:
  `https://arxiv.org/abs/1207.4757`.
- In Ore/Weyl module language, finitely presented modules can have maximal, nonholonomic dimension;
  finite presentation is not the finite-rank localized quotient condition.
- Adamczewski--Dreyfus--Hardouin prove that, in their Laurent/Puiseux shift, `q`-difference, and
  Mahler fields, a solution of a nontrivial linear difference equation is already either in the
  base field or hypertranscendental: `https://arxiv.org/abs/1910.01874`.  Thus the intended
  cross-language rigidity is stronger and already classified in those precise settings.

### Strict transitions

Strictness is not stationarity.  A strict nested system may grow forever, as Gamma's jet fields do.
For inverse systems, even the one-generator, one-relation quotients

```text
k[t]/(t^(n+1)) ->> k[t]/(t^n)
```

are strict and never eventually isomorphic.  Uniform finite length or a uniform total dimension
bound forces stabilization; strictness by itself does not.

## Stronger conjecture attacked

The first stronger proposal was:

> For a finite-rank difference module, Kolchin differential type zero of the parameterized
> difference-Galois group forces a filtration whose semisimple quotients are projectively
> isomonodromic and whose extension classes are annihilated by nonzero operators in `C[D]`.

This is **not promoted**.  Its simple-group and rank-one cases are already the Hardouin--Singer
integrability and telescoper theorems; projective integrability is treated by
Arreche--Singer (`https://arxiv.org/abs/1608.00015`); and in one derivation the linear-operator
description of differential algebraic subgroups of additive groups makes the proposed torsion
clause dangerously close to parent structure.  No novelty claim survives without a precise new
reducible-module obstruction beyond those classifications.

The genuine open core, if this direction is resumed, is therefore not "finite presentation forces
stabilization."  It is a source-specific classification of the failure of a flat mixed connection

```text
sigma(B) = A B A^(-1) + D(A) A^(-1)
```

inside reducible parameterized difference modules.  Hardouin--Singer already prove that this flat
connection is exactly the constant-group/integrable condition and that, for simple noncommutative
ordinary Galois group, any differential-dimension drop forces it.  A new programme must isolate a
reducible extension invariant not already contained in parameterized Galois cohomology.

## Positive phase diagram

| Hypothesis actually imposed | Exact consequence | Status |
|---|---|---|
| bounded increment at each jet depth | none; Gamma has increment one and is HT | falsified |
| bounded total jet transcendence degree | differential algebraicity | classical / Kolchin |
| finite derivative-invariant linear span | holonomicity | classical / differential module |
| finite nonlinear rational state closed under `D` | differential algebraicity of every state observable | classical; project successor |
| finite linear difference presentation plus DA in the standard ADH fields | base-field membership, hence rationality | literature |
| flat mixed connection for a finite-rank difference system | a compatible linear differential system | literature / integrability |

The significant content is the phase boundary: hypertranscendence detects failure of finite
derivation-closed state, whereas nonholonomicity detects failure of finite **linear** differential
state.  Neither failure is detected by presentation size or categorical strictness.

## Anti-theatre and significance gate

- `[ANTI-THEATRE -- PASS]` The ambiguous headline is retired rather than repaired by adding
  categorical vocabulary.
- `[NOVELTY -- NO]` The correct DA and D-finite implications are parent differential algebra and
  differential-module theory.
- `[SIGNIFICANCE -- POSITIVE CORPUS BOUNDARY]` The exact generator-escape contrapositive is a useful
  missing interface: it tells every future operator presentation exactly what must be proved to
  obtain DA and exactly what an HT source must violate.
- `[FIELDS VERDICT]` No Fields-scale theorem is present.  The reducible mixed-integrability
  classification is the only plausible hard successor, and its priority remains unverified.
- `[RH BOUNDARY]` No zeta input and no RH conclusion occurs.

## Gates

- [x] inherited statement made exact enough to attack
- [x] internal corpus audit completed before new formal work
- [x] differential-algebra, D-finite, Ore, and mixed-operator parent theories checked
- [x] explicit natural HT falsifier identified
- [x] bounded-total and bounded-increment meanings separated
- [x] stronger parameterized-Galois conjecture attacked and withheld from promotion
- [x] maximal positive finite-generator escape theorem proved on paper
- [ ] positive successor Lean-formalized and moved to Stage 3

## Log

- 2026-07-17 -- Programme 5 retired as a general research headline.  The exact positive
  finite-generator escape theorem was split into its own dependency-closed card before Lean work.
