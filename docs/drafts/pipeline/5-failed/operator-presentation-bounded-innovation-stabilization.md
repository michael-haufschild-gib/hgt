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

The exact positive replacement is a four-part boundary, split into dependency-closed cards:

1. `../3-formalized/not_new_scientific_knowledge/finite-generator-differential-escape-boundary.md`:
   finite nonlinear rational state closed under differentiation forces DA;
2. `../3-formalized/not_new_scientific_knowledge/finite-linear-state-differential-escape-boundary.md`:
   finite linear derivative state forces an explicit scalar linear ODE;
3. `../3-formalized/not_new_scientific_knowledge/bounded-finite-rank-submodule-stabilization.md`:
   a monotone finite-rank chain with bounded total rank stabilizes;
4. `../3-formalized/not_new_scientific_knowledge/mixed-fundamental-solution-flatness.md`:
   an actual common fundamental solution forces the mixed flatness identity.

These are the maximal generic consequences.  None uses presentation size or bounded per-depth
increments as a substitute for the relevant closure or total-rank hypothesis.

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

More generally, for an `m`-tuple `a` and

```text
H_a(n) = trdeg_K K(D^j a_i : i <= m, j <= n),
```

one always has `0 <= H_a(n+1)-H_a(n) <= m`.  Thus a uniform per-stage innovation bound is automatic
for every fixed finite tuple.  It cannot be the load-bearing stabilization hypothesis.

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

## The exact established linear mixed phase

The strongest correct cross-language theorems require an actual linear operator equation, not an
abstract finite presentation.

- Adamczewski--Dreyfus--Hardouin, Theorem 1.2, prove in their exact shift, `q`-difference, and
  Mahler Laurent/Puiseux settings that a solution of a nontrivial linear difference equation is
  either in the base field or hypertranscendental.  Thus **linear difference presentation plus
  DA implies base-field membership** there.  Their Theorem 1.3 treats simultaneous linear
  equations: `https://arxiv.org/abs/1910.01874`.
- Schaefke--Singer classify consistent pairs of linear differential and difference systems by
  reduction to normal forms: `https://arxiv.org/abs/1605.02616`.
- Dreyfus treats arbitrary reducible rational shift systems: a meromorphic solution vector whose
  coordinates are differentially algebraic is constrained to a periodic--rational--exponential
  ring, rather than being governed by presentation size alone:
  `https://arxiv.org/abs/2212.00388`.
- The elliptic difference setting has its own parameterized-Galois classification and cannot be
  inferred formally from the rational-shift theorem: `https://arxiv.org/abs/2409.10092`.

These are already genuine stabilization/phase theorems in specified categories.  The generic
programme cannot weaken their operator and base-field hypotheses to “finite type” without becoming
false.

## Stronger conjecture attacked

The first stronger proposal was:

> For a finite-rank difference module, Kolchin differential type zero of the parameterized
> difference-Galois group forces a filtration whose semisimple quotients are projectively
> isomonodromic and whose extension classes are annihilated by nonzero operators in `C[D]`.

This is **not promoted**.  Under its canonical linear-differential-algebraic-group reading it is
already parent structure; under the literal `C[D]`-torsion reading it is not even invariantly
defined unless differential lifts of the extension objects are supplied.

- Cassidy--Singer's Jordan--Hoelder theory classifies the almost-simple differential algebraic
  factors; the differential-type-zero noncommutative factors are constant-group phenomena:
  `https://singer.math.ncsu.edu/papers/Jordan_Hoelder.pdf`.
- Unipotent one-dimensional factors are controlled by additive differential algebraic groups
  `ker L`, which is exactly the nonzero-operator structure the proposed torsion clause rediscovered.
- Minchenko--Ovchinnikov--Singer prove a stronger finite-prolongation result: for a linear
  differential algebraic group, all representations are generated by a finite prolongation level
  (Proposition 4.3.3): `https://singer.math.ncsu.edu/papers/1304.2693.pdf`.
- Hardouin--Singer already identify flatness with conjugacy to constants in the exact integrable
  regime, while Arreche--Singer show that projective integrability is a genuinely weaker phase:
  `https://arxiv.org/abs/1608.00015`.  Rank-one `q`-theta-type systems prevent silently replacing
  projective integrability by full integrability.

Thus there is no surviving generic reducible-module conjecture here.  A future theorem must begin
with a specified source and a specified parameterized Galois group, then identify an obstruction
not already captured by differential algebraic group structure or finite prolongation.  Without
those data, “classify failure of flatness” is a research topic, not a well-posed conjecture.

## A complete one-dimensional mixed-state phase theorem

There is one clean geometric synthesis which explains why the nonlinear DA phase remains broader
than the holonomic phase.  Let `C` be a smooth projective connected curve over an algebraically
closed characteristic-zero field, let `v` be a nonzero regular vector field, and let `sigma` be an
infinite-order automorphism with `sigma_* v = v`.  Then `genus(C) <= 1`, and exactly two geometric
state types occur:

| Curve | Differential state | Compatible infinite-order automorphism |
|---|---|---|
| `P^1` | `v = (a + bx + cx^2) d/dx` (Riccati/projectively linear) | a projective transformation preserving `v` |
| elliptic curve | a translation-invariant vector field | translation by a nontorsion point |

Proof: a nonzero global section of `T_C` forces `deg(T_C)=2-2g >= 0`, so `g <= 1`.  On `P^1`, global
vector fields are precisely the quadratic polynomial fields displayed above.  On an elliptic
curve, write `sigma=t_P o u` with `u` fixing the origin.  Preservation of the nonzero invariant
vector field forces the differential of `u` to be one, hence `u=id`; infinite order then says that
`P` is nontorsion.

This theorem is classical, not a novelty claim, but it is a significant positive phase statement.
Riccati states such as `tan` and elliptic states such as the Weierstrass pair `(wp,wp')` are
finite nonlinear algebraic states with compatible translations, yet need not be holonomic.  They
show geometrically why “finite mixed state” can force DA without forcing a finite linear state.

## Positive phase diagram

| Hypothesis actually imposed | Exact consequence | Status |
|---|---|---|
| bounded increment at each jet depth | none; Gamma has increment one and is HT | falsified |
| bounded total jet transcendence degree | differential algebraicity | classical / Kolchin |
| finite derivative-invariant linear span | holonomicity | classical / differential module |
| finite nonlinear rational state closed under `D` | differential algebraicity of every state observable | classical; project successor |
| monotone finite-dimensional linear states with bounded total rank | eventual stabilization | classical; project successor |
| common invertible solution of `sigma(Y)=AY`, `D(Y)=BY` | `D(A)+AB=sigma(B)A` | elementary necessity; project successor |
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
- `[SIGNIFICANCE -- POSITIVE CORPUS BOUNDARY]` The nonlinear escape, linear escape, total-rank
  stabilization, and actual-solution flatness interfaces tell every future source theorem exactly
  which hypothesis it must establish and exactly what an HT source must violate.
- `[FIELDS VERDICT]` No Fields-scale theorem is present.  The generic reducible-group strengthening
  collapses into parent structure; only a source-specific obstruction could reopen this direction.
- `[RH BOUNDARY]` No zeta input and no RH conclusion occurs.

## Gates

- [x] inherited statement made exact enough to attack
- [x] internal corpus audit completed before new formal work
- [x] differential-algebra, D-finite, Ore, and mixed-operator parent theories checked
- [x] explicit natural HT falsifier identified
- [x] bounded-total and bounded-increment meanings separated
- [x] stronger parameterized-Galois conjecture attacked and withheld from promotion
- [x] proposed generic Galois strengthening killed by exact parent results
- [x] one-dimensional mixed-state phase theorem isolated as significant classical residue
- [x] four maximal generic positive successors proved on paper
- [x] positive successors Lean-formalized and moved to Stage 3

## Log

- 2026-07-17 -- Programme 5 retired as a general research headline.  The exact positive
  finite-generator escape theorem was split into its own dependency-closed card before Lean work.
- 2026-07-17 -- The stronger parameterized-Galois filtration conjecture was retired after the
  differential-algebraic-group and finite-prolongation audit.  Three further generic corpus
  interfaces and the complete one-dimensional geometric phase classification were retained.
- 2026-07-17 -- The four maximal generic positive successors passed direct cached Lean compilation
  and `#print axioms`, and were promoted to Stage 3.  No source-specific conjecture is well-posed
  without an actual operator system or function family beyond the programme's generic hypotheses.
