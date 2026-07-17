# Finite-generator differential escape boundary

- **ID:** `finite-generator-differential-escape-boundary`
- **Stage:** 3-formalized
- **Type:** EXACT POSITIVE BOUNDARY / CORPUS BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [PARENT DIFFERENTIAL ALGEBRA] [NOT NEW SCIENCE]`
  `[NOT AN RH RESULT]`
- **Source:** research programme 5 successor from
  `../../5-failed/operator-presentation-bounded-innovation-stabilization.md`
- **Statement:** A finite rational state packet whose generators differentiate back into that
  packet contains only differentially algebraic observables; consequently, a packet containing an
  HT observable has a generator whose derivative escapes.

## Exact theorem

Let `F -> E` be an extension of characteristic-zero differential fields, let `I` be finite, and
let `s : I -> E`.  Put

```text
S = F(s_i : i in I) <= E.
```

Assume

```text
D(s_i) in S    for every i in I.                            (1)
```

Then:

```text
D(S) subset S,                                               (2)
trdeg_F S < aleph_0,                                         (3)
every x in S is differentially algebraic over F.             (4)
```

Equivalently, if `x in S` is hypertranscendental over `F`, then

```text
there exists i in I with D(s_i) notin S.                     (5)
```

No shift, `q`-difference, Mahler, transition, strictness, or finite-presentation hypothesis is
needed.  Such data become relevant only if they prove `(1)` or its linear analogue.

## Paper proof

The derivative obeys the base rule, addition rule, Leibniz rule, and inverse rule

```text
D(a^(-1)) = -a^(-2) D(a).
```

Starting from `(1)`, induction through the ordinary field-adjoin construction therefore proves
`(2)`.  Since `I` is finite and `S` is generated as a field by `s(I)`, its ordinary transcendence
degree over `F` is finite, proving `(3)`.  The finite-algebraic-state elimination theorem then gives
`(4)`: all derivatives of `x` remain in the finite-transcendence-degree field `S`, so a finite
subset is algebraically dependent and yields a nonzero algebraic differential equation for `x`.
Taking the contrapositive proves `(5)`.  Every dependency is explicit and there is no open core.

## Why this is the maximal clean successor

The theorem says exactly what "bounded total differential innovation" must mean at nonlinear state
level: not a bound on how much each depth adds, and not finite presentation, but actual closure of a
finite-transcendence state field under the derivation.  Gamma shows that bounded per-depth
innovation and a finite compatible shift presentation do not imply this closure.

The linear strengthening is deliberately not conflated with this theorem.  To force holonomicity,
one needs a finite-dimensional derivative-invariant **linear** state, not merely the finite
transcendence nonlinear state above.  The project already proves that sibling in
`FiniteObservableKoopmanBoundary.lean`.

## Corpus dependency map

- `DifferentialIndependence.lean`: `DerivationClosed` and field-adjoin induction patterns.
- `DifferentialAdjoinFiniteTrdeg.lean`: finite-transcendence differential descent.
- `FiniteAlgebraicStateBoundary.lean`:
  `differentialAlgebraicOver_of_mem_derivationClosed_finiteTrdeg`.
- `FiniteObservableKoopmanBoundary.lean`: the separate linear/holonomic boundary.
- `HypertranscendentalObservableNet.lean`: HT forces every finite jet-field inclusion to be strict.

The only missing Lean surface is the finite-generator closure lemma and its escape contrapositive;
the differential-elimination endpoint already exists.

## Novelty and significance

This is standard rational-vector-field differential algebra, not new scientific knowledge.  Its
value is exact programme control: it prevents future work from treating finite presentations,
bounded increments, or strict maps as substitutes for derivation closure, and exposes the one
load-bearing hypothesis a source-specific operator theorem must establish.

## Lean theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/FiniteGeneratorDifferentialEscape.lean`.

- `adjoin_range_trdeg_lt_aleph0`
- `derivationClosed_adjoin_range_of_deriv_mem`
- `differentialAlgebraicOver_of_mem_finiteGeneratorState`
- `exists_generator_deriv_escape_of_hypertranscendentalOver`

## Gates

- [x] 0 -> 1: exact claim and falsifier boundary identified
- [x] 1 -> 2: dependency-closed paper proof complete
- [x] internal theorem surface audited before formalization
- [x] parent-theory / significance verdict assigned
- [x] 2 -> 3: unconditional Lean theorem batch
- [x] targeted touched-file check
- [x] touched-slice formal lint and axiom audit

## Log

- 2026-07-17 -- Created directly in Stage 2 after the programme-5 hostile audit.  The statement is
  a complete classical bridge and the exact positive residue of the failed headline.
- 2026-07-17 -- Promoted to Stage 3 after direct cached compilation.  `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The project lint reports no proof debt or
  reachability defect for this module; its nonzero repository-wide exit is an unrelated pre-existing
  umbrella-reachability baseline.
