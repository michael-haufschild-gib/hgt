# Hedenmalm theta ordinary-L2 pre-quasi exclusion

- **ID:** `hedenmalm-theta-ordinary-l2-prequasi-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `HedenmalmSourceHilbertGramClosedGraphNoGo.lean`;
  `PreQuasiGelfandTwoSidedSingularDefect.lean`
- **Statement:** No nonzero momentum-symmetric theta-null Hilbert-Gram form on the full Schwartz
  source can be the positive embedding of even a pre-quasi-Gelfand pair over ordinary
  `L2(R)`.

## Goal

Close the apparent quasi-Gelfand escape from the ordinary-`L2` Hedenmalm nonclosability theorem.
The result is source-specific and unconditional. It does not prove RH or construct a positive
Hedenmalm form. It determines that replacing a continuous Gelfand embedding by a closed densely
defined embedding cannot preserve simultaneously:

1. ordinary Lebesgue `L2(R)` as middle Hilbert space;
2. the full Schwartz source core;
3. nonzero Hilbert-Gram positivity;
4. momentum symmetry; and
5. annihilation of the completed theta source.

## Exact statement

Let `Q` be a continuous sesquilinear form on complex Schwartz space, let `plus` and `minus` be
partial linear operators on ordinary `L2(R)`, and let `J` map Schwartz space linearly into
ordinary `L2(R)`. Call this a full-source ordinary-`L2` pre-quasi realization when:

```text
HilbertPreQuasiPair plus minus,
Q(u,v) = inner (J v) (J u),
Q is momentum-symmetric,
J(thetaSource) = 0,
J != 0,
every Schwartz vector belongs to domain(plus),
plus agrees with J on that full Schwartz core.
```

`[LEAN-PROVED]` No such realization exists.

Equivalently, under the first five clauses, either some Schwartz vector is excluded from the
positive embedding domain or the positive embedding disagrees with `J` somewhere on its admitted
Schwartz core.

## Internal frontier

`[CORPUS]` `hilbertGram_l2PartialOperator_not_closable` proves that any partial ordinary-`L2`
operator agreeing on the full Schwartz core with a nonzero momentum-symmetric theta-null
Hilbert-Gram realization is not closable.

`[CORPUS]` `HilbertPreQuasiPair.plus_closed` makes the positive embedding closed. Every closed
partial linear operator is closable.

`[CORPUS]` `preQuasi_quasi_iff_eq_canonicalNegative` classifies full quasi compatibility as
saturation by the canonical inverse-adjoint graph. The proposed theorem is stronger in scope:
it rules out the theta realization before quasi saturation, using only the pre-quasi closedness
clause.

No declaration found by the generated corpus search composes these source-specific and abstract
pre-quasi results.

## External frontier

`[LITERATURE]` Skrepek's quasi-Gelfand triples replace continuous dense embeddings by closed dense
embeddings and classify the resulting middle-space structure:

- Nathanael Skrepek, *Quasi Gelfand triples*, arXiv:2301.04610.

`[LITERATURE]` Hedenmalm's theta spectral proposal develops self-adjointness of the pair `(LD,L)`
rather than an ordinary bounded Hilbert operator:

- Haakan Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.

Neither source contains the actual-theta cyclic-null obstruction or the stated incompatibility
with a pre-quasi positive embedding on the full Schwartz core. This non-detection is not a novelty
claim; the theorem is a direct cross-theory consequence and is classified as a bridge.

## Hostile audit

- **Not RH:** no positivity of the actual Hedenmalm Bezoutian is proved.
- **Not a new Gelfand theory:** abstract pre-quasi classification already exists in corpus and
  literature.
- **Not merely the old nonclosability theorem restated:** new conclusion removes the suggested
  closed-embedding rescue category and identifies which architectural clause must fail.
- **No hidden source assumption:** theta source, Schwartz core, ordinary `L2` embedding, and
  pre-quasi closedness are fixed objects or explicit structural clauses.
- **Verdict:** `BRIDGE`. Worth formalizing because it closes a concrete representation choice,
  not because it advances RH.

## Complete paper proof

`[PAPER-PROVED]` Assume a full-source ordinary-`L2` pre-quasi realization exists. Apply
`hilbertGram_l2PartialOperator_not_closable` with target Hilbert space ordinary `L2(R)` and partial
operator `T=plus`. Its hypotheses are exactly Hilbert-Gram realization, momentum symmetry,
theta-source annihilation, nonzero `J`, full Schwartz-core domain, and agreement of `plus` with
`J`. Therefore `plus` is not closable.

But `HilbertPreQuasiPair plus minus` includes `plus_closed`, so `plus` is a closed partial linear
operator. A closed partial linear operator is closable by taking itself as its closed extension;
its graph is already equal to its topological closure. Thus `plus` is closable, contradiction.
No unresolved lemma or analytic premise remains.

## Positive survivor

The failure does not prohibit rigged methods. It forces an exact escape from the advertised
ordinary-`L2` full-source category. Any nonzero momentum-symmetric theta-null Hilbert-Gram
realization inside a pre-quasi pair must satisfy at least one of:

```text
some Schwartz vector is outside domain(plus),
or plus fails to realize J on an admitted Schwartz vector.
```

After restoring the other fixed clauses, viable architectures must therefore use a different
middle Hilbert topology, a genuinely restricted/source-selected test domain, or a non-Hilbert-Gram
singular boundary pairing. Merely changing `continuous embedding` to `closed embedding` is not
enough.

## Gates

- [x] 0 -> 1: well-posed, source-specific, corpus and literature audited
- [x] hostile verdict fixed as `BRIDGE`
- [x] complete dependency-closed paper proof
- [x] move to Stage 2
- [x] exact Lean theorem and positive-survivor theorem; both exported declarations have zero
  parameters and prove closed propositions
- [x] `lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaOrdinaryL2PreQuasiExclusion.lean`
- [x] `#print axioms` scratch audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] targeted final build:
  `lake build GaloisForLFunctions.RHTower.HedenmalmThetaOrdinaryL2PreQuasiExclusion`
- [x] formal lint attempted: new module clean; repository gate remains blocked by unrelated
  pre-existing unwired `Sieve`, `XiCenteredFlow`, and `HTGeometry` modules
- [x] umbrella wiring in `GaloisForLFunctions.RHTower`
- [x] move to Stage 3

## Log

- 2026-08-19 — conjecture frozen after the naive Schwartz/Gelfand replacement was found already
  represented in corpus; strengthened to exclude even pre-quasi closed embeddings over ordinary
  `L2` on the full actual theta source core.
- 2026-08-19 — hostile audit classified claim as a useful bridge; complete paper proof closed by
  composing pre-quasi closedness with the actual-theta arbitrary-Hilbert-target nonclosability
  theorem.
- 2026-08-19 — formalized
  `not_hedenmalmThetaOrdinaryL2PreQuasiRealization` and
  `hedenmalmThetaOrdinaryL2PreQuasi_sourceEscape`; source check and targeted module build passed.
  Corpus search indexes all new declarations. Axiom audit found only standard Mathlib axioms.
