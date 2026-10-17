# Finite-copy trains: extremal-pair tail rigidity

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** infinite-grid-tail-rigidity-2026-10-17.md
- **Scope:** Fourth certified package; independent BiScaleUncertainty.

## Exact target

For the actual source `G(u)=sum_{j=0}^m c_j f(u-jS)`, with nonzero endpoint coefficients,
derive a support threshold from the compact C² seed. Once adjacent copies are sufficiently
separated, the grid node nearest the total span `L=mS` forces `h_f(d(L))=0` and
`h_G(d(L))=0`, regardless of interior coefficient signs or cancellations. Conclude exact-grid
span impossibility and logarithmic nearest-grid energy cost, hence a lower bound proportional
to the full span for both base and train.

## Plan

1. Inspect finite-sum correlation APIs and audit the elementary extremal-pair mechanism.
2. Write a dependency-closed paper proof, including local preservation and train regularity.
3. Formalize actual finite translated sums and isolate their unique outermost pair.
4. Derive support bounds from source compactness in the final endpoint; audit Lean, axioms,
   imports, generated index, and lint. Count the connected result once.

## Boundaries

Common seed is essential to this argument: unrelated packet shapes have an extremal
cross-correlation, which need not equal positive seed mass. No claim about that class or
general polar sources is made. Interior difference collisions are allowed. The positive
survivor of the exact-span obstruction is a quantitative energy law for every finite train.
Current corpus search: `/tmp/infinite-grid-train-search.txt`.

## Paper and formalization state

Complete paper proof: `docs/reports/BiScaleUncertainty/FiniteCopyTailRigidity.md`.
The source-pure division-free endpoint also covers zero-mass seeds and needs only the detecting
ceiling-grid sample. Its proof and normalization boundary are recorded separately in the paper.
`FiniteTranslationTrains.lean` contains the general source expansion, regularity, local diagonal
preservation, and unique endpoint-pair identity. `FiniteCopyTailRigidity.lean` contains the
nearest-distance and full-span energy laws. Both leaves passed final direct `lake --old env lean` checks without diagnostics.
All 15 theorems occur in the generated API, umbrella imports are present, and formal lint passed.
The separate scratch audit passed for all 15 theorems, with only `propext`, `Classical.choice`,
and `Quot.sound`. Count advanced to 4/100; the parent objective remains active.
Owned logs: `/tmp/infinite-grid-train-{algebra,rigidity,axioms,index,lint}.log`.
