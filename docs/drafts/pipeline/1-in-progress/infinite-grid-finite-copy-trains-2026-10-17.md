# Finite-copy trains: extremal-pair tail rigidity

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** infinite-grid-tail-rigidity-2026-10-17.md
- **Scope:** Fourth candidate package, not counted yet; independent BiScaleUncertainty.

## Exact target

For the actual source `G(u)=sum_{j=0}^m c_j f(u-jS)`, with nonzero endpoint coefficients,
derive a support threshold from the compact C² seed. Once adjacent copies are sufficiently
separated, the grid node nearest the total span `L=mS` should force `h_f(d(L))=0` and
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
