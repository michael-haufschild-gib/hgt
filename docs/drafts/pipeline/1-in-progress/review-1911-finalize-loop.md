# Review-1911 finalize loop

Goal: every open module in docs/reports/review-1911/finalize.md checked, its dependency oleans built, and wired into its umbrella.

Procedure: topological order over the listed modules plus the three unlisted dependency oleans
(`RepresentationLifting/KTheory/PermutationVirtualFreeness`, `InfiniteRankWeilTheory/TheRankBarrier`,
`arithmetic-positivity-theory/Jensen/XiStrictRoots`). A module imported by another listed module is built with
`-o/-i`; every other module is checked. A passing module is wired into its umbrella (the top-level programme file;
`HTGeometry/DispersivePDE/Applications.lean` for the dispersive PDE modules).

## Status

| Module | Status |
| --- | --- |
