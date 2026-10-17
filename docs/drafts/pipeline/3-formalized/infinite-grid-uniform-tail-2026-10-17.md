# Shape-independent infinite-grid tail decay

- **ID:** infinite-grid-uniform-tail-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Independent BiScaleUncertainty; certified package 7/100.
- **Statement:** Bounded normalized Lévy energy and all logarithmic-grid zeros force uniform
  two-sided correlation decay for arbitrary compact C² sources, independently of support and shape.

## Plan and gates

- [x] Search current corpus; distinguish quadratic-collar and nonpositive-interval results.
- [x] Complete paper proof: `docs/reports/BiScaleUncertainty/InfiniteGridUniformTail.md`.
- [x] Formalize logarithmic modulus, grid sampling error, normalized tail, uniform family
  quantifiers, and decaying window integral in one leaf.
- [x] Check leaf with `lake --old env lean`; audit every theorem's axioms in scratch file.
- [x] Wire umbrella, regenerate API, run lint, record exact certification and remaining boundary.

## Certificate

`InfiniteGridUniformTail.lean`: ten public theorems plus one private normalization helper.
Leaf passed without diagnostics; all ten dependency audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. All ten API entries and umbrella import verified.
Logs: `/tmp/infinite-grid-uniform-tail-{leaf,axioms,index,lint}.log`.
Global lint reports four concurrent foreign modules missing umbrella reachability, named in
the paper. No owned lint error. The uniform modulus, tail, and window estimates count once.

## Insight and boundary

The singular energy supplies the missing common continuity modulus. Krein transports it to
every location, and the complete grid converts exponentially short sampling distances into
an inverse-square-root tail law. No common source, support radius, derivative bound, or copy
decomposition is assumed. This does not establish tightness of the cosh-weighted polar tail.

Search: `/tmp/infinite-grid-arbitrary-tail-search.txt`; useful source-only candidates,
older-generation coverage snapshot, semantic coverage unmeasured. No exhaustive external
novelty claim. Paper dependencies are already certified local theorems.
