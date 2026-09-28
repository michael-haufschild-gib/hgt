# Local compatibility changes

The original source hashes are recorded in `upstream-manifest.json`.

- `lakefile.toml`: use the parent project's Lean/mathlib 4.32.2 dependency; disable the
  upstream umbrella as a default target because only the declared endpoint closure is present.
- `DifferentialGeometry/Bundle/TangentSpace.lean`: expand `mvfderiv` and use the available
  `MDifferentiableAt.mfderiv` chart formula; the newer `.mvfderiv` lemma is absent locally.
- `DifferentialGeometry/Tensor/Alternating/Shuffle/Derivative.lean`: close two reflexive
  permutation-sign goals explicitly after simplification on mathlib 4.32.2.
- `DifferentialGeometry/Tensor/Multilinear/Bundle/Defs.lean`: mark the additive-monoid and
  module instance aliases reducible so the local elaborator can compare inherited structures.
- `DifferentialGeometry/Tensor/Multilinear/Bundle/Fiber.lean`: construct an additive-group
  instance extending the displayed bundle monoid; preserve that group in the normed
  structure and replace its metric topology using the proved `topology_eq`. Supply the
  matching normed-space structure and explicitly import bounded-convergence topology.
  This preserves the topology and norm while aligning the structure projections needed
  by continuous currying. All original theorem statements remain present.
