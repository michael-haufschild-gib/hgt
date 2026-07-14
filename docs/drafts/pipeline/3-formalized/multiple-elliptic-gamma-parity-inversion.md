# Multiple elliptic-gamma parity inversion

- **ID:** multiple-elliptic-gamma-parity-inversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** direct transfer of the elliptic-gamma physics inversion to the existing all-order HTGeometry hierarchy
- **Statement:** Reflection through the sum of all additive nome parameters swaps the forward and backward multiple elliptic-gamma products; the genuine product is inverted in even rank and fixed in odd rank, while its logarithmic kernel transforms by `(-1)^rank`.

## Goal

Apply the newly formalized physics inversion atom to the rest of the Lean corpus rather than leaving
it specialized to the two-nome elliptic gamma.  The resulting theorem simplifies reflected all-order
values, transports regularity hypotheses, and closes a reflected log-derivative theorem using the
existing multiple-product analytic bridge.

## Gates

- [x] 0 → 1 in-progress: the all-order forward/backward atoms and parity-dependent product inspected; exact parity law derived; direct consumers identified
- [x] 1 → 2 fully-proven: coordinate reflection and pointwise factor swap prove the parity law without an open dependency
- [x] 2 → 3 formalized: direct module check, axiom audit, lint, and diff integrity pass
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics source and transfer

The rank-two inversion is the unitarity reduction used for elliptic-gamma Boltzmann weights in
solvable lattice models.  Multiple elliptic gamma functions originate in theoretical-physics
partition-function and modularity constructions; this result transfers that inversion atom to the
repository's existing finite-nome hierarchy.

- V. P. Spiridonov, *Elliptic beta integrals and solvable models of statistical mechanics*,
  arXiv:1011.3798.
- A. P. Kels, *Quasi-classical expansion of the star-triangle relation and integrable systems on
  quad-graphs*, arXiv:1602.07076.
- L. Tizzano and J. Winding, *Multiple sine, multiple elliptic gamma functions and rational cones*,
  arXiv:1502.05996.

## Formalized theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaInversion.lean`

- `multipleEllipticGammaCoordinate_reflection` identifies the all-order additive reflection.
- `multipleEllipticGammaForwardArgument_reflection` and
  `multipleEllipticGammaBackwardArgument_reflection` exchange the source atoms.
- `multipleEllipticGammaLogSummand_reflection`,
  `multipleEllipticGammaLogKernel_reflection`, and
  `multipleEllipticGammaAdditiveLogKernel_reflection` prove the uniform `(-1)^rank` law.
- `multipleEllipticGammaForwardFactor_reflection` and
  `multipleEllipticGammaBackwardFactor_reflection` exchange individual entire factors.
- `multipleEllipticGammaForwardProduct_reflection` and
  `multipleEllipticGammaBackwardProduct_reflection` exchange the all-order entire products.
- `multipleEllipticGammaProduct_reflection` gives reciprocal reflection in even rank and fixed
  reflection in odd rank from the actual parity-dependent product definition.
- `multipleEllipticGammaProducts_reflection_ne_zero` transports both regularity obligations.
- `multipleEllipticGammaProduct_mul_reflection_of_even` is the even-rank unitarity law.
- `logDeriv_multipleEllipticGammaProduct_reflection` applies the new relation to the existing
  analytic product bridge and discharges reflected-point hypotheses.

## Verification

- Direct Lean check of `MultipleEllipticGammaInversion.lean`: passed.
- `#print axioms` on the coordinate, product, kernel, unitarity, and analytic log-derivative laws:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint`: passed.
- `git diff --check`: passed.
- No numerical computation and no full or umbrella build was run.

## Proof

[PROVED HERE] Expanding the uncentered coordinate shows that reflection
`z ↦ (∑ i,τ i)-z` sends `x` to `(∏ i,p i)/x`.  The identity
`∏ i,p_i^(n_i+1)=(∏ i,p_i^n)(∏ i,p_i)` then exchanges every forward argument with
its backward partner.  Thus all factors and their `tprod`s are exchanged.  When the nome count is
even, the genuine product is the forward/backward quotient and is inverted; when it is odd, it is
their product and commutativity fixes it.  The logarithmic summand already weights the backward atom
by `(-1)^rank`; exchanging the two atoms therefore multiplies the summand, and hence its `tsum`, by
that same sign.  The product exchanges also turn original nonvanishing into reflected nonvanishing,
so the existing analytic log-derivative theorem applies at reflection without extra hypotheses.

## Log

- 2026-07-14 — formalized as the mandatory direct-corpus application of the rank-two inversion;
  imported into the HTGeometry umbrella and verified without a full build.
