# Elliptic-gamma inversion as a reflected-value eliminator

- **ID:** elliptic-gamma-inversion-unitarity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** physics transfer from elliptic-gamma solvable lattice models to the general HTGeometry product hierarchy
- **Statement:** In the repository's centered additive coordinate, reflection `z ↦ σ - z` swaps the forward and backward elliptic-gamma products, gives the unconditional reciprocal rewrite `Γ(σ-z)=Γ(z)⁻¹`, fixes the logarithmic kernel, and transports regularity to the reflected point.

## Goal

Add a source-general value relation, independent of zeta, that eliminates reflected elliptic-gamma
values and reflected logarithmic kernels throughout HTGeometry.  The theorem consumes the existing
product and log-kernel definitions, propagates regularity across reflection, and supplies direct
simplification lemmas rather than a physics-named wrapper.

## Gates

- [x] 0 → 1 in-progress: exact product involution identified; centered-coordinate convention checked symbolically; existing corpus searched; direct consumers named
- [x] 1 → 2 fully-proven: the factor swap is pointwise; `tprod` and `tsum` congruence give the product and kernel laws; quotient algebra gives inversion
- [x] 2 → 3 formalized: direct module check, axiom audit, formal lint, and diff integrity pass
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics source and transfer

Spiridonov's elliptic-beta-integral solution identifies elliptic-gamma Boltzmann weights with
star-triangle relations, superconformal indices, and Kramers-Wannier-type dualities.  Kels' review of
solvable edge-interaction models uses the normalized inversion law `W(α|a,b)W(-α|a,b)=1` as a
partition-function reduction.  The transferred algebraic atom is the elliptic-gamma inversion
`Γ(x;p,q) Γ(pq/x;p,q)=1`.

- V. P. Spiridonov, *Elliptic beta integrals and solvable models of statistical mechanics*,
  arXiv:1011.3798.
- A. P. Kels, *Quasi-classical expansion of the star-triangle relation and integrable systems on
  quad-graphs*, arXiv:1602.07076.

## Formalized theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/EllipticGammaInversion.lean`

- `ellipticThetaCoordinate_reflection_mul` and `ellipticThetaCoordinate_reflection` identify the
  correct centered additive involution `z ↦ σ-z`.
- `ellipticGammaForwardArgument_reflection`, `ellipticGammaBackwardArgument_reflection`, and
  `ellipticGammaLogSummand_reflection` prove the pointwise swaps.
- `ellipticGammaLogKernel_reflection` and
  `ellipticGammaAdditiveLogKernel_reflection` eliminate reflected kernel values.
- `ellipticGammaForwardProduct_reflection` and
  `ellipticGammaBackwardProduct_reflection` exchange the entire products.
- `ellipticGammaProduct_reflection` gives the unconditional reciprocal rewrite.
- `ellipticGammaProducts_reflection_ne_zero` discharges both reflected regularity hypotheses from
  the original pair.
- `ellipticGammaProduct_mul_reflection` is the regular-locus product-one, or unitarity, law.
- `logDeriv_ellipticGammaProduct_reflection` directly applies the new relations to the existing
  analytic product theorem and removes all reflected-point hypotheses.

## Verification

- Direct Lean check of `EllipticGammaInversion.lean`: passed.
- `#print axioms` on the product swaps, reciprocal/product-one laws, kernel reflection, and analytic
  log-derivative reflection: only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint`: passed.
- `git diff --check`: passed.
- No numerical computation and no full or umbrella build was run.

## Proof

[PROVED HERE] The coordinate identity
`x(τ,σ-z)x(τ,z)=ellipticNome(σ)ellipticNome(τ)` follows by expanding the two exponentials.  Thus
reflection sends the multiplicative variable to `pq/x`.  Expanding powers shows that this exchanges
each forward argument `p^(j+1)q^(k+1)/x` with the corresponding backward argument `p^j q^k x`.
Hence forward and backward factors, and then their `tprod`s, are exchanged.  Their quotient is
therefore inverted.  The same pointwise exchange fixes the sum of the two logarithmic atoms, so
`tsum` congruence fixes the full logarithmic kernel.  Finally the product swaps turn original
nonvanishing into reflected nonvanishing, allowing the existing log-derivative/product theorem to
be invoked at both points with no new hypotheses.

## Log

- 2026-07-14 — formalized and verified module-locally; imported into the HTGeometry umbrella.
