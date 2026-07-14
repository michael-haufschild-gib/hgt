# Ising cavity rapidity and audio-scattering cascade

- **ID:** `ising-cavity-rapidity-audio-cascade`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [FORMALIZATION]`
- **Source:** special-relativistic velocity addition, passive wave-digital/lattice scattering, Schur recursion, and the formal prime Ising cavity map
- **Statement:** The scalar Ising cavity maps form the same Möbius semigroup as normalized collinear velocities and real lossless reflection coefficients.  Serial cavity sections collapse to one effective coupling, and the zero-field prime-tree partition has an explicit positive edge-product normalization.

## Candidate competition

1. **Positive-real/scattering Cayley equivalence.**  Directly useful to Herglotz and passive-response routes, but much of its scalar content is already present in `CayleySchur` and `PrimeCayleyHalfPlane`.
2. **All-pass group-delay/Poisson identity.**  It may provide boundary orientation, but differentiating tree phases introduces a larger analytic dependency and does not immediately simplify a current theorem.
3. **Rapidity/reflection cascade.**  The exact law

   `T_c(T_d(r)) = T_((c+d)/(1+cd))(r)`, for `norm r < 1`,

   collapses serial cavity sections now.  At the common zero-field value of all centered prime fields it yields a closed edge-product formula for every finite tree, giving the source-comparison route a canonical nonzero normalization.  This is the selected bridge.

## Proof targets

- [x] Define the effective coupling `(c+d)/(1+cd)` and prove it remains in `[0,1]`.
- [x] Prove the exact cavity cascade identity on the physical open disk.  The unrestricted statement
  is false for Lean's totalized division at a pole, so the disk condition is mathematically and
  formally necessary.
- [x] Define the product of `(1+c_e)` over all tree edges.
- [x] Prove `treePartition (fun _ => 1) T = 2 * edgeFactorProduct T`.
- [x] Prove every centered prime field equals `1` at `z=0` and therefore
  `primeIsingTreePartition T 0 = 2 * edgeFactorProduct T > 0`.
- [x] Define the unit-central normalization, prove it changes no zero, prove it entire, and prove
  locally uniform convergence of these normalized trees to `XiC` implies RH.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/IsingCavityRapidityAudioCascade.lean` contains:

- `FerromagneticCoupling.compose` and `cavityTransfer_compose`;
- `treeEdgeFactorProduct_pos` and `treeConditionalWeights_one`;
- `treePartition_one`, `centeredPrimeLeeYangField_zero`, and `primeIsingTreePartition_zero`;
- `centralNormalizedPrimeIsingTreePartition_zero` and
  `centralNormalizedPrimeIsingTreePartition_eq_zero_iff`; and
- `riemannHypothesis_of_centralNormalizedPrimeIsingTreePartition_tendstoLocallyUniformly`.

The target and `RHTower` umbrella builds pass.  The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; the formal lint and diff checks pass.

## Open core after the bridge

The cascade law simplifies source-selected unary sections and fixes the central normalization, but it does not construct the cofinal source tree or prove locally uniform convergence to `E * XiC`.

## Physics and audio provenance

- A. Einstein, *Zur Elektrodynamik bewegter Koerper*,
  <https://doi.org/10.1002/andp.19053221004>;
- A. Fettweis, *Wave Digital Filters: Theory and Practice*, Proceedings of the IEEE 74 (1986),
  270--327;
- E. J. Beltrami, *Linear dissipative systems, nonnegative definite distributional kernels, and
  the boundary values of bounded-real and positive-real matrices*,
  <https://doi.org/10.1016/0022-247X(67)90118-7>;
- L. Baratchart, P. Enqvist, A. Gombani, and M. Olivi, *Surface Acoustic Wave Filters, Unitary
  Extensions and Schur Analysis* (2003).

## Log

- 2026-07-14 -- Created after the audio-engineering scope was added and the rapidity/scattering cascade survived comparison with the already-saturated scalar Cayley bridge and the more expensive group-delay derivative route.
- 2026-07-14 -- Formalized the cascade law, strict edge-product normalization, unit-central tree family, zero preservation, entireness, and normalized locally uniform RH capstone; promoted to Stage 3 after verification.
