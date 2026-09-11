# Selberg: regularity and actual derived principal-series action

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Classical Maass eigenfunctions are smooth; actual compact principal-series translations differentiate to the spherical Harish-Chandra operators on finite K-types.

## Scope

Formalize the concrete new proof arguments from the corpus investigation. Reuse the existing full-energy identities, boundary decomposition, Schur theorem, Kloosterman identities, and infinite-degree scalar theorem. The level-uniform spectral inequality and unbounded-degree automorphic lifting remain unresolved mathematical inputs and must not be assumed in a purported unconditional conclusion.

## Proof chain

1. Localize a C2 solution of the planar equation `Δu = V*u` by arbitrary compact smooth cutoffs. Integration by parts proves the distributional cutoff identity, including every commutator term.
2. Existing planar Sobolev gain and smooth-representative results bootstrap every cutoff to every Sobolev order. Continuity identifies its smooth representative with the original function.
3. Specialize to `V(z) = -λ / im(z)^2` on the upper half-plane.
4. Extend the existing diagonal and rotation derivatives from single K-types to finite sums.
5. Conjugate the inverse diagonal flow by compact rotations. At angle π/4 the derivative is `i(E-F)`; together with `E+F` this recovers the noncompact generators. Derive the corresponding Casimir expression from existing operator identities.

## Validation constraints

No new axioms or unfinished proof terms. No heartbeat increases. Scratch checks via `lake env lean <file>`, one foreground Lean process at a time. Produce only needed dependency oleans. Final audit targets only the finished new modules; wire umbrellas without building them.

## Formal results

- `HTGeometry/PlanarLocalEllipticRegularity.lean`: arbitrary open planar domains, classical weak equation, full cutoff commutator, all local Sobolev orders, and pointwise smoothness in `PlanarElliptic.smooth_of_equation`.
- `RHTower/MaassCuspSmoothness.lean`: `IsMaassEigenfunction.contDiffOn` and `MaassCuspEigenform.contDiffOn` upgrade the original C2 definitions to C∞ without new assumptions.
- `RHTower/RealPrincipalSeriesDerivedDirections.lean`: finite-vector diagonal/rotation derivatives, general compact conjugation, the quarter-turn derivative `i(E-F)`, recovery of E and F, and `sphericalPrincipalLaplacian_eq_derived`.
- All three modules are imported exactly once by their area umbrellas.

The model Casimir is now expressed through operators identified with actual pointwise flow derivatives. This does not yet construct the intertwiner from an arbitrary Maass eigenfunction to that model, prove Hilbert-space smooth-vector estimates, or establish global automorphic lifts. No all-level spectral inequality is claimed.

## Validation

- Scratch checks and needed dependency oleans used `lake env lean` sequentially.
- Targeted `lake build GaloisForLFunctions.RHTower.MaassCuspSmoothness`: passed, no warnings. New generic module: 18 seconds; Maass specialization: 8.4 seconds.
- Targeted `lake build GaloisForLFunctions.RHTower.RealPrincipalSeriesDerivedDirections`: passed, no warnings. New module: 2.6 seconds. Stale diagonal/rotation dependencies were rebuilt against the current `1-s` normalization.
- Final builds used `LEAN_NUM_THREADS=1`; no umbrella or full build.
- All 28 new public theorems audited with `#print axioms` in a temporary scratch file: only `propext`, `Classical.choice`, and `Quot.sound`; no new axioms or unfinished proofs.
- No heartbeat, recursion-depth, or transparency options added or increased.
- Generated indexes refreshed once. Repository lint reports unrelated unwired Deninger/horizon modules and generated-index drift from concurrent work; no errors mention these three modules. Global lint is not claimed clean.
