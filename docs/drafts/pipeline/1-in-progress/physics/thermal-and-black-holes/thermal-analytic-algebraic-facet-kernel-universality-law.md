# Thermal analytic--algebraic facet-kernel universality law

## Status

Formalized in Lean and wired into the HTGeometry umbrella. Kept in progress until the global
corpus-exhaustion and final audit gates complete.

## Lean sources

- `HTGeometry.GibbsExposedFaceRadicalFlag`
- `GaloisForLFunctions.HTGeometry.ThermalStanleyReisnerFacetFiltration`

## Conjecture

Let a finite facet family carry an energy marking. Equip the same facets with a positive
source-marked complex Gram packet and with localized Stanley--Reisner facet ideals. At every
threshold, simultaneous membership in the analytic Gibbs radical and algebraic thermal ideal is
equivalent to pointwise simultaneous vanishing on every surviving facet.

This joint kernel is monotone under raising the threshold, invariant under common translation of
all energies and the threshold, and at an upper radius is supported exactly on the exposed
maximum-energy facets.

## Why this is not already one source theorem

The Gibbs module proves the positive Gram radical criterion, its flag monotonicity, and energy
translation invariance. The Stanley--Reisner module independently proves the filtered ideal
membership criterion, ideal monotonicity, and the corresponding translation invariance. Corpus
search found no declaration coupling both detectors on one energy-filtered facet set.

## Proof plan

1. Define the simultaneous analytic--algebraic kernel predicate.
2. Rewrite both components using their exact pointwise criteria.
3. Derive the joint threshold flag from the two existing monotonicity theorems.
4. derive energy-origin invariance from the two existing translation laws.
5. At a common upper radius, reduce both components to the exposed facet set.

No numerical computation is used: all claims are exact consequences of existing formal theorems.

## Lean result

`formal/GaloisForLFunctions/HTGeometry/ThermalAnalyticAlgebraicFacetKernelUniversalityLaw.lean`
proves:

- `thermalAnalyticAlgebraicFacetKernel_iff`;
- `thermalAnalyticAlgebraicFacetKernel_mono`;
- `thermalAnalyticAlgebraicFacetKernel_add_const`;
- `thermalAnalyticAlgebraicFacetKernel_radius_iff`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/HTGeometry/ThermalAnalyticAlgebraicFacetKernelUniversalityLaw.lean`

## Novelty status

Post-proof searches for the exact conjunction of positive Gibbs Gram radicals, energy-filtered
localized Stanley--Reisner facet ideals, threshold monotonicity, translation invariance, and
exposed-face support found separate literature on Stanley--Reisner/face ideals and on persistent
face filtrations, but no matching joint analytic--algebraic kernel theorem. Novelty claim is
therefore deliberately narrow: the exact coupled finite-facet packaging formalized here was not
located, not that either component theory is new.
