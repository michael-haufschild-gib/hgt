# Gaussian beta normalization has an exposed multiscale Gamma orbit

- **ID:** `gaussian-beta-multiscale-normalizer-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[SEARCH]` primary-source normalizer; `[BRIDGE]` HT classification and cross-ensemble value relation
- **Source:** I. Dumitriu and A. Edelman, *Matrix Models for Beta Ensembles*, arXiv:math-ph/0206043, equations (1), (2), and (7)
- **Statement:** The Gamma part of the `K`-eigenvalue beta-Hermite partition normalizer is DA exactly for `K≤1` and HT exactly for `K>1`.  Its quotient by the circular beta normalizer is exactly the nonempty lower positive-integer-scale Gamma tower and is HT for every `K>1`.

## Goal

Use the Gaussian beta-ensemble normalization to force a reusable multiscale theorem rather than a
random-matrix wrapper.  The coupling `z=beta/2` is an observed parameter: the theorem classifies
the normalizer as a function of that clock and makes no claim about matrix time evolution.

## Gates

- [x] 0 → 1 in-progress: primary-source density and exact Gamma product located
- [x] 1 → 2 fully-proven: dependent-slot flattening and exposed maximal-scale orbit proved
- [x] 2 → 3 formalized: parent interface, Gaussian/circular relation, exact boundary, inversion, and source extraction pass
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Primary-source relation

Dumitriu--Edelman equation (2) gives the beta-Hermite density constant

`c_H = (2*pi)^(-K/2) product_{j=1}^K Gamma(1+z)/Gamma(1+j*z)`,

where `z=beta/2`.  Omitting only the nonzero constant power of `2*pi`, the reciprocal partition
normalizer is

`G_K(z) = product_{j=1}^K Gamma(1+j*z) / Gamma(1+z)^K`.

The cited paper places the beta-Hermite ensembles in Dyson's symmetry classes, describes their
physics origin, and connects general beta ensembles to Calogero--Sutherland quantum systems.  Lean
formalizes the Gamma normalizer as a complexified coupling observable, not those physical model
equivalences.

## Parent theorem forced by the application

An integer-scale family refines under Gauss multiplication to the dependent finite type

`Sigma i, Fin (n_i)`.

`MeromorphicGammaNatScale` previously classified a single refined orbit and transferred DA/HT
through the simultaneous Gauss gauge, but it lacked the type-level bridge from this dependent slot
space to the `Fin d` orbit theorem.  The new declarations provide:

- `gammaFintypeOrbitProductMero` and
  `hypertranscendentalOver_gammaFintypeOrbitProductMero`: arbitrary finite indexing;
- `gammaNatScaleFamilyRefinedMero_eq_slotProduct`: exact flattening of the nested Gauss products;
- `hypertranscendentalOver_gammaNatScaleFamilyMero_of_exposedRefinedOrbit`: an unconditional
  sufficient criterion requiring only one nonzero-charge refined orbit separated from every other
  slot.

The other refined slots may collide with one another and carry arbitrary signed charges.  Thus the
criterion is a strict corpus expansion, not a positivity-only special case.

## Exact positive statement

For `K≥2`, the largest factor `Gamma(1+K*z)` contributes the refined center `1/K`.  Every refined
center from a smaller positive integer scale has the form `(k+1)/j` with `j<K`; every other center
at scale `K` has `k>0`.  The exact integer argument proves

`(k+1)/j - 1/K` is never an integer

in either case.  Hence `1/K` is an exposed charge-one orbit, irrespective of all denominator
charges and all collisions elsewhere.  This gives

`DA(G_K) iff K≤1`, and `HT(G_K) iff K>1`.

The Gamma density prefactor is `G_K^(-1)` and has the same exact HT boundary.  Any scalar-aware
finite differential circuit realizing `G_K` for `K>1` must contain an HT non-scalar atom.

## Gaussian/circular value relation

The circular beta normalizer is

`C_K(z)=Gamma(1+K*z)/Gamma(1+z)^K`.

Therefore

`G_K(z) = [product_{j=1}^{K-1} Gamma(1+j*z)] C_K(z)`

and

`G_K(z)/C_K(z) = product_{j=1}^{K-1} Gamma(1+j*z)`.

The quotient is HT for every `K>1`.  This is the nontrivial positive contrast with the already
formalized circular/Dirichlet relation, whose quotient is rational and DA.  Equal HT labels do not
determine whether changing normalization loses all HT information or adds an entire multiscale
source; the exact orbit quotient does.

## Lean certificate

Modules:

- `GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale`
- `GaloisForLFunctions.HTGeometry.GaussianBetaEnsembleNormalizerBoundary`
- `GaloisForLFunctions.HTGeometry.CircularBetaEnsembleNormalizerBoundary`

Capstones:

- `hypertranscendentalOver_gammaFintypeOrbitProductMero`
- `hypertranscendentalOver_gammaNatScaleFamilyMero_of_exposedRefinedOrbit`
- `gaussianBetaEnsembleFamilyMero_eq_partitionNormalizer`
- `hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_many`
- `gaussianBetaEnsemblePartitionNormalizerMero_eq_lowerScale_mul_circular`
- `gaussianBetaEnsemble_div_circular_eq_lowerScaleTower`
- `hypertranscendentalOver_gaussianBetaEnsemble_div_circular`
- `hypertranscendentalOver_gaussianBetaEnsembleDensityGammaNormalizerMero_iff_many`
- `exists_hypertranscendental_atom_of_gaussianBetaEnsembleNormalizerCircuit`

Direct-file checks and exact cached module builds pass.  The capstone axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Multiscale black-hole/CFT impact

The exposed-orbit theorem closes a substantial commensurable subcase of the multiscale Gamma
problem: a full orbit consolidation is unnecessary whenever one refined pole lattice is visibly
unique.  It can now certify HT for BTZ, thermal-CFT, scattering, or Bogoliubov products that contain
such a scale.  It does not yet classify a family in which every refined orbit is shared, nor the
incommensurable-slope case.

## RH pressure test

The theorem strengthens the archimedean cancellation audit available to `RHTower`: one exposed
refined Gamma orbit is enough to rule out DA cancellation across an entire commensurable family,
even when the rest of the charge table is unresolved.  The Gaussian/circular contrast also shows
why HT status alone is insufficient; the quotient orbit content is decisive.  No prime-source,
positivity, sign, zero-free-region, or off-critical-zero hypothesis is discharged by this result.

## Log

- 2026-07-17 — Dumitriu--Edelman normalizer extracted; arbitrary-finite-index Gamma product,
  dependent Gauss-slot flattening, exposed-orbit criterion, complete Gaussian size boundary,
  Gaussian/circular tower relation, density inversion, and circuit source extraction formalized
  and verified with serialized targeted Lean processes.
