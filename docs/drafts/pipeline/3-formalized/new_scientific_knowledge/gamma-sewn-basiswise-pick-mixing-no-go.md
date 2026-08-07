# Gamma-sewn basiswise Pick mixing no-go — formal certificate

- **ID:** `gamma-sewn-basiswise-pick-mixing-no-go`
- **Stage:** 3-formalized
- **Scientific status:** `[UNCONDITIONAL LEAN] [ARBITRARY HILBERT DIMENSION]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:** `gamma/gamma-sewn-basiswise-pick-mixing-no-go.md`

## Formal declarations

```text
HTGeometry.continuousLinearMap_eq_id_of_basiswise_boundaryPick
RHTower.tendsto_gammaSewnMobius_commonAperturePickDiagonal_nhdsGT_zero
RHTower.not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily
RHTower.not_exists_continuous_gammaSewnMobius_basisMarginal_commonAperturePickFamily
```

## Source files

```text
formal/GaloisForLFunctions/HTGeometry/BasiswiseBoundaryPickRigidity.lean
formal/GaloisForLFunctions/RHTower/GammaSewnBasiswisePickMixingNoGo.lean
```

The universal theorem permits arbitrary index type and Hilbert dimension and assumes only
basiswise strong convergence at the boundary. The actual Gamma theorem proves the required common
aperture normalized loss limit from existing exact Gamma-sewn algebra and excludes every
prime-marginal-preserving operator-Pick family. A norm-continuous corollary is derived separately.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/BasiswiseBoundaryPickRigidity.lean
lake env lean GaloisForLFunctions/RHTower/GammaSewnBasiswisePickMixingNoGo.lean
lake build GaloisForLFunctions.RHTower.GammaSewnBasiswisePickMixingNoGo
```

All pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for each
principal declaration. Global repository lint is currently blocked by the unrelated, concurrently
present `RHTower.FiniteWindowSeamSincUniversalityLaw` umbrella-reachability failure; the two new
modules are umbrella-wired and contain no forbidden declarations.

## Exact scope

This closes common-aperture operator-Pick repair under unchanged actual Gamma prime marginals. It
does not prove the four-unit Xi graph contraction or RH. A surviving CCM transport must alter
first-order marginal boundary charge, use a singular/cofinal topology not strongly converging on
prime basis vectors, leave common-aperture Pick positivity, or modify the marginals before scalar
trace.
