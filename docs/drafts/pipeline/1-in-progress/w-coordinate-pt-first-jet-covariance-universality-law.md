# W-coordinate PT first-jet covariance universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; CLASSICAL INGREDIENTS]`

## Lean-derived conjecture

Reading `HTGeometry/PTInvolution.lean` against `RHTower/WCoordinate.lean` exposes a missing
connector.  For every scalar function `f`, away from `z = 0,1`, the Li coordinate conjugates
functional-equation pullback to inversion:

`(f ∘ w) ∘ sigma = f ∘ inv ∘ w`.

At first-jet level this square is covariant rather than merely commutative.  If `f` has derivative
`f'` at `w(z)⁻¹`, then the reflected pullback has derivative

`-f' z⁻² w(z)⁻²`.

The two inverse-square factors are respectively the Li-coordinate Jacobian and inversion
Jacobian; their product is exactly the derivative weight at the reflected point.

## Corpus inputs

- `GaloisForLFunctions.fePullback_apply`
- `GaloisForLFunctions.hasDerivAt_fePullback`
- `GaloisForLFunctions.wCoordinate_sigma_eq_inv`

## Novelty protocol

No literature search was performed before the Lean proof.

Post-proof audit:

- Bombieri--Lagarias and later Li-criterion literature uses the scalar coordinate
  `1 - 1/rho` and functional-equation zero pairing, but the searched sources do not state the
  arbitrary-function first-jet pullback theorem:
  <https://doi.org/10.1006/jnth.1999.2392>
- DLMF gives the classical Möbius derivative formula
  `(az+b)/(cz+d) ↦ (ad-bc)/(cz+d)^2`, which accounts for the individual inverse-square
  Jacobians:
  <https://dlmf.nist.gov/1.9.E42>
- Targeted searches found no source stating the exact joint certificate
  `(f ∘ w) ∘ sigma = f ∘ inv ∘ w` together with derivative
  `-f' z⁻² w(z)⁻²`.

Verdict: underlying algebra is classical, but the exact universal first-jet synthesis is absent
from both corpus and searched literature.  Novelty claim is restricted to that joint formulation,
not to Möbius differentiation or Li's coordinate separately.

## Lean target

`formal/GaloisForLFunctions/RHTower/WCoordinatePTFirstJetCovarianceUniversalityLaw.lean`

## Verification

- scratch proof: exact, warning-free
- source proof: exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/WCoordinatePTFirstJetCovarianceUniversalityLaw.lean`
- final module build deferred to terminal audit
