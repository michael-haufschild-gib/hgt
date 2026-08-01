# Complete resolution source-character selection

## Status

Formalized; manuscript integration and final audit pending.

## Theorem

Every summable analytic resolution of one supplies a nonzero \(\ell^1\) vector and a channel
preserving analytic order. Every equivariant descent of that vector into a norm-conservative
target either erases it or has zero real character rate.

For the complete high-exponent Riemann resolution at every
\(\operatorname{Re}\rho\ge\tfrac12\), the character rate is \(2\operatorname{Re}\rho-1\).
Therefore every such consumer satisfies
\[
T\mathbf M_K(\rho)=0\quad\text{or}\quad\operatorname{Re}\rho=\tfrac12.
\]
More generally, without exact equivariance its defect is bounded below by
\[
\|TU_\rho\mathbf M_K(\rho)-VT\mathbf M_K(\rho)\|
\ge |e^{2\operatorname{Re}\rho-1}-1|\,\|T\mathbf M_K(\rho)\|.
\]
Because \(\|\mathbf M_K(\rho)\|_1\ge1\), a consumer satisfying
\(\|Tx\|\ge\kappa\|x\|_1\) has the consumer-independent defect floor
\(\kappa|e^{2\operatorname{Re}\rho-1}-1|\).

## Formal source

`formal/GaloisForLFunctions/RHTower/CompleteResolutionSourceCharacterSelectionLaw.lean`

- `summableAnalyticResolution_sourceCharacter_conservation`
- `normConservative_sourceCharacter_defect_lowerBound`
- `completeResolution_sourceCharacter_selection`
- `completeResolution_sourceCharacter_defect_lowerBound`
- `one_le_norm_summableSourceVector_of_hasSum_one`
- `completeResolution_sourceCharacter_uniformFaithfulness_defect_lowerBound`
- `no_uniformlyFaithful_normConservative_approximateIntertwiners`

## Verification

- [x] Direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/CompleteResolutionSourceCharacterSelectionLaw.lean`
- [x] Reachable from `GaloisForLFunctions.RHTower`
- [ ] Final targeted build
- [ ] Axiom audit
