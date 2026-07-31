# Worst-spectrum sharpness for finite quantum survival

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteQuantumSurvivalWorstSpectrumSharpnessLaw`
- **Claim class:** `[LEAN-PROVED] [SHARPNESS]`

## Result

For the uniform pure state on \(d\) energy sectors, scalar survival loss is
exactly half the squared Hilbert–Schmidt displacement of the associated
rank-one density matrix:
\[
 1-S(t)=\frac12D_{\mathrm{HS}}(t)^2.
\]
The deterministic Haar-avoidance spectra for the matrix observer therefore
transfer without loss to scalar survival. For every projective rank
\(r=d-1\), hard spectra avoid the survival target at all sampled clocks
\(1\le n\le N\) under the explicit Haar budget, while every spectrum has a
constructive return
\[
 n\le(Q+1)^r,\qquad
 1-S(n)\le2\left(\frac{2\pi}{Q+1}\right)^2.
\]

Thus the projective exponent is attained in the same scalar survival metric
used by the localization law.

## Formal declarations

- `finiteSpectralSurvivalAmplitude_uniformSurvivalWeight`
- `uniformSurvivalDeviation_eq_half_observerDistanceSq`
- `exists_uniformSurvival_avoiding_return_through`
- `exists_rankSharp_uniformSurvival_avoiding_return_through`
- `exists_uniformSurvival_rank_recurrence`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

Sharpness is proved for the complete uniform pure-state observer. It does not
assert that arbitrary observer graphs or Anderson ensembles realize the hard
spectra.
