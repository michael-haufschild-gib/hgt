# Fourier notches and arithmetic aliasing

- **ID:** aal-fourier-notch-aliasing
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Question:** Can profiles with high-order real Fourier zeros suppress the aliasing of a finite-top-layer test while retaining unconditional positivity of its actual integer-atom Weil matrix?

## Proposed mechanism

Concentrate logarithmic packets near zeros of the profile's Fourier transform. A zero of order `m` suppresses each fixed harmonic to order `2m`; summing all harmonics requires separate control. A growing logarithmic separation could amplify the exceptional reflected pair faster than the remaining spectrum. Packet width, separation, and the arithmetic positivity range must be controlled together.

## Exact constraint

`exists_critical_multiple_completeWeilMatrix_posDef` is specifically for `tiltedUnitSpline`. It does not provide positivity for a profile obtained by applying a differential polynomial or introducing Fourier zeros. Such a transfer must be proved; it cannot be assumed. Integer translations of atoms also change the conductor range when realized by multiplicative shifts.

`EveryNonzeroProfileHasAPositiveConductorFloor.lean` already proves positive integrated spectral tails and a uniform conductor floor on bounded overlap for every nonzero compact `C²` profile, including profiles with real Fourier zeros. `EveryCompactProfileHasSubexponentialConductorFloors.lean` strengthens the tail floor to every exponential decay rate. The theorem `eventually_noRealZero_completeWeilMatrix_posDef` additionally requires absence of real Fourier zeros for its Gamma reserve. A conductor floor alone does not establish the required matrix positivity.

## Open step

Derive a complete energy estimate for these packets, including the archimedean concentration cost and every aliasing harmonic. No negative test in the certified positive matrix range has been constructed. No AAL conclusion is claimed.

## Exact harmonic-sum constraint

The centered family `φ_r=B_(2r+5)+Δ^(2r+1)B_4(·+(2r+1)/2)` has integral one and squared spectrum

`|φ̂_r(2πt)|²=[1+(2πt)^(4r+2)] |B̂_(2r+5)(2πt)|²`.

Its full alias density has an exact seventh-order notch at every positive integer, with positive coefficient `∫(Δ^(2r+1)B_4)²/(2j^8)`. Increasing individual harmonic-zero multiplicity therefore does not increase the alias-notch order in this family. The exact formulas, paper proof and checked Lean declarations are in [the formalized spline card](../3-formalized/alias-notch-saturation-for-differentiated-splines.md).

This rules out that particular inference about notch order. It does not retire the broader route: profile-dependent arithmetic positivity and the full packet energy remain open.
