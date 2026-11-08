# Fourier notches and arithmetic aliasing

- **ID:** aal-fourier-notch-aliasing
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Question:** Can profiles with high-order real Fourier zeros suppress the aliasing of a finite-top-layer test while retaining unconditional positivity of its actual integer-atom Weil matrix?

## Proposed mechanism

Concentrate logarithmic packets near zeros of the profile's Fourier transform. A zero of order `m` suppresses the nearby squared aliasing factor to order `2m`. A growing logarithmic separation could amplify the exceptional reflected pair faster than the remaining spectrum. Packet width, separation, and the arithmetic positivity range must be controlled together.

## Exact constraint

`exists_critical_multiple_completeWeilMatrix_posDef` is specifically for `tiltedUnitSpline`. It does not provide positivity for a profile obtained by applying a differential polynomial or introducing Fourier zeros. Such a transfer must be proved; it cannot be assumed. Integer translations of atoms also change the conductor range when realized by multiplicative shifts.

`EveryNonzeroProfileHasAPositiveConductorFloor.lean` already proves positive integrated spectral tails and a uniform conductor floor on bounded overlap for every nonzero compact `C²` profile, including profiles with real Fourier zeros. `EveryCompactProfileHasSubexponentialConductorFloors.lean` strengthens the tail floor to every exponential decay rate. The theorem `eventually_noRealZero_completeWeilMatrix_posDef` additionally requires absence of real Fourier zeros for its Gamma reserve. A conductor floor alone does not establish the required matrix positivity.

## Open step

Derive a complete energy estimate for these packets, including the archimedean concentration cost and every aliasing harmonic. No negative test in the certified positive matrix range has been constructed. No AAL conclusion is claimed.

## Differential-spline candidate

Let `B_m` be the convolution of `m` unit interval indicators. For even `m≥6`, the profile `B_m + (-1)^((m-4)/2) D^(m-4) B_m` has mean `1`, candidate Fourier multiplier `(1+ξ^(m-4))` times that of `B_m`, and fourth-power Fourier decay. Each nonzero integer harmonic retains a zero of order `m`.

The harmonic sum requires a separate analysis. Near an integer overlap, its leading term is proportional to

`Σ_{k≥1} k^(-8) sin(πkε)^(2m)`.

The conjectured order is `|ε|^7`, independent of `m≥4`: harmonics `k≈1/|ε|` contribute at that order. Thus high multiplicity of individual Fourier zeros need not give high multiplicity of the full aliasing zero. An exact dilation limit and its positive coefficient remain to be proved and formalized.
