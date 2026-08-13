# Route U exact polynomial–Gaussian carrier formalized (2026-08-13)

New module: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePolynomialGaussianCarrier.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Closed the carrier mismatch exposed by audit: prior `PolynomialGaussianFourierAperture` concerns squared density `P(x²)^2 exp(-t x²)`, while HEPW compact witness requires an amplitude whose square is the heat term.

Definitions/theorems:
- `routeUXiPolynomialGaussianProfile P t z = evalRealPolynomial P (z^2) * exp (-(t/2) z^2)`.
- `routeUXiPolynomialGaussianProfile_sq_xiSpectralPoint`: its square at every Xi copy is exactly `xiPolynomialGaussianHeatTerm P t q`.
- `routeUXiHeatProfileSchwartz`: explicit rescaled polynomial-Gaussian Schwartz spectral profile.
- `routeUXiHeatPhysicalComplex`: its Fourier transform; proved real and even.
- `routeUXiHeatPhysicalReal`: real Schwartz amplitude consumed by finite Hankel lift.
- `routeURealEvenAmplitude_heatPhysical_eq`: complexification/evenification recovers exact complex physical amplitude.
- `routeUPositiveFourierExtension_heatPhysical_eq`: exact real-axis positive Fourier extension equals the unsquared profile.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/XiShiftedHardEdgePolynomialGaussianCarrier.lean` passed.
- `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianCarrier` passed, 11965/11965.
- Axiom audit for four capstones: `[propext, Classical.choice, Quot.sound]` only.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe` in module.

Exact next gap: prove compact cutoff extensions converge to this profile in a strip-Schwartz norm strong enough for dominated convergence over `XiZeroCopy`; pointwise real-axis convergence is insufficient. Then strict negative heat trace yields a compact negative divisor trace, existing hard-edge divisor limit yields negative lattice trace, and existing exact finite Hankel lift yields negative finite shifted reciprocal Hankel witness. Do not use squared density aperture as surrogate.