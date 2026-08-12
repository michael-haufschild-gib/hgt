Route U C43-Y/PDH.9 polynomial-Gaussian Fourier aperture is formally closed.

Lean module:
- formal/GaloisForLFunctions/RHTower/PolynomialGaussianFourierAperture.lean
- Wired into formal/GaloisForLFunctions/RHTower.lean.

Main closed theorems:
- RHTower.norm_fourier_polynomialGaussianEnergy_le: for every P : Polynomial ℝ and signed η, exact FGA.1 with exponent -π η²/2 + |η| sqrt(4π natDegree P), RHS Gaussian L² norm squared.
- RHTower.norm_routeUPolynomialGaussianFourier_le: native exp(-i ξ x) Route-U estimate before division.
- RHTower.routeUPolynomialGaussianFourier_div_mass_le: exact FGA.2 ratio with exponent -ξ²/(4t) + 2 sqrt(deg Q)|ξ|/sqrt(t). Positivity t encoded in subtype {t : ℝ // 0<t}; no nonzero Q or positive mass premise, zero-mass case closed.

Proof architecture:
1. Explicit entire integrand P_C(z)^2 exp(-2πz²-2πiηz).
2. Explicit coefficient-dependent lower-strip exponential majorant.
3. Lower horizontal contour shift z=x-iη/2.
4. Exact completing-square identity.
5. Previously closed coefficient-uniform complex translated polynomial-Gaussian L² theorem.
6. Fourier conjugation for negative η.
7. Exact native Route-U dilation and radical identities, including mass scaling.

Verification:
- lake env lean GaloisForLFunctions/RHTower/PolynomialGaussianFourierAperture.lean passed.
- Final lake build GaloisForLFunctions.RHTower.PolynomialGaussianFourierAperture passed 8825/8825.
- #print axioms on all three capstones: [propext, Classical.choice, Quot.sound] only.
- Target module contains no sorry/admit/axiom/opaque/unsafe.
- Corpus-wide scripts/formal_tools.py lint still fails on many pre-existing umbrella-unreachable modules; no target-module banned declaration or reachability issue.
- No numerical computation was used.

Research card moved to:
docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/mass-shifted-polynomial-gaussian-fourier-aperture.md
Standalone theorem classified BRIDGE/classical-adjacent; exact Route-U normalization/composition is now a verified load-bearing closure. Goal RH remains open. User requested pause after finishing this Lean unit.