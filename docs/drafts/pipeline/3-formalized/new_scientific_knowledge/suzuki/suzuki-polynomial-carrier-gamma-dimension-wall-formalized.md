# Polynomial-carrier Gamma dimension wall — Lean formalization

- **ID:** `suzuki-polynomial-carrier-gamma-dimension-wall-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:**
  `../../../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-polynomial-carrier-gamma-dimension-wall.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiPolynomialCarrierGammaDimensionWall.lean`
- **Status:** `[FORMALIZED CORE] [AXIOM-CLEAN] [NOT RH]`

## Certified theorem surface

The module proves the exact analytic and arithmetic collision, not a proxy matrix inequality.

| Paper statement | Lean declaration |
|---|---|
| distorted squared carrier `(7)` | `suzukiPolynomialDistortedGammaNormSq` |
| exact tail `(8)` | `suzukiPolynomialDistortedGammaNormSq_rpow_tendsto` |
| integrability for `κ < σ` | `integrable_suzukiPolynomialDistortedGammaNormSq` |
| nonintegrability for `σ <= κ` | `not_integrable_suzukiPolynomialDistortedGammaNormSq` |
| sharp iff `(9)` | `integrable_suzukiPolynomialDistortedGammaNormSq_iff` |
| common exponent window `(11)` | `suzukiPolynomialGammaDimensionWindow` |
| dimension wall `(3)` | `suzukiPolynomialGammaDimensionWindow_iff` |
| one-prime lattice square `(13)` | `summable_suzukiOnePrimePolynomialWeightSq` |
| concrete survivor `(12)` | `suzukiOnePrimePolynomialGammaWindow` |

The proof uses the already formalized exact Gamma-ratio asymptotic and derives both sides of the
power-integrability threshold. The rank theorem is an iff. The concrete one-prime result certifies
both the actual (mathbb Z)-sum and the exact distorted Gamma integral.

## Scope boundary

This module certifies the sharp scalar majorant and exponent compatibility. It does not assume or
claim the missing vector-valued primitive source transfer or a source-selected Evans cancellation.
Those remain explicit paper-side gates; compact-middle coverage is already closed by dyadic orbit
charts.

## Gates

- [x] exact distorted density defined
- [x] exact asymptotic proved
- [x] both integrability directions proved
- [x] dimension window iff proved
- [x] concrete one-prime lattice and Gamma survivor proved
- [x] wired into `GaloisForLFunctions.RHTower`
- [x] compact-middle coverage available from dyadic orbit charts
- [ ] vector-valued rough primitive transfer
- [ ] one-prime trace-zero (H^1_0)
