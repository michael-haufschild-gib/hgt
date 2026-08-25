# Irregular Stokes cubic negative orientation landing (2026-08-25)

Formalized strict negative wall–Xi cubic residual and canonical source-side orientation landing.

- New module `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation.lean` proves `thetaCuspRawEvenMoment_three_mul_zero_lt_fifteen_mul_one_mul_two` and `normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg` unconditionally. Core proof: strict log-concavity of full theta source -> strictly increasing score -> IBP -> strict factorial-normalized moment log-concavity -> `M6*M0 < 15*M2*M4` -> exact cumulant sign.
- New module `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding.lean` proves every natural cutoff `X >= 3` and summable unnormalized Euler/Wold current limit are strictly negative, same Stokes chamber as Xi residual. It also proves normalized completed-residue grade-forgetting channel cannot tend to nonzero Xi residual because it collapses to zero.
- Quotient-selected scaling was rejected as target fitting. Strongest source-natural survivor is orientation, not magnitude equality.
- Remaining exact open core: construct a non-collapsing, source-derived irregular microlocal/Stokes incidence carrying cubic magnitude to Xi residual without fitted target scale. Existing normalized grade-forgetting destroys magnitude.
- Targeted checks passed. Axiom audits for all new public theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Frontier map remained read-only.

See cards `route-p-prime-gamma-wall-cubic-residual-negative-orientation.md` and `route-p-prime-gamma-wall-canonical-negative-cubic-orientation-landing.md`.