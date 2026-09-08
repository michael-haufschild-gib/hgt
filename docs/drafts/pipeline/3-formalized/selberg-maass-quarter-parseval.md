# Physical quarter-energy Parseval identity for Maass slices

- **ID:** SELBERG-MAASS-QUARTER-PARSEVAL
- **Stage:** 3-formalized.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 21.
- **Scope:** Actual positive-height horizontal slices of principal-congruence Maass cusp eigenforms.

## Exact result

At period `w=N+1` and any `y>0`, the actual normalized Fourier coefficients satisfy the three convergent identities

`sum |a_n(y)|^2 = (1/w)*integral_0^w |f(x+iy)|^2 dx`,

`sum k_n^2*|a_n(y)|^2 = (1/w)*integral_0^w |partial_x f(x+iy)|^2 dx`,

`sum |a_n'(y)|^2 = (1/w)*integral_0^w |partial_y f(x+iy)|^2 dx`.

Consequently the actual physical horizontal quarter-energy integral is exactly

`integral_0^w (|partial_x f|^2+|partial_y f|^2-|f|^2/(4*y^2)) dx`

`= w * sum_n (|a_n'|^2+(k_n^2-1/(4*y^2))*|a_n|^2)`.

The final signed series is summable. No termwise infinite-height integration or quotient-core cancellation is assumed.

## Dependency-closed paper proof

The inspected `DeningerFourierBridge` identifies the literal exponential Fourier kernel with the additive-circle character. Mathlib's `fourierCoeffOn_eq_integral` then identifies the normalized Maass coefficient with its interval Fourier coefficient, including the factor `1/w`.

Every actual horizontal slice is continuous, and compactness of one period gives a finite norm bound. It is therefore square integrable on that interval. Apply the inspected `hasSum_sq_fourierCoeffOn` to obtain the physical mass identity. The source C² regularity gives the same square integrability for both directional first derivatives.

For the horizontal derivative, use the actual periodicity and one integration by parts to identify its coefficient with `i*(2*pi*n/w)*a_n`. Taking squared norms gives the frequency-weighted series. For the vertical derivative, use the already-proved differentiation under the weighted interval integral to identify its coefficient with the actual `a_n'`.

Add the two derivative-energy `HasSum` identities and subtract `1/(4*y^2)` times the mass identity. Linearity of the finite interval integral is justified by continuity of all three real integrands. This proves the signed modal series and the physical quarter-energy identity with the exact period normalization.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassParseval`, namespace `SelbergMaassParseval`.

Capstones: `coefficient_eq_fourierCoeffOn`, `coefficient_mass_hasSum`, `coefficient_horizontal`, `maass_mass_hasSum`, `maass_horizontal_hasSum`, `maass_vertical_hasSum`, `maass_quarter_hasSum`, `maass_quarter_energy_identity`.

Complete scratch and direct source checks passed without warnings. The targeted final build passed, rebuilding one module (`/tmp/selberg_maass_parseval_build.log`). Eight capstone checks in the combined `/tmp/selberg_trace_parseval_axioms.lean` audit report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired and indexed. Repository-wide formal lint passed with existing large-file warnings (`/tmp/selberg_trace_parseval_lint.log`); whitespace checks passed. All task-owned Lean/Lake processes finished. No additional axiom, modal ansatz, numerical experiment, or global spectral conclusion is used.

## Remaining source question

The physical energy interface is now proved at each positive height. The next target is the actual flux balance and the infinite-height integrability needed to use it on an entire cusp. The quotient-core response and Selberg quarter bound remain unproved.
