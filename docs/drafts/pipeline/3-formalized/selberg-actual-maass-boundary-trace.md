# Actual Maass traces in the Bessel boundary-form domain

- **ID:** SELBERG-ACTUAL-MAASS-BOUNDARY-TRACE
- **Stage:** 3-formalized.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 20.
- **Scope:** Actual Fourier coefficients of principal-congruence Maass cusp eigenforms at every positive height.

## Exact result

For the literal normalized coefficients `a_n(y)` at period `w=N+1` and every `y>0`, there exists a nonnegative finite `C` such that

`(1+|n|)^2*|a_n(y)|<=C` for every integer `n`.

The four real series `sum |a_n|`, `sum |a_n|^2`, `sum k_n^2*|a_n|^2`, and `sum k_n*|a_n|^2` are summable, where `k_n=2*pi*|n|/w`.

Thus the actual sequence at height `exp(T)` defines an element of complex `ell^2(Z)` and of the exact principal-frequency form domain from cycle 18. Its outgoing Bessel seam series is summable and satisfies

`sum B_n*|a_n|^2 = sum k_n*|a_n|^2 - Re <C_B a,a>`,

where `C_B` is the actual positive compact Bessel correction operator already constructed. The zero Fourier coefficient is retained in the sequence, while the nonzero-mode seam sets its own zero coefficient to zero.

## Dependency-closed paper proof

Cycle 19 proves `k_n^2*|a_n|<=M` at each positive height. Divide by the positive squared frequency unit `(2*pi/w)^2` to obtain `n^2*|a_n|<=L`. For a nonzero integer, `|n|>=1` and `(1+|n|)^2<=4n^2`. The choice `C=4L+|a_0|` therefore bounds every weighted coefficient, including zero.

The inspected corpus theorem `RHTower.deningerFourier_summable_inv_sq` proves that `(1+|n|)^(-2)` is summable over the integers. Comparison gives absolute coefficient summability. The same weighted bound implies `|a_n|<=C`, so `|a_n|^2<=C*|a_n|` gives square summability. Multiplying the original frequency estimate by `|a_n|` gives `k_n^2*|a_n|^2<=M*|a_n|`, hence summability of the squared-frequency energy. Finally `k_n<=1+k_n^2` gives summability of the first-frequency energy.

Use these actual proofs to bundle the literal sequence in `lp ... 2`, and then in the existing frequency form domain. Substitution into the already-proved compact-correction identity gives the stated actual-trace identity; its outgoing-series summability follows from the exact domain equivalence.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassBoundaryTrace`, namespace `SelbergMaassTrace`.

Capstones: `coefficient_weighted_bound`, `coefficient_norm_summable`, `coefficient_normSq_summable`, `coefficient_gradient_summable`, `coefficient_frequency_summable`, `boundaryTrace`, `formTrace`, `maass_boundary_decomposition`, `maass_seam_summable`.

Complete scratch and direct source checks passed without warnings. The targeted final build passed, rebuilding one module (`/tmp/selberg_maass_trace_build.log`). Ten capstone checks in the combined `/tmp/selberg_trace_parseval_axioms.lean` audit report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired and indexed. Repository-wide formal lint passed with existing large-file warnings (`/tmp/selberg_trace_parseval_lint.log`); whitespace checks passed. All task-owned Lean/Lake processes finished. No additional axiom or numerical experiment is used.

## Next source obligation

The sequence now comes from the actual Maass function. [Cycle 21](selberg-maass-quarter-parseval.md) also proves the physical mass and energy Parseval identities at each positive height. Infinite-height integration, the quotient-core response, and the global quarter bound are still unproved.
