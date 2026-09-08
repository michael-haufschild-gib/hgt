# Compact correction to the exact Bessel boundary form

- **ID:** SELBERG-COMPACT-BESSEL-BOUNDARY-OPERATOR
- **Stage:** 3-formalized.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 18.
- **Scope:** Actual Bessel coefficients on complex square-summable Fourier sequences.

## Exact result

At period `w=exp(b)` and height `Y=exp(T)`, let `k_n=2*pi*|n|/w` and let `B_n` be the actual critical Bessel outgoing coefficient for each nonzero integer `n`. Set `c_n=k_n-B_n`, and explicitly set `B_0=c_0=k_0=0`.

The diagonal operator `C:u -> (c_n*u_n)` on complex `ell^2(Z)` is compact, positive, and self-adjoint. It satisfies `||C||<=1/(2*Y)` and

`0<c_n< w/(16*pi*Y^2*|n|)` for `n != 0`.

Its kernel is exactly the constant channel. Its quadratic form is strictly positive whenever any nonconstant coefficient is present.

For every `u` in `ell^2`, the series `sum c_n*|u_n|^2` is summable. Consequently the outgoing form has exactly the frequency-weighted form domain:

`Summable(B_n*|u_n|^2) <-> Summable(k_n*|u_n|^2)`.

On this domain,

`sum B_n*|u_n|^2 = sum k_n*|u_n|^2 - Re <Cu,u>`.

The outgoing form is at most its principal frequency form, with equality precisely on the constant channel.

## Dependency-closed paper proof

Cycle 17 proves `0<k-B(k,Y)<min(1/(2Y),1/(8kY^2))` for the source-defined Bessel function. Substitution of the literal integer frequencies gives both diagonal bounds. For every positive epsilon, choose `N>w/(16*pi*Y^2*epsilon)`. A coefficient at least epsilon must have `|n|<N`, so only finitely many coefficients lie outside the epsilon ball. The coefficients tend to zero in the cofinite filter.

The inspected `HTGeometry.BoundedDiagonalOperatorLp` constructs the bounded diagonal operator and proves compactness from this decay by finite diagonal truncation. Since all coefficients are real, conjugation proves symmetry and self-adjointness. The Hilbert inner-product series is summable and its summands here are `c_n*|u_n|^2`; taking real parts gives the correction-energy series. Its nonnegative summands prove positivity. Every nonzero-frequency coefficient is strictly positive, so a zero operator value or a zero correction sum forces every nonconstant coordinate to vanish. The converse follows coordinatewise.

Finally `B_n=k_n-c_n` at every index, including zero. Adding or subtracting the already-summable correction series proves the equivalence of the two form domains. Linearity of summation on that domain proves the exact form decomposition and its equality classification.

## Lean implementation

Module: `GaloisForLFunctions.RHTower.SelbergBesselBoundaryOperator`, namespace `SelbergBoundaryOperator`.

Capstones: `amplitude_index_bound`, `amplitude_tendsto_cofinite`, `operator_compact`, `operator_selfAdjoint`, `operator_positive`, `operator_kernel_iff`, `quadratic_pos_iff`, `seam_summable_iff`, `boundary_form_decomposition`, `boundary_form_eq_principal_iff`.

Complete scratch and direct source checks passed without warnings. The targeted final build passed, rebuilding one module (`/tmp/selberg_boundary_operator_build.log`). Twelve capstone checks in `/tmp/selberg_boundary_operator_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into RHTower and indexed; whitespace checks passed. Latest repository-wide lint failed on seven unrelated unwired modules, detailed on the parent card (`/tmp/selberg_fourier_final_lint.log`). All task-owned Lean/Lake processes finished. No numerical experiment, assumed lift, added axiom, or global spectral conclusion is used.

## Remaining source obligation

This constructs the boundary form on sequence data. It does not yet identify an actual Maass Fourier trace with this form, construct a response on the congruence quotient core, or prove that the coupled core and tail energy is nonnegative. The Selberg goal remains open in this work.
