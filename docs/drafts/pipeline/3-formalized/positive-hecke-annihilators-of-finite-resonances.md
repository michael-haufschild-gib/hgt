# Positive Hecke annihilators of finite resonances

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `logs/aal-conjecture-loop-2026-11-07.md`, cycles 292–294.
- **Statement:** Every finite set of actual nontrivial zeta zeros admits a polynomial with nonnegative coefficients in the two Hecke operators `T₂,T₃`, with identity coefficient one, annihilating the corresponding completed Eisenstein modes.

## Construction

For `u=(ρ−1)/2`, the Hecke eigenvalues are `p^u+p^(−u)`. Since `Re u<0` and `Im u≠0`, at least one of the eigenvalues at `p=2,3` lies outside the nonnegative real axis. A normalized complex number other than one has a power with negative real part. Its conjugate quadratic gives a positive polynomial annihilator. Products handle finite sets and powers impose multiplicities.

The polynomial acts by literal finite sums of ordered compositions of `T₂,T₃`. Nonnegative coefficients and constant coefficient one imply pointwise domination of every nonnegative test. The established Hecke eigen-equation proves annihilation of the completed Eisenstein modes. Commutation on arbitrary functions is unnecessary.

## Constant-mode cost

For every actual zero, `−1/2 < Re u < 0`, hence

`|p^u+p^(−u)| ≤ 2 cosh((Re u) log p) < 2 cosh((log p)/2)`.

The right side is the Hecke eigenvalue of the constant function. If `P` has nonnegative coefficients, constant coefficient one, and vanishes at the resonant pair, its nonconstant terms sum to `−1`. Their constant-mode values strictly dominate their norms. Therefore `P(T₂,T₃)1 > 2` everywhere.

On `Re u<0`, a positive annihilator with constant coefficient one exists exactly when `Im u≠0`: at real parameters every monomial is positive, so evaluation is at least one. This separates nonreal resonances from real exceptional parameters.

## Scope

This construction removes finitely many resonant modes while preserving positivity. Constant-mode amplification is unavoidable; no AAL conclusion follows. The unresolved arithmetic contradiction is not an input to the proposed theorem.

## Lean

Namespace: `GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke`.

- `PositiveHeckeAnnihilatorsOfFiniteResonances.lean`: `exists_xi_zero_annihilator_with_multiplicities` constructs the positive polynomial and all prescribed spectral zero orders.
- `PositiveHeckePolynomialsDominateTheirTests.lean`: `exists_positive_dominating_xi_annihilator` couples the polynomial to literal Hecke action, annihilation, and pointwise domination.
- `PositiveHeckeCancellationAmplifiesTheConstantMode.lean`: `constant_response_gt_two` proves the forced cost; `exists_annihilator_iff_nonreal` gives the exact classification on `Re u<0`; `exists_xi_annihilator_with_constant_cost` combines all conclusions for the same polynomial.

All three modules pass direct `lake --old env lean` checking without warnings and are umbrella-wired. All five capstone audits have exactly `propext`, `Classical.choice`, and `Quot.sound`. No AAL or off-line-zero hypothesis is used.
