# The general Weierstrass factorization theorem on ℂ

- **ID:** weierstrass-factorization-general
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** goal request 2026-08-21
- **Statement:** every entire `f : ℂ → ℂ` that is not identically zero is
  `z ^ m · exp (g z) · ∏' n, E_n (z / a n)` with `g` entire, `m` the order of vanishing at the
  origin, and `(a n)` a padded enumeration (zeros of the sequence are inert) of the nonzero zeros
  of `f` with multiplicity.

## Goal
Close the classical Weierstrass factorization theorem unconditionally in the corpus — no growth
hypothesis, no summability hypothesis, no finiteness hypothesis on the zero set.  Mathlib has no
form of this theorem; the corpus owns only the *existence* half (`weierstrassGenusProduct` realizing
a prescribed divergent zero sequence) and the *order-one* Hadamard half.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (classical; route fixed below)
- [ ] 2 → 3  formalized: Lean theorem `exists_weierstrass_factorization`, umbrella wired, axiom audit
- [ ] 3 → 4  publication-ready

## Approach
Three new layers, all reusing the existing corpus stack.

1. **Padded genus product** (`WeierstrassPaddedGenusProduct`).  The corpus product
   `weierstrassGenusProduct a z = ∏' n, E_n (z / a n)` currently needs `∀ n, a n ≠ 0` and
   `‖a n‖ → ∞`.  Because `z / 0 = 0` and `E_p 0 = 1`, an entry `a n = 0` contributes the factor `1`,
   so the *padded* hypothesis `∀ r, {n | a n ≠ 0 ∧ ‖a n‖ ≤ r}.Finite` suffices and covers the case
   of a finite zero set.  Re-prove local uniform convergence, entirety, the zero set, and the exact
   analytic order under that hypothesis.
2. **Padding a countable divisor** (`PaddedSequenceOfDivisor`).  A locally finite family
   `p : ι → ℂ` with `p i ≠ 0` is automatically countable; `Function.extend g p 0` along an injection
   `g : ι ↪ ℕ` gives a padded ℕ-sequence with the same fibres over every `w ≠ 0`.
3. **The theorem** (`WeierstrassFactorizationEntire`).  Take `ι` to be the multiplicity copies of
   the zero divisor of `f` away from the origin (`EntireZeroDivisorIndex.ZeroCopy`), pad it, form
   `P z = z ^ m · weierstrassGenusProduct a z`, check `analyticOrderAt P = analyticOrderAt f`
   everywhere, apply `EntireQuotient.exists_entire_nonvanishing_quotient` and then
   `exists_entire_log_of_ne_zero`.

## Log
- 2026-08-21 — created; corpus audit done (existence half + order-one Hadamard already owned).
