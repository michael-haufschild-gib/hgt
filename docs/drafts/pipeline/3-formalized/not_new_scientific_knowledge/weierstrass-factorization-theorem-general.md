# The general Weierstrass factorization theorem on ℂ

- **ID:** weierstrass-factorization-general
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** goal request 2026-08-21
- **Statement:** every entire `f : ℂ → ℂ` that is not identically zero is
  `z ^ m · exp (g z) · ∏' n, E_n (z / a n)` with `g` entire, `m` the order of vanishing at the
  origin, and `(a n)` a padded enumeration (entries equal to `0` are inert) of the nonzero zeros of
  `f`, each occurring with exactly its multiplicity.

## Goal
Close the classical Weierstrass factorization theorem unconditionally in the corpus — no growth
hypothesis, no summability hypothesis, no finiteness hypothesis on the zero set.  Mathlib has no
form of this theorem; the corpus previously owned only the *existence* half
(`weierstrassGenusProduct` realizing a prescribed divergent zero sequence) and the *order-one*
Hadamard half (`RHTower.OrderOneHadamard.exists_expAffine_mul_hadamardProduct`, which needs a
growth envelope and hence square-summable inverse zeros).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: `GaloisForLFunctions.exists_weierstrass_factorization`, umbrella wired,
      `scripts/formal_tools.py lint` PASS, axiom audit clean
- [ ] 3 → 4  publication-ready

## Lean

Modules (all under `formal/GaloisForLFunctions/HTGeometry/`, all wired into
`GaloisForLFunctions.HTGeometry`):

1. `WeierstrassPaddedGenusProduct.lean` — the canonical product of increasing genus over a
   **padded** zero sequence.  `PaddedZeroSeq a : ∀ r, {n | a n ≠ 0 ∧ ‖a n‖ ≤ r}.Finite`.  Because
   `z / 0 = 0` and `E_p 0 = 1`, an entry `a n = 0` contributes the factor `1`, so padding replaces
   the old pair of hypotheses `(∀ n, a n ≠ 0)` and `‖a n‖ → ∞` and additionally covers a finite
   zero set.  Contents: `hasProdLocallyUniformlyOn_padded`,
   `differentiable_weierstrassGenusProduct_padded`, `weierstrassGenusProduct_eq_zero_iff_padded`,
   `analyticOrderAt_weierstrassGenusProduct_padded` (order at `z₀ ≠ 0` = multiplicity of `z₀` in
   the sequence) and `analyticOrderAt_weierstrassGenusProduct_padded_zero` (order `0` at the
   origin, since the product there is `1`).
2. `PaddedSequenceOfDivisor.lean` — `countable_of_locallyFiniteNorm` (a locally finite family in
   `ℂ` has a countable index type: the index is the countable union of the finite sets
   `{i | ‖p i‖ ≤ n}`) and `exists_paddedZeroSeq` (extend `p` by zero along an injection
   `ι ↪ ℕ`; the result is a `PaddedZeroSeq` with the same fibres over every `w ≠ 0`).
3. `WeierstrassFactorizationEntire.lean` — `analyticOrderAt_ne_top_of_entire`, the origin-free
   zero-copy index `NonzeroZeroCopy`, and the two headline theorems
   `exists_weierstrass_factorization` and
   `exists_weierstrass_factorization_of_ne_zero_at_origin`.

Assembly: index the zero divisor of `f` with multiplicity by
`EntireZeroDivisor.ZeroCopy f`, discard the copies over the origin, pad the resulting locally
finite family into `a : ℕ → ℂ`, set `P z = z ^ m · weierstrassGenusProduct a z`, check
`analyticOrderAt P = analyticOrderAt f` everywhere, apply
`EntireQuotient.exists_entire_nonvanishing_quotient` and then
`HTGeometry.exists_entire_log_of_ne_zero`, absorbing the constant `h 0` into the exponent via
`Complex.exp_log`.

Axiom audit: `[propext, Classical.choice, Quot.sound]` only.

## Log
- 2026-08-21 — created; corpus audit done.
- 2026-08-21 — all three modules compile, umbrella wired, lint green, axioms clean; promoted to
  3-formalized.
