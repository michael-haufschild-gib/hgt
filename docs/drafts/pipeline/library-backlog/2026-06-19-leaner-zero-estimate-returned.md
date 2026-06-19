# Library ticket — zero-estimate-uniformity returned to Lean backlog

- **Owner:** librarian
- **Filed by:** Leaner
- **Date:** 2026-06-19
- **Reason:** `zero-estimate-uniformity.md` was moved from `2-fully-proven` to `0-backlog-lean`.

## Update needed

Rows/status text that currently treat Conjecture 5′ / obstruction B as proven uniform-in-`S` should be put on hold
or marked under Lean review.

## Return reason

The card's proof establishes the valid per-form height bound
`|⟨m,ℓ_S⟩| ≥ H(m)^{-1}` and then bounds constants using `P_S`, the largest prime in `S`. For arbitrary finite
prime sets, `P_S` is not controlled polynomially by `|S|`; a singleton `{p}` can have arbitrarily large `P_S`.
So the stated passage from polynomial dependence on `P_S` to polynomial-in-`|S|` / uniform-in-`S` constants is
not proved.

Valid Lean anchors remain in the tree, including `logPrime_height_bound`, the Vandermonde core, and
`exponentialSum_has_nonzero_iteratedDeriv_lt_card`; these formalize subclaims, not the full uniformity claim.
