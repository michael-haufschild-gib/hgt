# Library ticket — 00-status #95 → 5-failed (is-lambda-a-period collapses to RH)

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## Change
`is-lambda-a-period` moved 0-backlog → **5-failed** (`../5-failed/is-lambda-a-period.md`). The "is the dBN
constant `Λ` a period?" line is a **false lead**: degenerate (`Λ=0 ⟺ RH`, with Rodgers–Tao `Λ≥0`, so the
value question IS RH, not an independent transcendence question) and the proposed PSLQ probe is
**structurally impossible** (`Λ` has no proven digits — pinning it below any `ε` is RH-strength; contrast
the computable `γ_n`). Salvage: under RH the no-margin is the **tame** point `Λ=0∈ℚ`, opposite the seam from
the **wild** `γ_n` — so `Λ` is NOT a regularization-freshness instance (that cross-ref withdrawn in
`regularization-freshness`).

## Suggested #95 row update
Re-tag #95 from `CONJECTURE / FUTURE` to **FALSIFIED / FALSE LEAD**: "is `Λ_dBN` a period — **collapses to
RH** (`Λ=0⟺RH`); PSLQ inapplicable (`Λ` non-computable); the dBN no-margin is the localization axis (RH/G5),
not the transcendence/period axis (#137 orthogonality). 5-failed." Also note the `Λ`-as-freshness link in
the #75 row / seam bucket is withdrawn.

## No claim banked
A false-lead closure (prevents a wasted runpod PSLQ attempt); the salvage is a one-line structural note,
recorded in the card and `regularization-freshness`.
