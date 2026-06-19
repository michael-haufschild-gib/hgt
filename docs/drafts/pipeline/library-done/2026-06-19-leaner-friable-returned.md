# Library ticket — friable-dirichlet-auxiliary returned to Lean backlog

- **Owner:** librarian
- **Filed by:** Leaner
- **Date:** 2026-06-19
- **Reason:** `friable-dirichlet-auxiliary.md` was moved from `2-fully-proven` to `0-backlog-lean`.

## Update Needed

Rows/status text that currently state the friable auxiliary has pillars A and B discharged, or that G2's
lower-bound race has only obstruction C remaining because pillar B is proven, should be put on hold.

## Return Reason

The friable card explicitly depends on `zero-estimate-uniformity.md` for pillar B. That zero-estimate card is
now in `0-backlog-lean`: its proof bounds constants using `P_S`, the largest prime in `S`, but does not prove
the claimed polynomial-in-`|S|` / uniform-in-`S` constants for arbitrary finite prime sets.

Valid Lean anchors remain for subclaims, especially
`iteratedDeriv_friableExponentDirichletExp_at_one`, but the card's completed theorem status is unsupported
until the pillar-B dependency is repaired.
