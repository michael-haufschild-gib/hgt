# Open-obstacle contributions

- **Scope:** `docs/reports/review-0811/obstacles-summary.md`, §2.2.
- **Target:** At least 250 distinct significant mathematical contributions, each proved in Lean and audited. Helpers and corollaries of one result count together.
- **Verified:** 3 / 250. Original obstacles remain open unless explicitly closed below.

| # | Obstacle | New result | Certificate |
|---|---|---|---|
| 1 | B13, positive annihilation | Order `r+1` imposes Chebyshev mass cost; for `r≥1`, supported logarithmic frequency `≥log 2+2(log 2)r²/(H−1)` | [Proof and Lean audit](../3-formalized/annihilator-multiplicity-chebyshev-cost.md) |
| 2 | B13, B112, reflected pairs | Sharp hyperbolic mass cost, positive extremizers at every even bandwidth, and strict unattained floor `2^δ`; reflection forces no uniform excess | [Proof and Lean audit](../3-formalized/reflected-pair-annihilator-hyperbolic-cost.md) |
| 3 | B13, B112, prescribed heights | Explicit bandwidth-independent mass gap; reflected-pair mass approaches `2^δ` at fixed height `γ` iff `cos(γ log 2)=-1` | [Proof and Lean audit](../3-formalized/fixed-height-annihilator-mass-gap.md) |

Next conjecture: [multiplicity and the hyperbolic mass budget](../0-backlog/annihilator-multiplicity-hyperbolic-budget.md). Unproved and uncounted.
