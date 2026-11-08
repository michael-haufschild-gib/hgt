# Open-obstacle contributions

- **Scope:** `docs/reports/review-0811/obstacles-summary.md`, §2.2.
- **Target:** At least 250 distinct significant mathematical contributions, each proved in Lean and audited. Helpers and corollaries of one result count together.
- **Verified:** 6 / 250. Original obstacles remain open unless explicitly closed below.

| # | Obstacle | New result | Certificate |
|---|---|---|---|
| 1 | B13, positive annihilation | Order `r+1` imposes Chebyshev mass cost; for `r≥1`, supported logarithmic frequency `≥log 2+2(log 2)r²/(H−1)` | [Proof and Lean audit](../3-formalized/annihilator-multiplicity-chebyshev-cost.md) |
| 2 | B13, B112, reflected pairs | Sharp hyperbolic mass cost, positive extremizers at every even bandwidth, and strict unattained floor `2^δ`; reflection forces no uniform excess | [Proof and Lean audit](../3-formalized/reflected-pair-annihilator-hyperbolic-cost.md) |
| 3 | B13, B112, prescribed heights | Explicit bandwidth-independent mass gap; reflected-pair mass approaches `2^δ` at fixed height `γ` iff `cos(γ log 2)=-1` | [Proof and Lean audit](../3-formalized/fixed-height-annihilator-mass-gap.md) |
| 4 | B13, B112, full zero divisor | Complete Green-weighted divisor consumes logarithmic mass drop; optimized conjugate-pair test forces exponential multiplicity cost without a bandwidth cutoff; exact-order witnesses attain exponential growth | [Proof and Lean audit](../3-formalized/annihilator-multiplicity-hyperbolic-budget.md) |
| 5 | B13, B112, annihilator division | Canonical quotient coefficients have unbounded excursions of both signs at every nonnegative exponent below a right-hand zero; absolute weighted mass diverges at the endpoint | [Proof and Lean audit](../3-formalized/annihilator-division-forces-coefficient-oscillation.md) |
| 6 | B13, B112, initial heat energy | Exact finite or infinite initial trace; bounded heat energy iff initial squared upper-depths are summable; finite mass forces `t N(t)→0` | [Proof and Lean audit](../3-formalized/the-initial-trace-of-heat-depth-energy.md) |

Candidate: [elapsed heat pays for surviving pairs](elapsed-heat-pays-for-surviving-pairs.md).
