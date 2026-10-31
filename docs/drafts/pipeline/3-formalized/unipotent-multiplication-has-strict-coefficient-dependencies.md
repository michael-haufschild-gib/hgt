# Unipotent multiplication has strict coefficient dependencies

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The lower-right entry through degree `N` depends on the upper-left
  and lower-left entries through `N`, but on the upper-right entry only below `N`.
  The three free-entry multiplication defects have explicit zero-constant factorizations.

## Proof

For `g=(a,b;c,d)`, the audited coordinate equivalence gives
`d=invOfUnit(a,1)(1+bc)`. An inverse coefficient through `N` depends only
on coefficients through `N`, by the existing principal-unit inverse recursion.
In coefficient `n` of `bc`, the convolution term using `bₙ` is zero because
`c₀=0`. Every other term uses `b` below `n` and `c` through `n`.
The outer convolution proves the stated dependence of `d`.

For `h=(A,B;C,D)`, direct multiplication gives

- `b(gh)−b−B=(a−1)B+b(D−1)`;
- `c(gh)−c−C=c(A−1)+(d−1)C`;
- `a(gh)−a−A+1=(a−1)(A−1)+bC`.

All indicated principal-unit differences and lower-left entries have zero
constant coefficient. In a product with one zero constant, the corresponding
current-degree boundary term vanishes; with two zero constants both boundary
terms vanish. These are exact finite-convolution identities over every
commutative ring. The full interlaced-stream triangular law is a separate step.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientPrefixes.lean`:
`unipotentCoefficient_lowerRight_congr`,
`unipotentCoefficient_upperRight_defect`, `unipotentCoefficient_lowerLeft_defect`,
`unipotentCoefficient_upperLeft_defect`. Direct Lean check passed. Transitive axiom audits: `propext`, `Classical.choice`, `Quot.sound`.
