# The Robin diagonal of the rational-torus Green sum

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: identify an actual global Robin finite part for the weighted Green kernel.
- **Target:** Prove that the termwise Robin value of the convergent torus sum is its genuine diagonal finite part, with the point-source normalization fixed.

## Proposed statement

Let `P(x,y)` be the regularized Green sum indexed by `q∈ℚˣ`, and let
`x=(z,u)`, `y=(w,u)` lie in one archimedean leaf. The proposed limit is

`P(x,y)/2 − 1/(4π d(z,w)) → P(x,x)/2` as `w→z`, `w≠z`.

The factor two comes from the two rational parameters `±1` acting trivially.
The resulting diagonal should descend to the rational-torus quotient.

## Mechanism and unresolved inputs

Profile summability makes every finite-vertex torus stabilizer finite. A
finite subgroup of `ℚˣ` consists of `±1`, suggesting the exact stabilizer
classification without a separate local-tree calculation. After splitting
these two terms, the strictly tempered profile dominates the remaining
orbit sum uniformly in the archimedean points. Continuity of each remaining
entry and dominated convergence would then commute the Robin limit with
the sum. The two central terms use the proved local Green finite-part limit.

Still required: formal stabilizer classification and the central action;
continuity and the dominated orbit limit; the precise punctured diagonal
limit and quotient descent. No global Robin-limit theorem is claimed yet.

## Boundary

This concerns the standard branch of the specified weighted operator. It
asserts neither a Bochner-integral inverse on the full rational `SL₂`
quotient nor identification with Weil's diagonal. The accepted invariant
gluing obstruction applies to that proposed identification.
