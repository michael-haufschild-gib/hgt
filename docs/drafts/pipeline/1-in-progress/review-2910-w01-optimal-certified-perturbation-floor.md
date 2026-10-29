# Optimal floor from the certified Trans-Metzler estimates

- **ID:** review-2910-w01-optimal-certified-perturbation-floor
- **Stage:** 1-in-progress
- **Type:** THEOREM (formalized certified-bound optimization; analytic-constant audit open)
- **Source:** [W01](../../../reports/review-2910/obstacles-summary.md)
- **Statement:** Optimize the exact existing reference/coercivity/perturbation inequalities and
  transfer their full open positive range to the actual complete Weil matrices.

## Paper argument

[FORMALIZED] Let M=‖x‖² and D=poleDefect(x). The current source proves
`E≥M/25`, `E≥−2100000M+D/1024000`, and
`F≥E−e(D+M)`, with `e=2000δ+o(1)` for overlap at most 1+δ.
For `0≤e≤1/1024000`, combine the first inequalities with weights
`1−1024000e` and `1024000e`. This yields

`F≥(1/25−Ke)M`, where `K=1+1024000(2100000+1/25)`.

The exact optimal asymptotic floor furnished by these inequalities is
`L(δ)=1/25−2000Kδ`. Indeed, the scalar data
`M=1`, `D=K−1`, `E=1/25`, `F=1/25−Ke` attain all relevant inequalities.
Thus their positive range has exact supremum
`δ*=1/(50000K)=1/107520002048050000`.
The existing width, geometry and coercivity constraints are all weaker than this constraint.
For any ε>0, choose a positive tail allowance at most ε/K and half the defect reserve. Since
`C_short/log(N/3)→0`, the actual complete Weil matrix eventually has floor `L(δ)−ε`.
For δ<δ*, choose ε=L(δ)/2 to obtain positive definiteness.

The optimum here is for the displayed, already-proved estimates. It is not an upper bound on
actual positivity, nor a claim that every analytic constant in the underlying method is optimal.
Any further improvement must sharpen at least one estimate rather than change their convex weights.

## Verification

- [x] Read exact reference floor, coercivity, and perturbation statements and their domains.
- [x] Optimal algebraic floor and sharpness formalized.
- [x] Actual-matrix transfer over the full open certified range checked.
- [x] Transitive axioms and umbrella import audited.

Leaf `TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean` passed
`lake --old env lean GaloisForLFunctions/TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean`.
All three terminal declarations report only `propext`, `Classical.choice`, `Quot.sound`.

## Remaining scope

The spectral-floor argument uses adjunction energies strictly above 1/20 but states only 1/25.
Consequently the optimum of these three displayed inequalities does not yet certify the largest
reach of the underlying analytic proof. Generalize its reference floor before closing W01;
also retain the c-dependence of the charge reserve when auditing the coercivity constants.
