# Unqualified regulator-uniform reciprocal-amplitude resistance

- **ID:** selberg-uniform-resistance-shortcut-29
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement tested:** Local smoothness and positive square regularization alone keep reciprocal-amplitude path resistance bounded as the regulator vanishes.
- **Scope:** The exact local nodal profile h(x)=x disproves this unqualified statement. It is not a Maass counterexample; a Maass-specific global estimate would require additional proved source information.

## Killing mechanism and strongest positive survivor

For `r_e=sqrt(x²+e²)`, actual FTC gives

`integral_{-1}^1 1/r_e = 2arsinh(1/e) = 2log(1+sqrt(1+e²))-2log(e)`.

Therefore resistance tends to infinity, its finite part after adding `2log(e)` tends to `2log 2`, and the capacity coefficient `2/resistance` tends to zero. The complete singularity classification is the positive survivor, beyond merely negating boundedness. Every statement is formalized in `SelbergNodalResistance`.

## Actual-source positive salvage

For the actual smooth augmented Maass family, fixed endpoint separation survives for every sufficiently small regulator. On the same fixed ordered path, the proved theorem retains both

`pathEnergy > 2/pathResistance`

and

`sum_j (integral |partial_x U_j|)² > 2`.

The second inequality does not introduce resistance and retains a regulator-independent source variation cost. It is not a two-dimensional quarter estimate and is not mislabeled as vector geodesic length. The added coordinate's exact nonzero weighted mean remains present in the chord calculation.

## Audit

The exact nodal classification and actual-source survivor have dependency-closed paper proofs and passed Lean checks. Four serialized target builds passed; all 57 audited public declarations use only standard Lean/mathlib axioms or none. Repository lint is separately limited by unrelated unwired `HTGeometry.FokasLenellsUniformizedFrame`. Main Selberg goal remains active.

[Complete source construction, paper proof, and audit](../3-formalized/selberg-augmented-chord-capacity-and-nodal-resistance.md). [Next live conjecture](../1-in-progress/selberg-quarter-conjecturing-loop.md).
