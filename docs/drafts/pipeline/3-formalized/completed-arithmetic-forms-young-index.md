# Complete Weil index ceiling throughout the certified prefix range

- **ID:** completed-arithmetic-forms-young-index
- **Stage:** 3-formalized
- **Type:** THEOREM

Fix `1≤d<c_*`, where `c_*` is the unique zero of the optimized complete
Trans-Metzler Young floor. There is a prefix horizon `M₀(d)` such that, for
every `M≥M₀(d)`, `N≥M`, and `c>0` with `cM=dN`, each strictly negative
subspace of the actual complete length-`N`, overlap-`c` Weil form has dimension
at most `N−M`.

The exact principal-prefix identity identifies its matrix with the complete
length-`M` source at overlap `cM/N=d`. The corpus proves eventual positive
definiteness for every fixed `d` in this full certified range. Restriction of
a negative subspace to its tail is therefore injective, giving the stated bound.

The normalized tail dimension is exactly `1−d/c`. This uses the complete
certified prefix range, including `d>1`; the one-third bound at `c=3/2`
and `d=1` is a concrete benchmark. The residual Schur sign remains a distinct
arithmetic question.

Dependencies: `plateauPrefixBlock_eq`,
`eventually_completeWeilMatrix_posDef_before_young_boundary`, and finite-dimensional
tail restriction. The source positivity premise is discharged at the stated
parameter range; no residual sign estimate is assumed.

Lean: `CompletedArithmeticForms/WeilPrefixIndex.lean`,
`eventually_completeWeil_negative_subspace_dim_le_young_tail`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
