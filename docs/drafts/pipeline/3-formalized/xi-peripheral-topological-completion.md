# Actual marked-cover completion with exact peripheral projections

- **ID:** XI-PERIPHERAL-TOPOLOGICAL-COMPLETION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Every subgroup cover of the actual marked target has an explicit completion filling precisely its positive-power peripheral components. This space is Hausdorff, second countable and path connected, its old body induces a fundamental-group surjection, and its projection remains a covering away from the two marks.

## Complete paper proof

[PROVED HERE, relative to the checked covering classification and cap-completion construction]

Index the actual marks 0 and −1 by Bool. On the marked target, take the radius-1/4 neighborhoods of these marks and normalize by ζ=4(z−b). The inverse b+ζ/4 avoids both marks for ζ∈D*. The two neighborhoods are disjoint by the triangle inequality. These are explicit homeomorphic punctured-disk charts with exact inverse and projection identities.

For a subgroup H of the transported modular-cover deck group, the subgroup quotient is Hausdorff and second countable, and its projection is a covering. Index connected components above the two target charts by their connected-component quotient types. These index types are countable. A chosen representative names each component. Its image in the old cover is open. Different indices give disjoint regions: either their target charts differ, or their connected components inside one preimage differ.

Each component has a power or exponential model by the checked classification. Retain exactly indices admitting a positive power model, and choose one such model per retained index. This is a subtype of the component index, so multiple choices of a chart cannot create multiple cap indices. The full unit disk minus its center is explicitly homeomorphic to D*. Compose that identification with the inverse chosen power chart and the component-to-region homeomorphism. This constructs the actual `PointCapData`.

The projection in the ith full cap is exactly b+ζⁿ/4, including ζ=0. Hence the extended projection is continuous. Old projected values avoid both marks, whereas a new point projects to its mark. The checked projection-separation theorem proves Hausdorffness. The countable cap index proves second countability. The full disk is contractible and its punctured part path connected, so the checked cap theorem proves path connectedness and old-body fundamental-group surjectivity.

The completed projection is unmarked exactly on the old body. Its old inclusion therefore gives an explicit homeomorphism from the original cover to the unmarked part of the completion. Transport the original covering projection through this homeomorphism to prove the completed projection is still a covering over the actual twice-punctured target.

## Scope

No finite-sheet, compactness, asymptotic-value or RH premise was supplied to this cover-family construction. H is an arbitrary subgroup parameter; the previously proved exact-image factorization supplies the actual Xi subgroup. An arbitrary H need not give a simply connected completion. The global extended Xi lift and its simple-connectedness deduction remain separate obligations. No external novelty certification or web sources.

## Verification

- `RHTower/XiPeripheralTargetCharts.lean`: twelve public declarations; production leaf build PASS, 11121 jobs.
- `HTGeometry/PuncturedDiskCapModel.lean`: eight public declarations; leaf build PASS, 2429 jobs.
- `RHTower/XiPeripheralComponents.lean`: twenty-five explicit public declarations; leaf build PASS, 11129 jobs.
- `RHTower/XiPeripheralCaps.lean`: sixteen public declarations; leaf build PASS, 11152 jobs.
- All sixty-one declarations pass the standard-only axiom audit, `/tmp/hgt-xi-actual-caps-axioms.log`.
- All four final actual-source `lake env lean` checks PASS with empty logs, `/tmp/hgt-{XiPeripheralTargetCharts,PuncturedDiskCapModel,XiPeripheralComponents,XiPeripheralCaps}-final.log`.
- Wired into their theorem-area umbrellas and indexed. Latest lint snapshot appears on the parent card; no own-module or forbidden-declaration errors.
