# Peripheral components inherit covering models and analytic caps

- **ID:** PERIPHERAL-COMPONENT-BRIDGE-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Source components over open punctured-disk charts inherit covering projections and the power/exponential classification. A continuous punctured lift of an analytic zero forces the finite power model and extends with exact order identity.

## Complete paper proof

[PROVED HERE, relative to the checked classification and local extension]

Restrict a covering to a clopen subset C of its source. At any base point choose a connected open subset W of an evenly covered neighborhood. For each sheet, the inverse image of C under its continuous section over W is clopen in connected W. Membership is therefore constant. Retain exactly the sheet indices belonging to C. Restricting the original trivializing homeomorphism gives the required trivialization of the restricted map; this works when the retained index set is empty.

Connected components are clopen in locally connected spaces. Restricting first to an open target subset preserves the covering property and local connectedness, so the same argument applies to each component above it. Local path connectedness makes that component path connected. A punctured-disk target chart now allows the checked power/exponential classification. The analytic zero theorem excludes its exponential alternative and supplies the analytic cap coordinate and multiplicity identity.

A continuous map from a connected source lands in the component of any chosen image point. `continuousMapToComponent` packages this restriction without changing the original map.

## Topological inputs for the actual subgroup cover

The subgroup projection separates distinct points in a fiber by the previously checked separation theorem. Points in different fibers are separated by inverse images of disjoint base neighborhoods. Thus a Hausdorff base makes the subgroup cover Hausdorff.

The quotient map from the universal source is open and surjective; images of a countable basis give a countable basis downstairs. In an open piece of this locally connected, second countable cover, the component quotient is both discrete and separable. Hence it has at most countably many components. This controls the finite-cap index set.

## Verification

- `HTGeometry/CoveringComponentRestriction.lean`: three public theorems; leaf build PASS, 1427 jobs.
- `HTGeometry/SubgroupCoverTopology.lean`: three public theorems; leaf build PASS, 1710 jobs.
- `HTGeometry/PeripheralCoverComponent.lean`: four public declarations; leaf build PASS, 3439 jobs.
- All ten public declarations have standard-only axiom audits; `/tmp/hgt-covering-clopen-axioms.log`, `/tmp/hgt-subgroup-cover-topology-axioms.log`, `/tmp/hgt-peripheral-component-axioms.log`.
- All three final actual-source checks PASS with empty logs. All modules wired into `HTGeometry.lean`; index refreshed.
- Global lint reports seven unrelated unreachable modules: RHTower.{PaperCircleLocalizationLimit,StretchedBoseDefect} and HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra}. No forbidden declaration or own-module errors; `/tmp/hgt-peripheral-lint.log`.

The global completed surface, analytic atlas and source gluing remain in progress. No external novelty claim, web source, or numerical experiment.
