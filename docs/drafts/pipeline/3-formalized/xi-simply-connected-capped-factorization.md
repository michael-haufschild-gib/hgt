# Actual Xi factors through a simply connected completed image cover

- **ID:** XI-CAPPED-SIMPLY-CONNECTED-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/XiContinuousCappedLift.lean`, `HTGeometry/CappedSimplyConnectedFactorization.lean`, `RHTower/XiSimplyConnectedCappedFactorization.lean`.
- **Statement:** Actual Xi factors continuously through a simply connected capped subgroup cover of the twice-punctured plane, with no mathematical hypotheses.

## Contribution and limits

This discharges the global source-extension and simple-connectedness obligations of `xi-image-cover-analytic-capping.md`. The completed space already has a checked Hausdorff, second-countable topology, an exact positive-power projection in every attached disk, and a covering projection away from 0 and −1. This theorem adds an actual lift from the whole source plane and proves simple connectedness of the particular exact-image completion.

The analytic atlas is now also verified in `xi-image-cover-analytic-capping.md`. Intrinsic uniformization and exterior analytic classification remain separate obligations. Neither exact Xi target-monodromy surjectivity nor RH follows from this theorem alone. External novelty is unverified under the corpus-only instruction.

## Complete paper proof [PROVED HERE]

Choose the exact-image cover Y and its actual source lift F from `xi_exact_image_cover_factorization`. Its induced map on fundamental groups is surjective. Let M be the checked completion of Y by all finite peripheral components.

At a deleted source point a, Xi(a) is one of the two marks b. The checked isolated-mark theorem gives a small punctured source disk that avoids both deleted fibers and maps into the b-target disk. This punctured disk is path connected, so its continuous lift lies in one peripheral component. The checked analytic-zero component theorem forces this component to admit a positive power chart; hence it is one of the components capped in M.

Use the chart already selected by the cap data, not a newly selected chart. Its coordinate u is continuous on the punctured source disk and satisfies uⁿ=4(Xi−b). The checked root-extension theorem proves that replacing u(a) by zero is analytic at a. The coordinate has norm less than one throughout its arbitrarily extended domain, and replacing its value by zero preserves that property. Composing this disk-valued extension with the cap map gives a continuous local lift at a, agrees with the old lift near a, and projects to Xi(a) at a.

Choose such a local extension for each deleted point. Define G to equal the old lift on the old source and the chosen center value at each deleted point. The old source is open. Each deleted point has a neighborhood containing no other deleted point, so G agrees there with its chosen local extension. Thus G is globally continuous, agrees with the old lift and projects exactly to Xi. This argument is formalized by the checked punctured local gluing lemma; no compatibility or existence assumption is added.

The old inclusion Y→M induces a surjection on fundamental groups: identify Y with its open body image, then use the checked body-inclusion surjection. Consequently the composite old-source→Y→M induces a surjection. This composite equals old-source→C→M through G. Every source loop dies after mapping into the simply connected plane, so every loop class in M is trivial. Path connectedness of M transports this conclusion to all basepoints, proving M simply connected.

## Lean certificate

Main theorem: `RHTower.XiMarkedMonodromy.xi_simplyConnected_capped_factorization`.

All three modules are wired. Production leaf builds pass. All seven explicit public declarations have axiom audits containing only `propext`, `Classical.choice`, `Quot.sound`. All three final actual-source checks pass with empty logs:

- `/tmp/hgt-CappedSimplyConnectedFactorization-final.log`
- `/tmp/hgt-XiContinuousCappedLift-final.log`
- `/tmp/hgt-XiSimplyConnectedCappedFactorization-final.log`

Audit input/output: `/tmp/hgt-xi-simply-connected-axioms.lean`, `/tmp/hgt-xi-simply-connected-axioms.log`. All modules are indexed. Latest global lint has eight unrelated unreachable-module errors and no own-module or forbidden-declaration errors; full snapshot in `xi-image-cover-analytic-capping.md`.

## Log

- 2026-10-09 — complete paper argument, production formalization, axiom audit and final actual-source verification.
