# An analytic zero forces a finite power chart for its punctured lift

- **ID:** ANALYTIC-ZERO-COVER-CAP-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** A continuous punctured lift of an analytic germ vanishing at a through a connected punctured-disk cover forces that cover to be a positive power model; its chart coordinate extends analytically by zero with the exact multiplicity identity.

## Complete paper proof

[PROVED HERE, relative to the corpus continuous-root upgrade and checked punctured-root extension]

A continuous function whose positive integer power is a nonvanishing analytic germ is analytic locally, by the corpus continuous-root theorem. Applying this at each nearby nonpuncture point upgrades continuous punctured roots to holomorphic roots. The checked root-extension theorem then extends the root by zero and gives ord(f)=n·ord(root).

There cannot be a continuous logarithm ℓ with exp(ℓ)=f on a punctured neighborhood of a zero a. Such an equality makes f nonzero there, ruling out a locally zero germ. Thus f has a positive finite order m at a. The continuous root exp(ℓ/(m+1)) becomes holomorphic by the preceding upgrade. Root extension would make m+1 divide m, a contradiction.

Apply the checked punctured-disk cover classification to the cover carrying the lift. Its logarithmic alternative would supply precisely the forbidden continuous logarithm. Its power alternative supplies a continuous root, which extends analytically as above. Neither finite sheet count nor an existing analytic atlas on the covering source is assumed.

## Verification and scope

- Module `HTGeometry/AnalyticZeroCoverCap.lean`, four public theorems; main theorem `analytic_zero_lift_has_power_chart`.
- Production leaf build PASS, 3437 jobs, warning-free.
- All four public declarations pass the standard-only axiom audit in `/tmp/hgt-peripheral-axioms.log`.
- Final actual-source `lake env lean` PASS, empty `/tmp/hgt-AnalyticZeroCoverCap-final.log`.
- Wired into `HTGeometry.lean`; index refreshed. Global lint reports seven unrelated unreachable modules, no own-module or forbidden-declaration errors; `/tmp/hgt-peripheral-lint.log`. Exact list appears on `peripheral-component-bridge.md`.

This removes the separate local meridian/winding calculation from source-lift capping. The global surface and actual source extension still require component restriction, topology, atlas and gluing proofs. It is not an RH theorem or a novelty certification against external literature. No web sources or numerical experiments.
