# HC46 HB third-order cokernel threshold rigidity (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderCokernelThresholdRigidity`.
Card: `docs/drafts/pipeline/3-formalized/hb-third-order-cokernel-threshold-rigidity.md`.

Corpus-led advance: HC45's sharp one-third lower bound is rigid. For complex channels `a+b+c=-t`, simultaneous norm bounds `≤‖t‖/3` saturate nested triangle inequalities; strict convexity and SameRay force `a=b=c=-t/3`. Exact dichotomy: some channel strictly exceeds threshold or unique aligned equipartition. Applied to actual critical-line unit BM incidence with nonzero absorbed seed: strict branch selects a quantitatively dominant nonexact physical channel; equipartition branch fixes all three projections to `-AIME/3` and proves all three channels nonexact. No diffuse subthreshold source configuration survives.

Audit: direct `lake env lean` passed; target-only build passed 12,750 jobs; all four public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; global lint has no HC46 error and remains red only on unrelated unreachable modules. Bounded primary-source audit found no exact match. Frontier map remained untouched.