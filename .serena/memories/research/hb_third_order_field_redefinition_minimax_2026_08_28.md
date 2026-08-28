# HC47 HB third-order field-redefinition minimax classification (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderFieldRedefinitionMinimax`.
Card: `docs/drafts/pipeline/3-formalized/hb-third-order-field-redefinition-minimax-classification.md`.

Corpus-led correction and survivor: quadratic field redefinition makes individual stationary/second-harmonic/direct projections coordinate-dependent. New exact affine law is `(a,b,c) -> (a-delta,b-epsilon,c+delta+epsilon)`. Total is invariant; equal-total triples admit unique transfer coordinates. Every orbit cancelling target `t` has peak norm at least `‖t‖/3`, with unique minimizer/equipartition `(-t/3,-t/3,-t/3)`. Actual Einstein Taylor field-redefinition formulas realize this redistribution. Closed scalar witness changes direct projection from 0 to 3/2 while preserving full total. Thus HC45 one-third existential burden survives coordinate changes; HC46 equipartition is unique minimax gauge representative, not invariant physical channel identity.

Audit: direct `lake env lean` passed; target-only build passed 12,752 jobs; all nine public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; global lint has no HC47 error and remains red only on unrelated unreachable modules. Bounded primary-source audit found no exact match. Frontier map remained untouched.