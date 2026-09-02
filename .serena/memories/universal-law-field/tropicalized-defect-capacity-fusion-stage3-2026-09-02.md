# ULF-DSA-002 Stage-3 promotion, 2026-09-02

Card promoted to `docs/drafts/pipeline/3-formalized/universal-law-field/direct-subunit-anchor/tropicalized-defect-capacity-fusion.md`.

Lean module: `formal/GaloisForLFunctions/RHTower/DirectSubunitEscapeCapacityFusion.lean`.

New exact surface:
- `xiRight_tropicalizedDefectCapacityFusion`: packages escape multiplicity one and strict Euler/cubic energy sandwich.
- `gammaSewnSynchronizedRecoveryQuadraticCost_singleton`: singleton synchronized curvature is `(3/8) log(p)^2`.
- `xiWardCubicFormationMetricAnomalyTraceWeight`: normalized formation anomaly.
- `xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero_eq`: exact source-weight times resonant-excess formula.
- `xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source` and subtraction equivalent.
- depth-zero companion and formation anomaly are nonsummable; source slice and exact relative remainder are summable.
- `xiRight_tropicalizedDefectCapacityFormationRelativeCompletion`: complete second capstone.

No hypotheses were added; parameters are exactly typed `XiRightZeroCopy` and prime indices from the card. Module imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella was not built.

Verification:
- direct `lake env lean` pass;
- targeted leaf build pass, 13190/13190 jobs;
- axioms for all 11 new declarations: only `propext`, `Classical.choice`, `Quot.sound`;
- corpus research indexes both capstones;
- formal lint has no issue for target, but global exit 1 persists from unrelated unreachable modules;
- `git diff --check` pass;
- temporary scratch files removed and no Lean/lake process remains.

Open core preserved, not formalized: pre-divisor prime-mixed relative polarization/index selection yielding `E(q) ≤ B_Euler`; this is the RH-strength missing edge.