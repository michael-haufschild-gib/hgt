# ULF-DJG-1 diagonal law genesis

2026-08-10 field-level pivot after reading `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` as five mechanism laboratories, not routes.

## Certified mechanism
- Paper: `docs/drafts/pipeline/2-fully-proven/universal-law-field/diagonal-law-genesis-mechanics/iterated-diagonal-challenge-genesis-and-filtered-limit-escape-law.md`.
- Lean: `formal/GaloisForLFunctions/HTGeometry/ConstitutiveDiagonalLawGenesis.lean`.
- Stage3: `docs/drafts/pipeline/3-formalized/universal-law-field/diagonal-law-genesis-mechanics/iterated-diagonal-challenge-genesis-and-filtered-limit-escape-law-formalized.md`.
- Wired into `HTGeometry.UniversalLawField`.

For Boolean self-evaluator E, anti-diagonal `δ_E(x)=not E(x,x)` is no existing row. Canonical successor adds one fresh row realizing δ on old columns, preserves every old pair, is minimal among conservative realizations, and is natural under relabelling. Iteration from empty gives `E_n(i,j)=decide(j<i)`. Limit on Nat has only finite-support rows; every finite column horizon of constant true is realized, but no row realizes it globally. Successor of limit has top/infinite-support row, hence is not evaluator-isomorphic to limit. This certifies failure of diagonal succession to commute with cofinal formation.

Verification: warning-free direct elaboration; leaf build 2,997 jobs; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; ULF umbrella audit passes with unrelated replay warnings. No RH or analytic assumptions.

## Field interpretation
This is first exact source-normal grammar-update calibration closing PCG supplied-operation gap in one Boolean laboratory. It is not universal field. Next mechanism is typed recursive diagonalization and successor--repair exchange: challenge output must alter future grammar/admission and interact with bipolar fine/coarse repairs without arbitrary state-indexed oracle. Existing generic same-carrier closure-formation exchange ULF-LSM-3 must not be rediscovered; new comparison must be indexed/change-of-carrier and genuinely recursive.
