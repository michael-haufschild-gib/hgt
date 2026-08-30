# S6F finite matrix-channel contravariant route killed (2026-08-30)

Closed unconditional Lean capstone `HTGeometry.modularThetaSourcePositive_no_D1_finiteMatrixContravariantCarrier`.

Result: for every nonempty finite channel dimension, neither canonical left nor right matrix-coefficient action supports a positive-definite matrix-valued contravariant source-sl2 polynomial carrier containing actual D1. Proof uses existing D1 vacuum string: nonzero u,v with Eu=0, Fv=u, Ev!=0. Contravariance on (u,v) makes PosDef <u,u> annihilate coefficient, so matrix invertibility forces coefficient=0. Contravariance on (v,Ev) then makes PosDef <Ev,Ev>=0, contradiction.

Module: `formal/GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveD1MatrixContravariantNoGo.lean`; wired into `formal/GaloisForLFunctions/HTGeometry.lean`.

Verification: direct `lake env lean` clean; targeted `lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1MatrixContravariantNoGo` passed; `#print axioms` reports only propext, Classical.choice, Quot.sound. Global lint still fails because many unrelated concurrent modules are unwired, but this module disappeared from reachability errors after wiring.

Route consequence: kills finite non-scalar Gram/Shapovalov escape toward native rank-three D1. Survivors: genuinely infinite-channel, localized/singular, indefinite/Krein, or direct cross-scale Hankel/singular-face geometry. TCD-D1-BOUNDARY-FLUX remains open route-closing core.

Research card entry: `docs/drafts/pipeline/1-in-progress/theta-rank-three-direct-parabolic-determinant.md`.