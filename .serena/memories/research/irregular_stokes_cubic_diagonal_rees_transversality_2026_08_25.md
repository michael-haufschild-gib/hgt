# Cubic Xi diagonal-Rees transversality (2026-08-25)

Module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicDiagonalReesTransversality.lean`.
Card: `docs/drafts/pipeline/3-formalized/route-p-cubic-diagonal-rees-transversality.md`.

[LEAN-PROVED] For every coefficient-generated cubic Xi landing at completely contracted threshold parameter:
1. total canonical threshold block coarea is strictly positive;
2. unit-Rees Witt value minus cubic Xi target equals that total block coarea;
3. unit-Rees value is therefore strictly above target.

Mechanism: landing charge is nonzero because target residual is negative. Some local orbit charge is nonzero. Surjectivity of branch-to-orbit map makes pulled-back branch vector nonzero. Canonical positive pendant singleton cuts make its block energy strictly positive; all other local blocks are nonnegative. Global Rees decomposition cancels terminal and physical-rank terms between parameters zero and one, leaving exactly block coarea.

Consequences:
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber`;
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber`.

Representation lesson: fixed-charge coefficient-generated cubic Xi crossing is necessarily Rees-transverse. A viable irregular-RH producer must change charge/carrier or break canonical two-scale Rees covariance. Earlier terminal-energy theorems on raw Rees-rigid fiber are valid but vacuous and were documented as such.

Targeted module check passed. Five new declarations depend only on `propext`, `Classical.choice`, `Quot.sound`. Umbrella import added. Frontier map untouched. Scientific novelty unverified.