# Independent Euler–Wold Krein Xi-residue transport

- Formal module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldIndependentKreinXiResidueTransport.lean`.
- Capstone: `sourceHorizontalEulerWoldIndependentKreinXiResidueTransport`.
- One bivariate pre-selection source has pure `(3,0)` Euler and `(0,3)` Wold third jets; mixed `(3,3)` jet is zero. This is intrinsic independence, not external tags.
- Literal Euler depth deformation proves exact negative `(log p)^3 (k+1)^2 p^(-(k+1))` coefficient.
- Both jets pass through same two completed Gamma gauges; selected polar factor is forced to `2` and target remains `routePJuliaSharedOrientationOrbitBlock`, preserving all four orientations.
- Joint `Fin 3` bundle retains existing BV signed endpoint landing as component 0; actual `XiRightSupportFiber` sum equals exact `xiSupportMultiplicity` multiple.
- Euler selected coefficient is negative, Wold selected coefficient positive.
- Faithful linear grade-forgetting is exactly `-2 D_N/H_N^3 • O(c)`, nonzero/strictly negative at every finite clock and tending to zero. Therefore next open core is source-derived nonlinear/non-spectral physical selection retaining Euler order-one action while carrying Wold regulator data faithfully.
- Exact leaf build passed. `#print axioms` for capstone and key theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Card promoted to `docs/drafts/pipeline/3-formalized/source-horizontal-euler-wold-independent-krein-xi-residue-transport.md`; frontier updated.
- Global static lint currently fails only on six unrelated pre-existing unreachable HTGeometry modules.