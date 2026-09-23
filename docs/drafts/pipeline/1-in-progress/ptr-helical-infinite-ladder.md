# PTR source helical infinite-ladder seam

- **ID:** PTR-HELICAL-LADDER
- **Stage:** 1-in-progress
- **Type:** closed constitutive source law; physical boundary bridge open
- **Chain:** rotating temporal-Maxwell constitutive source → infinite Floquet/OAM boundary operator → prime conormal eigen-distribution → independent defect confinement → RH.

## Corpus basis and test

`PhotonicTimeCrystalDynamicChirality` proves the rotating helicities and the common integer action on frequency and OAM. `PhotonicPrimeCyclicSlabParabolicRealization` fixes the nonzero prime helical material coefficient but only projects its first order-four channel. `PhotonicFiniteOAMPortLadderNoGo` excludes a faithful three-port ladder. Tested conjecture: multiplication by the literal positive helical material harmonic sends the full two-variable Floquet Fourier mode at every integer grade `n` exactly to grade `n+1`; its negative companion sends `n` to `n−1`.

## Outcome and route consequence

`PhotonicHelicalInfiniteLadderCore` proves both all-grade mode shifts, the positive shift on every finite Fourier packet, and injectivity/infinite range of the physical OAM label `ℓ+n m` whenever `m≠0`. Direct Lean and targeted module build pass. Thus no finite set of **absolute OAM labels** carries the whole literal helical ladder. This closes constitutive sideband selection and upgrades the prior three-port obstruction to arbitrary finite absolute-label carriers. An independently derived physical mode-folding law remains possible. The pre-existing bare positive-step theorem already ruled out finite closed Floquet truncations; this card does not claim that again as new.

Open hard seam: derive the infinite boundary map from rotating-cylinder Maxwell equations, including modal overlaps and interface conditions; prove it selects the prime conormal generalized eigenfamily and independently confines the defect. Neither this algebraic material multiplication nor the source-defined conormal multiplier proves those facts. Prime specialization was attempted in scratch but its large source-module import exceeded the short Lean-check budget, so no prime-specialized theorem is claimed.
