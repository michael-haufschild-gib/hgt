# PTR finite OAM port versus infinite Floquet ladder

- **ID:** ptr-finite-oam-port-infinite-ladder
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `PhotonicTimeCrystalDynamicChirality` locked Floquet frequency/OAM action and literal `Fin 3` OAM port in `PhotonicPrimeCyclicSlabParabolicRealization`
- **Statement:** The literal three-port OAM readout realizes the nontrivial infinite PTR Floquet/OAM ladder faithfully.

## No-go closure

- **Exact killing theorem:** for `m ≠ 0`, the locked labels `ℓ + n m` at grades `n = 0,1,2,3` are injective. A faithful three-port readout would inject `Fin 4` into `Fin 3`, which is impossible.
- **Strongest positive survivor:** `photonicFirstFourOAMLabels_injective` is the exact finite boundary: a valid infinite-ladder boundary model needs an infinite OAM carrier, or a physical mode-folding law that proves its identifications.
- **Route consequence:** the current finite three-port dilation can establish selection at one port layer but cannot be the missing rotating temporal-Maxwell amplitude map. The full PTR open problem remains the literal infinite boundary map followed by defect confinement.
- **Lean status:** dependency-closed source module `PhotonicFiniteOAMPortLadderNoGo.lean`; direct audit and leaf OLean passed. Both claims use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella build intentionally not run.
