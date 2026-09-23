# PTR fixed-wavenumber geometric Maxwell test

- **Stage:** 1-in-progress.
- **Chain:** rotating Maxwell material → infinite Floquet/OAM boundary equations → prime conormal eigenfamily → independent defect confinement → RH.
- **Corpus basis:** `PhotonicTemporalMaxwellSlabRealization` proves the fixed-spatial-wavenumber `(D,B)` equations `D'=k B/μ`, `B'=-k E` with `D=εE` for constant slabs. `PhotonicFiniteDressedLaurentNoGo` identifies the full rotating material symbol `P(T)=d+a(T+T⁻¹)`. `PhotonicTimeCrystalDynamicChirality` gives sideband frequency `ω+nΔ`; `PhotonicPrimeCyclicSlabParabolicRealization` gives geometric conormal sidebands.

## Conjecture and falsifier

For a nonzero fixed spatial wavenumber `k` and nonzero drive frequency `Δ`, no nonzero geometric sequence `E_n=λ^n` solves the exact coefficient equations of `(εE)''+(k²/μ)E=0` for all Floquet grades. The Laurent material action makes `D_n=P(λ)E_n`, so the equation would force `(ω+nΔ)² P(λ)=k²/μ` for every `n`. Grades `0,1,2` have second difference `2Δ²P(λ)=0`, forcing `P(λ)=0` and then `k=0`. A counterexample with `kΔλ≠0` falsifies the conjecture.

If closed, this kills direct identification of the prime geometric conormal with an electric-field amplitude in the **fixed-`k` scalar temporal-Maxwell extension** of the existing two-slab model. It does not kill PTR with grade-dependent spatial dispersion/OAM radial modes, a vector-valued boundary state, or a singular quotient. Need distinguish formal coefficient equations from a fully derived distributional Maxwell boundary trace.
