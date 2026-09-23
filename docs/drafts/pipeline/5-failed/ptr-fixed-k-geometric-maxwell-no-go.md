# PTR fixed-wavenumber geometric Maxwell test

- **Stage:** 5-failed (fixed-`k` pure-geometric coefficient ansatz only; PTR remains open).
- **Chain:** rotating Maxwell material → infinite Floquet/OAM boundary equations → prime conormal eigenfamily → independent defect confinement → RH.
- **Corpus basis:** `PhotonicTemporalMaxwellSlabRealization` proves the fixed-spatial-wavenumber `(D,B)` equations `D'=k B/μ`, `B'=-k E` with `D=εE` for constant slabs. `PhotonicFiniteDressedLaurentNoGo` identifies the full rotating material symbol `P(T)=d+a(T+T⁻¹)`. `PhotonicTimeCrystalDynamicChirality` gives sideband frequency `ω+nΔ`; `PhotonicPrimeCyclicSlabParabolicRealization` gives geometric conormal sidebands.

## Proven obstruction and falsifier

For a nonzero fixed spatial wavenumber `k` and nonzero drive frequency `Δ`, no nonzero geometric sequence `E_n=λ^n` solves the exact coefficient equations of `(εE)''+(k²/μ)E=0` for all Floquet grades. The Laurent material action makes `D_n=P(λ)E_n`, so the equation would force `(ω+nΔ)² P(λ)=k²/μ` for every `n`. Grades `0,1,2` have second difference `2Δ²P(λ)=0`, forcing `P(λ)=0` and then `k=0`. A counterexample with `kΔλ≠0` would falsify the theorem; Lean proves none exists in this coefficient model.

`PhotonicFixedKGeometricFloquetNoGo.lean` proves the all-grade no-go with a closed no-premise declaration and the sharp necessary exception `Δ=0 ∨ k=0`; direct Lean, targeted OLean and standard-axiom audit pass. It also proves the exact positive survivor: a geometric sequence solves the coefficient equation with grade-dependent spatial coefficient `K_n` **iff** `K_n=(ω+nΔ)²[d+a(λ+λ⁻¹)]` at every grade. `PhotonicFixedKGeometricFloquetSourceBridge.lean` replaces the abstract clock with the exact corpus Floquet frequency; direct Lean passes. Its targeted OLean was stopped after 50 seconds with no output under the no-long-build rule, so no OLean is claimed for that bridge.

This kills direct identification of the prime geometric conormal with an electric-field amplitude in the **fixed-`k` scalar temporal-Maxwell coefficient extension** of the existing two-slab model. The strongest positive survivor is the exact required dispersion profile above; in the nondegenerate PTR sector the boundary state must realize that profile through OAM/radial modes, or use a non-geometric vector-valued state or singular quotient. The coefficient equations are formalized, but their derivation as a distributional boundary trace of full rotating-cylinder Maxwell is not; therefore this is not a no-go for PTR itself.
