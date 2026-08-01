# Route J closed: unrenormalized Julia coherent-energy no-go

Route J in `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is retired. Exact unconditional result: for `L_m = 6 log m`, `25 ≤ m`, and `exp 20 ≤ (m^4 : ℝ)`, every Julia scale `x` satisfies

`log m / 20 ≤ ccmFirstClockJuliaBadCoherentEnergy x L_m (ccmFirstClockAdmittedPrimePacket L_m)`.

Reason: every prime in `(2m^4,5m^4]` is a one-mode admitted prime with phase in `(4π/3,3π/2]`, hence bad square at least `(log p)^2/(4p)`; pointwise-positive unit-diagonal Julia kernel retains diagonal; Chebyshev block mass yields `log m/20`. Uniform-in-scale unboundedness follows. For fixed `L`, zero scale tends to `(sum bad)^2`, so de-attenuation restores rank-one coherence. Post hoc diagonal subtraction fails on one-node unit packet (`1 ≤ 0`).

Lean:
- `formal/GaloisForLFunctions/HTGeometry/NonnegativeKernelDiagonalCapacity.lean`
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaCoherentEnergyDiagonalFloor.lean`
- Capstones: `ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower`, `ccmFirstClockJuliaFullBadCoherentEnergy_unbounded_uniformly_in_scale`, `tendsto_ccmFirstClockJuliaFullBadCoherentEnergy_zero`.

Docs:
- Stage 3: `docs/drafts/pipeline/3-formalized/route-j-julia-coherent-energy-diagonal-floor.md`
- Failed route: `docs/drafts/pipeline/5-failed/route-j-julia-unrenormalized-coherent-energy-budget.md`

Audits passed: direct leaf Lean, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), `formal_tools.py index`, `formal_tools.py lint --check-generated`, final `lake build GaloisForLFunctions.RHTower.CCMFirstClockJuliaCoherentEnergyDiagonalFloor`. Existing replay/linter warnings are outside new modules. No computation used.

Only viable successor is a new source-defined principal-relative Julia current with counterterm inserted before good/bad positive projection and a new relative orientation theorem; it is not Route J.