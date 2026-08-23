# Hawking–Suzuki wall KMS commutator endpoint (2026-08-23)

New formal module:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSuzukiWallKMSCommutatorEndpoint.lean`
- wired from `formal/GaloisForLFunctions/RHTower.lean`.

Core construction:
1. Exact Hartle–Hawking Araki–Woods coefficients
   `a=sqrt(1/(1-q))`, `b=sqrt(q/(1-q))`,
   `q=thetaCuspHawkingKMSBoltzmannRatio kappa omega`.
2. Proves `a^2-b^2=1`, `IsTwoModeBosonicCCR`, signed-Hermitian preservation, and explicit signed-adjoint inverse. Thus full finite/nonperturbative SU(1,1) scattering, not a rate ansatz.
3. Defines passive reflected quarter-turn readout
   `(F(t) ± I F(-t))/2`; its population difference scales quadratically and reverses sign under complex conjugation.
4. Feeds actual `suzukiCriticalWallField` through down/up Araki–Woods branches. Because physical up branch conjugates phase, its readout current is `-q` times down current.
5. Oriented KMS sum (commutator current) cancels Bose factors:
   `downCurrent + upCurrent = im (wallField t)^2`.
   Complex form equals `suzukiCriticalWallReflectedCurrentKernel t t p e`.
6. Prime-power specialization exactly recovers
   `criticalMellinAtomWeight n * sin(2*pi*log n*xi)`.
7. Center-blindness no-go: reconstructed current vanishes at xi=0 while negative-light reserve is strictly positive, so exact KMS/scattering plus phase readout cannot itself prove global Ward positivity/RH.

Interpretation:
- Hawking radiation is structural: SU(1,1) Araki–Woods thermal dilation creates absorption/emission branches; passive reflected SU(2)-type quarter-turn readout exposes phase.
- Thermality transports Suzuki phase faithfully and temperature-independently through the commutator, but does not select its sign.
- Remaining RH-bearing producer stays full prime–Gamma/Robin/holonomy Ward assembly or another source-specific mechanism controlling signed current against reserve.
- Do not misidentify `ccmActualHeadMatchedSymmetricCellResidual` as positive output population: it is a signed cosine integral.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingSuzukiWallKMSCommutatorEndpoint.lean` passes.
- Axiom audit of five main theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` reports only unrelated pre-existing umbrella reachability errors for `RHTower.CesaroSignRecurrence` and `HTGeometry.ABHN.CyclicGaloisRestrictionOrientation`.
- Direct umbrella Lean check is blocked by another pre-existing missing olean for `AnharmonicChebyshevCubicDescentCriterion`.

Related prior memory: `mem:research/hawking_full_mirror_bogoliubov_standard_clock_endpoint_2026_08_23`.
