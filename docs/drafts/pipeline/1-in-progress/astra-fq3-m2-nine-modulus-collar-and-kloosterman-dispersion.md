# Nine-Modulus Collar Selectivity and Multi-Modulus Kloosterman Dispersion Transfer

**Stage:** `1-in-progress`
**Category:** `RH-core`
**Created:** 2026-10-27
**Updated:** 2026-10-27

## Statement
Deliver Milestone 2 of Focus Question 3 in two unconditional parts:
1. **Nine-Modulus Collar Selectivity & Polar-Paid Complement (`AIP`):**
   - Prove that at aperture `r = 69/50 = 1.38 ∈ (½ log 15, ½ log 16)`, `relevantShifts (69/50) = Finset.Icc 2 15`, whose prime-power support (`Λ(n) > 0`) is **literally `midpointPositiveModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`** (the exact nine-modulus collar where `0 < totalAntiDiagonalKernel n (log n / 2)`), while every prime power `n ∉ midpointPositiveModuli` is paid pointwise at its midpoint by the `s = 1` pole.
   - Prove the archimedean-free **Catalan `(8, 9)` (`2³ + 1 = 3²`) Cube-Square Gauge Separation** inside `midpointPositiveModuli` (`w(8) w(9) = 72^σ (log 2)(log 3) > 0` for all real scale twists `n^σ Λ(n)` vs `(λΛ)(8)(λΛ)(9) = -(log 2)(log 3) < 0`) and the exact **7-negative vs 2-positive sign partition** of `liouvilleTwistedVonMangoldt` across `{2,3,5,7,8,11,13}` vs `{4,9}`.
   - Prove monotonicity of `liouvilleWindowGroundEigenvalue r` for `0 < r₁ ≤ r₂`, certifying `liouvilleWindowGroundEigenvalue r < -3/10 < 0` and simultaneous smooth odd witnesses `F ∈ C²_c([-r, r])` with `Re W_ζ(F ⋆ F̃) > (1/25) ∫ F² > 0` and `Re W_{λΛ}(F ⋆ F̃) < -(3/10) ∫ F² < 0` across **every** `r ≥ 23/40` (including the exact nine-modulus collar `r = 69/50` and `r = 2 * log 2`), paired with the nine-modulus ratio-comb incidence floor.
2. **Multi-Modulus Kloosterman Dispersion & Guth–Maynard `17/30` Prime-Row Transfer (`ACT` / `BVI`):**
   - Prove exact multi-prime packet energy decomposition for `K_S(n) = ∑_{p ∈ S} a_p reciprocityZeroMeanKernel p n` over `range M`, collapsing every cross-prime pair `p₁ ≠ p₂` by CRT to a single terminal block of length `M % (p₁ p₂) < p₁ p₂` bounded by `(π⁴ / 5184) p₁³ p₂³`.
   - Prove cross-modulus CRT orthogonality of `omittedClassWeight q` against `bernoulliKernel p - primeKernelMean p` for distinct primes `q ≠ p` (`|Q · Λ_p(omittedClassCorrector q Q)| ≤ (p³ q + p³) / Q → 0`), proving that the multi-prime packet corrector `∑_{q ∈ S} omittedClassCorrector q Q` simultaneously cancels the omitted-residue-class bias at **every** prime `p ∈ S` while preserving `O((∑_{q ∈ S} q)/Q²)` block mass and coupling with the Guth–Maynard `17/30` short-window centred prime-row transfer.

## Idea
Identify `2 * (69/50) = 138/50 ∈ (log 15, log 16)` with the exact boundary between `{2,3,4,5,7,8,9,11,13}` and `16 = 2⁴`; exploit CRT coprimality `(p, q) = 1` on `omittedClassWeight q * (bernoulliKernel p - m_p)` and `reciprocityZeroMeanKernel`.

## Dependencies
- `ArithmeticIncidencePositivity/TotalAntiDiagonalClassification.lean`
- `ArithmeticIncidencePositivity/ContinuumCrossingRatioBridgeAndMultiAtomWindowLaw.lean`
- `SelectivePositivityAndThresholdLaws/TwoPrimeCatalanSeparationAndContinuumTowerObstruction.lean`
- `ArithmeticCompensationTheory/TheBalancedRegimeAndTheOmittedResidueClassLaw.lean`
- `BezoutValuationIncidence/ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram.lean`

## Proof
See `logs/astra-2710-research.log` Part VI (Milestone 2).

## Audit
- [x] Proof complete (no gaps)
- [x] Dependencies verified
- [x] Checked against kills (`docs/reports/rh-killed-routes.md`)
- [ ] Formalised in Lean 4

## Lean
- Targets:
  - `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/NineModulusCollarSelectivityAndPolarLedger.lean`
  - `formal/GaloisForLFunctions/ArithmeticCompensationTheory/MultiModulusKloostermanDispersionAndPrimeRowTransfer.lean`
- Umbrellas:
  - `formal/GaloisForLFunctions/ArithmeticIncidencePositivity.lean`
  - `formal/GaloisForLFunctions/ArithmeticCompensationTheory.lean`
