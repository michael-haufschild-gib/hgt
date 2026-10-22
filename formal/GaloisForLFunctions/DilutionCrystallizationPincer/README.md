# Dilution–Crystallization–Incommensurability (DCI) Pincer (`GaloisForLFunctions.DilutionCrystallizationPincer`)

This directory formalizes **Mechanism 1: The Dilution–Crystallization–Incommensurability (DCI)
Pincer Across Wall 3 and Wall 1.3** from [`docs/reports/review-2110/argon.md`](../../../../docs/reports/review-2110/argon.md).

## Architecture and Module Ledger

1. **[`DilutedPatternAndCrystalVisibilityLaw.lean`](./DilutedPatternAndCrystalVisibilityLaw.lean)**
   - Defines `dilutedPatternConfig`, superposing an arbitrary `P`-pair periodic off-line pattern of
     period `2π/ℓ` (`P` reflected off-line pairs per period at offsets `c_r` and depths `d_r ∈ (0, ½]`)
     onto a dense doubled on-line lattice `{½ + 2πik/L}` of background density `L/2π`.
   - Proves the exact lag formula `W_dilutedPatternConfig` and the Toeplitz equivalence
     `dilutedPattern_weil_nonneg_iff_toeplitz` for apertures `0 < a ≤ L/2`.
   - Proves the mode bound `norm_patternSymbol_le_of_diluted_hiding`: hiding at `a ≤ L/2` forces
     `ℓ ‖D(m)‖ ≤ 2Pℓ + 2L` for `1 ≤ m < ⌈2a/ℓ⌉₊`.
   - Proves `patternSymbol_crystal_mul_period` and `norm_patternSymbol_crystal_mul_period`: for any
     `P`-pair uniform crystal (`d_r = δ` and `P(θ_r − θ_{r'}) ∈ ℤ`), destructive interference kills
     `1 ≤ m < P`, but at every harmonic `m = kP` (`k ≥ 1`) the `P` pairs align with 100%
     constructive interference (`‖D(kP)‖ = 2P cosh(δ k P ℓ)`).
   - Proves `diluted_crystal_visible_at_harmonic` and `exists_diluted_pattern_visibility_constants`:
     both diluted crystals and arbitrary diluted periodic patterns become strictly visible at the
     logarithmic aperture `a ≍ (1/2 d_max) log(L/ℓ)`.

2. **[`ArchimedeanDominationOfDilutedVisibility.lean`](./ArchimedeanDominationOfDilutedVisibility.lean)**
   - Proves `integral_norm_sq_pos_of_re_W_neg` and `exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`.
   - Proves the **Sub-Barrier DCI Comparison Theorems**
     `archimedean_dominates_diluted_lattice_visibility` and
     `archimedean_dominates_diluted_crystal_visibility`: at any aperture `0 < a ≤ L/2` past the
     logarithmic diluted threshold, there exist a `C²` test `f` supported in `[-a, a]` (polar-free
     in the lattice case) and an explicit height horizon `Ξ > 0` such that `f` makes the diluted
     off-line configuration strictly negative (`Re W_{dil}(f, f) < 0`) while `ζ`'s localized Weil
     form is strictly positive and `L²`-coercive (`Re W_ζ(S_ξ f, S_ξ f) ≥ ∫ ‖f‖² > 0`) at all
     heights `|ξ| ≥ Ξ`.

3. **[`PrimeTorusCrystallineResonanceObstruction.lean`](./PrimeTorusCrystallineResonanceObstruction.lean)**
   - Proves `patternSymbol_crystal_nat_eq_zero_of_not_dvd`,
     `patternSymbol_crystal_int_eq_zero_of_not_dvd`, and `patternSymbol_crystal_dichotomy`: for a
     `P`-pair uniform crystal, **every** integer mode `m ∈ ℤ` not divisible by `P` vanishes
     identically (`D(m) = 0`), while every multiple `m = kP` has norm `2P cosh(δ k P ℓ)`.
   - Proves `offLineLattice_comb_teeth_and_gap_dichotomy` and
     `crystal_gap_prime_torus_incompatibility`: at any lag `v > 2w` lying in a crystal gap
     `|v − nL| > 2w`, the difference test `g_v = twoBump (modScaledBump w 0) v (-1)` sees zero
     off-diagonal crystal response (`W_{crystal}(g_v, g_v) = 4L ∫ ‖κ_w‖² > 0`), whereas on `ζ`,
     Kronecker phase alignment on the prime torus (`loggedPrimes_linearIndependent`) produces a
     height `ξ ∈ ℝ` where `Re Π_{g_v}(ξ) > B` and forces either `Re W_ζ(S_ξ g_v, S_ξ g_v) < 0` or
     exponential height escape.

4. **[`MasterDCIPincerTheorem.lean`](./MasterDCIPincerTheorem.lean)**
   - Proves `exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor` and
     `polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor`: any sub-exponential
     aperture-dependent bound `W(A) = o(e^{εA})` on the depth-floor factor already forces
     `polarGroundEnergyRate = zetaZeroWidth`.
   - Proves `exists_superexponential_depthFloor_of_lt` and
     `exp_depthMass_lt_height_of_window_depthMass_gt`: any unit window `[T-1, T+1]` (`|T| ≥ 4`)
     with squared off-line depth mass `> W` must lie at height
     `180 |T| > exp(W / (40 · zetaZeroWidth²))`.
   - Packages the five-part unconditional **`dci_pincer_master_theorem`**.
