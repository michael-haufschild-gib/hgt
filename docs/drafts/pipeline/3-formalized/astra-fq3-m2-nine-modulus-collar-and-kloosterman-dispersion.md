# Nine-Modulus Collar Selectivity and Multi-Modulus Kloosterman Dispersion Transfer

- **ID:** astra-fq3-m2-2026-10-27
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2710/astra.md · Focus Question 3, Milestone 2
- **Statement:** (A) At the nine-modulus collar aperture `r = 2 * log 2 = (1/2) log 16`, `(relevantShifts (2 * log 2)).filter (0 < Λ ·) = totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`, `W_{λΛ} - W_ζ` cancels the square-class shifts `{4, 9}` identically and collapses to `-2` times the 7 odd-`Ω` collar atoms `{2, 3, 5, 7, 8, 11, 13}`, Catalan `(8, 9) = (2³, 3²)` separates all real scale twists `n^σ Λ(n)` from `λΛ` inside the collar, `liouvilleWindowGroundEigenvalue r < -3/10` with explicit smooth odd witnesses holds across every `r ≥ 23/40` (including `r = 2 * log 2`), and `totalDominatedModuli` prices the entire ratio-comb crossing charge in `fullZeroForm`. (B) On multi-prime reciprocity packets `K_S(n) = ∑_{p ∈ S} a_p W_K(p, n)`, unitary Parseval equates linear and Kloosterman mode energies `∑ α_p(h)² = ∑ C_m(p)²`, the Montgomery–Vaughan Farey large sieve yields two-sided `p⁴` quasi-isometry across `[N + 1, N + K]`, CRT collapses cross-prime Gram remainders, and `packetOmittedCorrector S Q = ∑_{q ∈ S} omittedClassCorrector q Q` simultaneously cancels `Q · Λ_p → 0` for every `p ∈ S` while preserving the Guth–Maynard `17/30 < α < 1` short-window centred prime-row bound.

## Goal
Extend smooth odd Weil selectivity and polar-paid incidence accounting from the two-prime window `[-23/40, 23/40]` (`{2, 3}`) across the complete nine-modulus collar `totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}` (`AIP`), and extend single-modulus Kloosterman Parseval and omitted-residue-class prime-row compensation (`BVI` / `ACT`) to arbitrary finite prime packets `S` coupled with Guth–Maynard `17/30` short-window transfer.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, nine-modulus collar + multi-prime CRT packet design
- [x] 1 → 2  fully-proven: complete paper proof in `logs/astra-2710-research.log` (Part VI, Milestone 2)
- [x] 2 → 3  formalized: Lean modules `NineModulusCollarSelectivityAndPolarLedger.lean` and `MultiModulusKloostermanDispersionAndPrimeRowTransfer.lean`, `lake --old env lean` exit 0, transitive axioms `[propext, Classical.choice, Quot.sound]`

## Proof
1. **Nine-Modulus Collar Window, Catalan `(8, 9)` Separation, and 7-Atom Collar Difference (`relevantShifts_two_mul_log_two_filter_vonMangoldt_pos`, `catalan_cubeSquare_collar_separation`, `re_weilFullFunctional_liouville_sub_vonMangoldt_collar`):** Because `exp(2 * (2 * log 2)) = 16`, `relevantShifts (2 * log 2) = Icc 2 15`, whose prime powers are `totalDominatedModuli`. On `[−2 log 2, 2 log 2]`, `W_ζ` and `W_{λΛ}` share identical archimedean, polar, and square-shift `{4, 9}` terms, so `Re W_{λΛ} - Re W_ζ` equals `-2` times the 7 odd-`Ω` shifts `{2, 3, 5, 7, 8, 11, 13}`. Antitonicity of `liouvilleWindowGroundEigenvalue` (`liouvilleWindowGroundEigenvalue_antitone_of_ge`) and support inclusion propagate `liouvilleWindowGroundEigenvalue r < -3/10` and smooth odd `C²_c([-r, r])` witnesses (`smooth_odd_selectivity_of_ge_twentyThreeFortieths`) to `r = 2 * log 2`, paired with `fullZeroForm_ge_nineModulusCollar_combLedger` (`nineModulusCollar_selectivity_package`).
2. **Dual Unitary Parseval and Two-Sided Montgomery–Vaughan Kloosterman Quasi-Isometry (`sum_Ico_reciprocityLinearCoeff_sq_eq_kloosterman`, `abs_sum_window_kloostermanPacket_sq_sub_le`, `sum_window_kloostermanPacket_sq_le_weil`, `sum_window_kloostermanPacket_sq_ge_fourthPower`):** Discrete Fourier orthogonality on `ℤ/pℤ` equates `∑_{h=1}^{p-1} α_p(h)² = (1/p) ∑_{n=1}^{p-1} W_K(p, n)² = ∑_{m=1}^{p-1} C_m(p)²`. Embedding `(h, p)` (`p ∈ S`, `1 ≤ h < p`, `p ≤ Q₀`) injectively into `fareySet Q₀` separates all frequencies by `1/(Q₀(Q₀ - 1))`, giving `(K - Q₀(Q₀ - 1)) E ≤ ∑_{n=N+1}^{N+K} K_S(n)² ≤ (K + Q₀² - 1) E`, together with exact CRT cross-prime terminal collapse (`sum_range_kloostermanPacket_sq_eq_diagonal_add_terminal`) and multi-modulus prime Gram dispersion (`abs_sum_primeGram_rankThree_remainder_le`).
3. **Simultaneous Multi-Prime Omitted-Class CRT Cancellation and `17/30` Transfer (`sum_range_omittedClassWeight_mul_bernoulliKernel_sub_mean_of_ne`, `tendsto_mul_kernelStatistic_centredPrimeBlock_add_packetCorrector`, `eventually_packetCorrectedPrimeBlock_seventeenThirtieths`):** For distinct primes `q ≠ p`, `omittedClassWeight q` and `𝔅(p, ·) - m_p` factor through CRT over `range (q * p)` with zero mean on the `p`-factor, yielding `|Q · Λ_p(omittedClassCorrector q Q)| ≤ (p³ q + p³)/(12 Q) → 0`. Summing over `q ∈ S` cancels `Q · Λ_p → 0` simultaneously at every `p ∈ S` while disturbing the inverse-square block mass by `O((∑_{q ∈ S} q)/Q²)`, preserving the Guth–Maynard `17/30 < α < 1` short-window bound.

## Lean
- Modules:
  - `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/NineModulusCollarSelectivityAndPolarLedger.lean`
  - `formal/GaloisForLFunctions/ArithmeticCompensationTheory/MultiModulusKloostermanDispersionAndPrimeRowTransfer.lean`
- Umbrellas:
  - `formal/GaloisForLFunctions/ArithmeticIncidencePositivity.lean`
  - `formal/GaloisForLFunctions/ArithmeticCompensationTheory.lean`

## Insight
Square-class shifts `{4, 9}` are gauge-blind across the nine-modulus collar while `{2, 3, 5, 7, 8, 11, 13}` carry the entire Liouville gauge charge (aligning directly with `RenormalizedBiarithmeticGeometry`'s square-class gauge-charge law); on the prime-row reciprocity side, distinct primes decouple cleanly both in Farey/CRT Kloosterman dispersion and in simultaneous omitted-residue-class compensation, isolating the single-modulus `p⁴` Kloosterman norm as the genuine dispersion core.

## Log
- 2026-10-27 — created in `1-in-progress`, proved, formalized in Lean 4 across `AIP` and `ACT`, audited (`lake --old env lean` exit 0), and promoted to `3-formalized`.
