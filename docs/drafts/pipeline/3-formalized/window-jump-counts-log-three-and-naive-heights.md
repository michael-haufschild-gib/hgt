# Window jump counts through `log 3` and naive heights on `ℤ[ℚ_{>0}^×]`

- **ID:** WJCH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.5.1 (Q1, steps 1–3) and §2.6.1 (B20, B28, B32)
- **Statement:** Unconditional `{∞, 2}` jump-count and `T₂`-graph identities through `2a ≤ log 3`, variable-hub and `T₂`-stick sum-of-squares completions, exact folded-Markov corner ceilings (`8(√2 − 1)` at `log 2` and `3(√3 − 1)` at `log 3`), unconditional window coercivity regimes, and genuine `ℕ`-valued count heights on `ℤ[ℚ_{>0}^×]` and `ℤ[p^ℤ · q^ℤ]` deciding `RiemannHypothesis`.

## Gates
- [x] 0 → 1  in-progress: mathematical statements fixed and mapped to existing corpus infrastructure
- [x] 1 → 2  fully-proven: dependency-closed paper proofs
- [x] 2 → 3  formalized: Lean 4 modules audited cleanly with `lake --old env lean`, `#print axioms` verified (`[propext, Classical.choice, Quot.sound]`), wired into umbrellas

## Lean Formalization

1. **`GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions`**
   (`formal/GaloisForLFunctions/LatticeSectionTheory/WindowJumpCounts/SinglePrimeWindowJumpGraphAndObstructions.lean`)
   - `autocorr_eq_zero_of_two_mul_le`: boundary autocorrelation vanishing `autocorr f x = 0` for `tsupport f ⊆ [−a, a]` and `2a ≤ x` (overlap `{−a}` has Lebesgue measure zero).
   - `two_mul_poleCross_eq_poleSquares`: `2 poleCross N f = 2 evenPoleMoment(f)² − 2 oddPoleMoment(f)²`.
   - `weilPair_eq_jumpCount_add_poleSquares_of_le_log_two`: closed prime-free (`2a ≤ log 2`) decomposition into diagonal, archimedean Lévy `jumpCount`, and signed pole squares.
   - `weilPair_eq_jumpCount_add_primeTwoGraph_of_le_log_three` and `primitiveH1_eq_jumpCount_add_primeTwoGraph_of_le_log_three`: single-prime (`2a ≤ log 3`) decomposition into archimedean `jumpCount`, the `T₂`-graph jump `(log 2 / √2) primeTwoGraphJump f` (`∫ (f(u) − f(u + log 2))² du`), combined diagonal `(Ω(0) − √2 log 2) ∫ f²`, and signed pole squares.
   - `neg_two_mul_autocorr_gauge_eq` and `path_routing_jump_identity`: gauge-strip `T₂`-graph jump decomposition `primeTwoGaugeStripJump M g` and two-hop harmonic chord completion of squares.
   - `weilPair_ge_of_le_threeTenths` (`primitiveH1_ge_of_le_threeTenths`), `weilPair_ge_of_odd_le_oneHundredEightyOneFiveHundredths`, `weilPair_ge_of_evenPoleMoment_zero_past_primeTwo`: unconditional window coercivity on `[−3/10, 3/10]` (all parities), on `[−181/500, 181/500]` (odd, past `p = 2`), and on `(−a, a)` with `2a ≤ log 2 + 1/50` (`evenPoleMoment f = 0`, crossing `p = 2`).
   - `fullSourcePair_thetaTranslate_eq_zero`: every individual admissible `Θ`-translate (`|b| < ½ log 2`) lies in the radical of the pole-completed CHMD bilinear form `fullSourcePair`.

2. **`GaloisForLFunctions.ArithmeticCriticalityTheory.WindowJumpCounts.VariableHubSchurAndFoldedMarkovObstruction`**
   (`formal/GaloisForLFunctions/ArithmeticCriticalityTheory/WindowJumpCounts/VariableHubSchurAndFoldedMarkovObstruction.lean`)
   - `variableHub_pointwise_sq_eq`, `variableHub_pointwise_ge_schur`, `integral_variableHub_sq_eq`, `harmonicHub_jump_ge_hubMean_sq`: variable-hub completion of squares for signed potentials `p(x) u(x)²` and continuous harmonic-mean Cauchy–Schwarz hub reduction `w(x) = m_Z² / ∫_Z (M/K)`.
   - `twoVertexStick_sq_eq`, `twoVertexStick_ge_schur`, `stickDet_eq`: exact 3-square elimination of a `T₂`-coupled pair `(u₁, u₂)` with Schur numerator `(p₁ p₂ + g₁₂(p₁ + p₂))(w₁ + w₂) + (p₁ + p₂) w₁ w₂`.
   - `archLevyDensity_lt_two_mul_cosh_iff_plastic`: exact plastic-number threshold `ω(a) < 2 cosh(a/2) ↔ e^{−2a} + e^{−3a} < 1`.
   - `le_cornerCeiling_of_foldedCalibratedConductance_nonneg`, `cornerCeiling_half_log_two`, `cornerCeiling_half_log_three`, `cornerCeiling_half_log_two_lt_four`, `cornerCeiling_half_log_three_lt_four`, `exists_folded_weilJumpDensity_neg_of_plastic`, `exists_folded_weilJumpDensity_neg_half_log_two`, `exists_folded_weilJumpDensity_neg_half_log_three`: corner ceiling `c₀ ≤ 2 ω(a) / cosh(a/2)` (`= 8(√2 − 1) < 4` at `2a = log 2`, `= 3(√3 − 1) < 4` at `2a = log 3`) and strict interior negativity of the folded Weil jump conductance on `(0, ½ log 2)²` and `(0, ½ log 3)²`.
   - `phiDoob_halfLine_coshMass_split`: half-line Doob pole-mass conservation `∫_{(0, a]} Φ cosh(x/2) + ∫_{(a, ∞)} Φ cosh(x/2) = 1/4`.

3. **`GaloisForLFunctions.ArithmeticEffectivityTheory.WindowNaiveHeights.MultiplicativeScaleHeightsAndWindowCounts`**
   (`formal/GaloisForLFunctions/ArithmeticEffectivityTheory/WindowNaiveHeights/MultiplicativeScaleHeightsAndWindowCounts.lean`)
   - `PosRatScale`, `posRatLog`, `posRatLog_injective`, `denseRange_posRatLog`, `twoPrimeLog`, `denseRange_twoPrimeLog`, `zetaPosRatScalingDatum`, `zetaTwoPrimeScalingDatum`, `posRatRosatiForm`, `twoPrimeRosatiForm`, `intRosatiForm_scaleInvolution`: multiplicative group `ℚ_{>0}^×`, rational Hecke group ring `ℤ[ℚ_{>0}^×]`, and rank-two subrings `ℤ[p^ℤ · q^ℤ]`.
   - `eq_natFloor_add_sq_of_nonneg`, `abs_natFloor_sub_le_one_of_nonneg`, `exists_natCount_iff_nonneg`, `windowNatCount_decomp_of_le_threeTenths`, `windowNatCount_decomp_of_odd_le_oneHundredEightyOneFiveHundredths`, `windowNatCount_decomp_of_evenPoleMoment_zero_past_primeTwo`, `posRatNatCount_decomp_of_support_le_threeTenths`: genuine `ℕ`-valued floor counts `⌊·⌋₊` + manifest square remainders with distance `≤ 1` and zero sign-clamping across all proved nonnegative window regimes.
   - `continuous_zetaOrbitCorr`, `zetaOrbitHodgeIndex_pullback_iff_of_denseRange`: per-cycle dense subgroup transfer `(pullbackScalingDatum zetaScalingDatum φ).OrbitHodgeIndex x ↔ zetaScalingDatum.OrbitHodgeIndex x` via orbit-correlation continuity and `zeta_orientation_iff`.
   - `riemannHypothesis_iff_forall_posRatNatCount`, `riemannHypothesis_iff_forall_posRatNaiveHeight`, `riemannHypothesis_iff_singleOrbit_posRatNatCount`, `exists_cycle_riemannHypothesis_iff_posRatNatCount`, `riemannHypothesis_iff_singleOrbit_twoPrimeNatCount`, `riemannHypothesis_iff_forall_windowCountPlusNonneg`: global all-cycle, single-generic-orbit (over `ℤ[ℚ_{>0}^×]` and over `ℤ[p^ℤ · q^ℤ]`), and all-window count-plus-nonnegative-remainder equivalences with `RiemannHypothesis`.
   - `goldenDatum_no_natCount`, `complexFake_no_natCount`: selectivity obstructions refuting `ℕ`-valued count heights on off-line and complex-quartet fakes.

## No-go closure (for obstructed local Markov / gauge routes on `A ≤ log 3`)
- **Exact killing theorem/mechanism:** `le_cornerCeiling_of_foldedCalibratedConductance_nonneg` + `cornerCeiling_half_log_two_lt_four` / `cornerCeiling_half_log_three_lt_four` + `fullSourcePair_thetaTranslate_eq_zero`: full pole calibration (`c₀ = 4`) exceeds the corner ceiling `2 ω(a) / cosh(a/2)` at every `a` past the plastic threshold `e^{−2a} + e^{−3a} = 1` (`8(√2 − 1) < 4` at `2a = log 2`, `3(√3 − 1) < 4` at `2a = log 3`), while individual `Θ`-translates lie in the radical of `fullSourcePair`.
- **Strongest positive survivor:** Variable-hub Schur completion (`variableHub_pointwise_sq_eq`, `harmonicHub_jump_ge_hubMean_sq`), coupled 2-vertex `T₂`-stick elimination (`twoVertexStick_sq_eq`), all-parity coercivity through `a ≤ 3/10` (`weilPair_ge_of_le_threeTenths`), odd coercivity past `p = 2` (`a ≤ 181/500`, `weilPair_ge_of_odd_le_oneHundredEightyOneFiveHundredths`), and `cosh`-orthogonal smooth coercivity across `[−½ log 2, ½ log 2]` and past `p = 2` (`2a ≤ log 2 + 1/50`, `weilPair_ge_of_evenPoleMoment_zero_past_primeTwo`).
- **New insight:** Past `a = log ρ`, negative edge potentials and folded jump conductances are absorbed only by non-local hub and `T₂`-mirror squares; on `ℤ[ℚ_{>0}^×]` (and `ℤ[p^ℤ · q^ℤ]`), bounded-error `ℕ`-count heights transfer cycle-by-cycle to full `ℝ`-shifts by continuity and orientation.
- **Status:** Fully proved and formalized in Lean 4 across the three modules above (`[propext, Classical.choice, Quot.sound]`).
