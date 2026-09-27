# Cofinal prime deletion recovers the hidden translation measure — Lean certificate

- **Paper card:** `theta-all-sieve-seed-projector-translation-cone.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaAllSieveSeedProjector` (card), on top of the
  measure-gauge layer `GaloisForLFunctions.RHTower.ThetaTranslationMeasureGauge`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 16 audited theorems; no `sorry`.

A finite signed Borel measure `μ` is represented as `ν₁ - ν₂` with finite measures `ν₁, ν₂` (any
signed measure has such a representation, e.g. its Jordan decomposition); (1) is
`Integrable (e^{|s|/2}) νᵢ`; `g_μ = thetaSignedMeasureGauge ν₁ ν₂`; "μ positive" is `ν₂ ≤ ν₁`.

| Card item | Lean theorem |
|-|-|
| All-sieve theorem: every `b_{D_S g_μ}` CM ⇔ `μ ≥ 0` | `allSieve_completelyMonotone_iff` |
| (3) `b_{D_S k}(u) = 2π∑_{(n,S)=1} n²e^{-πn²u}`, `0 ≤ b_{D_S k} ≤ b_k ≤ u^{-3/2}/2` | `thetaNormalizedFlux_thetaPrimeDeletion_eq`, `thetaNormalizedFlux_thetaPrimeDeletion_nonneg`, `thetaNormalizedFlux_thetaPrimeDeletion_le` |
| (4) `b_{D_S g_μ}(t) = ∫ e^{5s/2} b_{D_S k}(e^{2s}t) dμ`; deletion commutes with mixing | `thetaNormalizedFlux_thetaPrimeDeletion_thetaMeasureGauge`, `thetaPrimeDeletion_thetaMeasureGauge`, `thetaNormalizedFlux_thetaMeasureGauge` |
| positive `μ` ⇒ every deleted flux CM | `completelyMonotoneOn_thetaPrimeDeletion_thetaMeasureGauge` (via `completelyMonotoneOn_integral`) |
| (2) cofinal limit to `b_seed,μ`; CM passes to the limit | `PrimeExhaustion.tendsto_flux_thetaMeasureGauge`, `completelyMonotoneOn_of_tendsto` |
| Bernstein–Widder + Laplace uniqueness + injective rate map ⇒ `μ ≥ 0` | `le_of_completelyMonotoneOn_thetaSeedFlux_sub` (`le_of_completelyMonotoneOn_laplace_sub`, `thetaSeedRateMeasure`, `le_of_thetaSeedRateMeasure_le`) |
| (5) `L_w g_μ = M_μ(w) L_w k` on `|Re w| ≤ 1/2` | `integral_cexp_mul_thetaSignedMeasureGauge`, `integral_cexp_mul_thetaMeasureGauge` |
| (6) all-sieve + mass + both charges ⇒ `μ = δ₀`, `g_μ = k` | `allSieve_two_charge_rigidity` (`thetaMeasureGauge_anchors`, `integral_cosh_half_eq`, `measure_eq_dirac_of_cosh_half`) |
| even `g_μ`: mass and `+1/2` charge suffice | `allSieve_even_rigidity` |
| (7) `μ_p`: positive probability, `g > 0`, all-sieve CM, mass and `+1/2` charge exact, `-1/2` charge larger, off-line zero of `M` and of `L_w g` at `1/4 + iπ/(2 log p)` | `thetaTwoShiftCounterMeasure_properties` (for every `p ≥ 2`) |
| (8) `C_{L,σ} < ∞` (explicitly `≤ 2cosh(L/2)/(cosh(L/2)-1)`) | `thetaGapConstant_le`, `bddAbove_thetaGapRatio` |
| (9) `|M_μ(w) - 1| ≤ C_{L,σ} δ` at all heights; `C δ < 1` ⇒ no zeros | `norm_measureMultiplier_sub_one_le`, `measureMultiplier_ne_zero_of_gap` |
| integer shifts have gap `log 2` | `log_two_le_abs_log_nat` |
| (10) `μ_ε` positive, even, all-sieve, exact mass, zero at `σ + iπ/ε` | `thetaGapFamily_properties`, `thetaGapFamily_multiplier_zero`, `thetaGapFamily_multiplier` |
| `M_{μ_ε}(1/2) = 1 + θ_ε(cosh(ε/2)-1) → 1`; `T_ε²(M(1/2)-1) → π²/16` | `thetaGapFamily_charge`, `thetaGapFamily_charge_limits` |
