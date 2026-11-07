# Review-0711 §2.1 Flow, near-line, continuation, orbit (A15–A24, A34)

- **ID:** r0711-flow-orbit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), per task
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.1 "Flow, near-line, continuation, orbit"
- **Statement:** complete and unconditional Lean solutions of A15–A24, A34, easiest first.

## Rules
No computations (A16 numerics and certified scans excluded). Corpus search first. `lake --old env lean` per module, foreground, one at a time. MMD cubic files belong to the A25–A33 session; CACT files to the A9–A14 session.

## Status
| # | Task | Status | Lean |
|---|---|---|---|
| A15 | RH ⇔ `Ψ` locally bounded | formalized | `ArithmeticInnerFunctionTheory/ThePotentialIsLocallyBoundedIffRH.lean`: `riemannHypothesis_iff_canonicalPotential_locallyBounded`, `riemannHypothesis_iff_anchorAngle_locallyBounded`, `riemannHypothesis_or_anchorAngle_unbounded` |
| A16 | numerical `r,m,q` | excluded: computation | — |
| A17 | Selberg `O(T)` depth density, inner-field form | formalized | `ArithmeticInnerFunctionTheory/TheInnerFieldIsBoundedAtInfinity.lean`: `exists_sum_depth_le_linear` (uniform in `|t|≤T`), `exists_innerField_le`, `eventually_innerField_le` (`I ≤ 27/5`), `eventually_poisson_log_le` (Abel log-mean `≤ 11/2`) |
| A18 | twisted second moments past `21/50` | open: re-tune of the far pair-error envelope (see below) | |
| A19 | heat horizon toward method floor | assessed (see below) | |
| A20 | Jensen rung toward saddle scale | open: needs a new contraction mechanism (see below) | |
| A21 | census items, log two-point Chowla, runs past five | runs past five blocked by the census input; Chowla open (see below) | |
| A22 | VK `ζ(1+it)` bound into first-return bracket | formalized | `TailArithmeticOfThePrimeOrbit/TheVinogradovKorobovBoundOnTheOneLine.lean`: `norm_riemannZeta_le_vkCube`, `exists_norm_riemannZeta_le_two_thirds` (`≪ (log τ log log τ)^{2/3}` on `1≤σ≤2`); `TheFirstReturnPastTheVinogradovScale.lean`: `eventually_log_ge_of_isWeakReturn`, `eventually_exp_le_firstReturn` (`R ≥ exp(c(log N)^{3/2}/log log N)` at `η log log N ≤ D`) |
| A23 | resonator mean of `|ζ(s+iτ)|²` on Bohr sets | formalized | `TailArithmeticOfThePrimeOrbit/TheResonatorMeanOfZeta.lean`: `tendsto_resonatorMean_zeta` (`(1/T)∫_T^{2T}|Rζ(σ+it)|² → Σ_k|c_k|²`, `½<σ<1`), `tsum_resonatorCoeff_eq_mul`, `tendsto_resonatorMean_zeta_smooth` (smooth head: limit = head part × `Σ_{rough u} u^{−2σ}`) |
| A24 | scans of `S_S`, brackets `S*(a,b)` | excluded: certified numerics of the `S`-smooth spectra (mpmath scans) | — |
| A34 | integrate [S] modules | done except MMD cubic (owned by the A25–A33 session) | checked: `PrimeTorusTheory/TheMixingTimeFromBelow`, `PrimeTorusTheory/TheQuestionsOfTheField`, `ArithmeticAuxiliaryDynamics/TheAtomsOfTheExtremalMeasure` (lint fixed); TAPO questions already built |

## A15 — paper proof
Fix a precontact base `b`. `canonicalPotential_sub_eq`: `Ψ(y)−Ψ(x) = L(y)−L(x)+∫_x^y sinh 2L`, `L = artanh r` continuous on the precontact set.
- (⇒) Under RH the precontact set is `(0,∞)`; on `[b,c]` both `L` and `sinh 2L` are continuous, so `Ψ` is bounded.
- (⇐) Off RH let `a*` be the contact. If `|Ψ| ≤ M` on `[b,a*)`, then `|L| ≤ |L(b)| + 2M` there: if `L(y) > θ := max(L(b),0)+2M`, take the last `x ≤ y` with `L(x) ≤ max(L(b),0)`; on `(x,y]` `L > 0`, so `sinh 2L > 0` and `L(y)−L(x) ≤ Ψ(y)−Ψ(x) ≤ 2M`, contradiction; symmetric below. Then `m = cosh 2L` is bounded, `(log K)′ = 2m` keeps `K(i,i)` bounded below `a*`, contradicting `K(i,i) → ∞` at contact.

## A17 — paper proof
`eventually_offLineMoment_le_selberg_upper`: `Σ_{0≤γ≤V,β>½} m(β−½) ≤ (67/1000)V`. Conjugation preserves zeros and multiplicity (`analyticOrderAt_riemannZeta_conj` via `iteratedDeriv_riemannZeta_conj`), so a window `|γ−t| ≤ T`, `|t| ≤ T` has depth `≤ 2·offLineMoment(2T) = O(T)`. `innerField_le_of_depthDensity` gives `I ≤ 40ε` when every window of size `≥ x` has depth `≤ εT`; with `ε = 135/1000` for `x ≥ 134|t|`, `I ≤ 27/5`. `innerField = Poisson log-mean + (log‖w‖ − log‖ζ̃(w)‖)` and the correction tends to `0`.

## A22 — paper proof
Vinogradov's dyadic estimate (`norm_sum_logPhase_le_dyadic`) gives prefix sums `≤ 12e^{20}Y^{1−δ/4} + 200Y^{1/2}`, `δ/4 ≥ ℓ²/(A L²(log L)²)`, `A = 746496`, `ℓ = log Y`, on `e^{L^{2/3}} ≤ Y ≤ τ^{1/22}`. At `σ ≥ 1` the block is `≤ 12e^{20}exp(−ℓ³/(AL²l²)) + 200Y^{−1/2}`; the 24th derivative test gives `≤ 2560 Y^{−1/(3·2^{24})}` for `Y^{22} > τ`. With `K³ = AL²l²` and blocks starting at `N₁ = ⌈e^K⌉`: `ℓ³/(AL²l²) ≥ ℓ/K`, so the middle blocks sum to `≤ 12e^{19}(1 + K/log 2)`; the other pieces are `O(1)`; the initial segment is `≤ e^{1/50}(1 + log N₁)`. Hence `|ζ(σ+iτ)| ≪ (log τ)^{2/3}(log log τ)^{2/3}` on `1 ≤ σ ≤ 2`. Through `log|ζ(s_N(t))| ≥ log log N − A_t(N) − K`, a weak return (`A_t(N) ≤ C`) forces `(log t)(log log t) ≫ (log N)^{3/2}`, so `log t ≫ (log N)^{3/2}/log log N`.

## A23 — paper proof
`R(t)=Σ_{m∈A} r_m m^{it}`, `D_N=Σ_{n≤N}n^{−σ−it}`. (i) `R·D̄_N` has coefficients `c^N_k=Σ_{m∈A,m|k,k/m≤N} r_m(k/m)^{−σ}`; the dyadic mean value theorem gives `M_T(RD_N) → Σ|c^N_k|²`. (ii) `||a+b|²−|a|²| ≤ δ|a|²+(1+δ⁻¹)|b|²` and `|R| ≤ Σ|r_m|` give `|M_T(Rζ)−M_T(RD_N)| ≤ δM_T(RD_N)+(1+δ⁻¹)(Σ|r|)²M_T(ζ−D_N)`; Carlson: `M_T(ζ−D_N) → Σ_{n>N}n^{−2σ} → 0`. (iii) `c^N_k → c_k`, dominated by `g_k=Σ_{m|k}|r_m|(k/m)^{−σ}` with `g_k² ≤ |A|Σ_m|r_m|²[m|k](k/m)^{−2σ}` summable. Decoupling: for smooth `m`, `m|su ⇔ m|s`, so `c_{su}=u^{−σ}c_s`; `(s,u)↦su` is a bijection onto `k≥1` (`smoothPart·roughPart = k`).

## A18 — state
The far pair-error envelope (`ZetaGateFarPairError`) has `x = u^100`, taper `η = u^95`, dual split `Y₀ = u^102`; its own docstring names the only binding constraint, the per-step oscillation saving `η^{−2}·hk·Y₀ = u^{2m+102−190}`, so `m < 44`. The `N²` pairs are summed without cancellation against a per-pair error `≍ u^{−98}`, so this architecture stops at `m < 49`, i.e. `θ < 0.49·(49/50)`. A taper `u^99` with `Y₀ = u^101` gives `m ≤ 48`. `θ → ½` (BCHB) needs joint treatment of the off-diagonal over pairs; Conrey's `4/7` needs Kloosterman-sum input.

## A19 — assessment
Profile margin: repulsion holds for `c` with `(c−w)² > 4cμ(½+w)` on `[0,½]`. For a linear piece `μ(½+w) ≤ a − bw` the threshold is `a/(b(1−b))` (here `a = 33/200`, `b = 97/200`: `6600/9991`). Convexity and the functional equation give `μ(½+w) ≥ μ(½) − w/2`, hence `b ≤ ½` and the method floor is `4μ(½) = 33/50` at the corpus exponent. Reaching it needs a source point `(σ₁, μ(σ₁) ≤ 33/200 − (σ₁−½)/2)`, i.e. an exponent pair with `l − k ≥ σ₁ > ½` and `N`-explicit block bounds (the corpus's critical-line prefix bound `P` is not explicit in `N`). Gain `6·10⁻⁴` inside `[½, 6600/9991]/log X`, a band that carries no zero information (ZCG README). Below `33/50` needs a smaller `μ(½)` (Huxley `32/205`, Bourgain `13/84`).

## A20 — assessment
`nonrealRootCount_diffOp_X_pow_eq_zero` needs `|t(w)e^{cw²}| ≤ M` on `|w| = r` and `((1+M)d/r)² ≤ 2c`. Any Gaussian taken from LP factors of zeros above `Y` costs the quartic error `r⁴Σ_{γ>Y}γ^{−4} ≍ r⁴ log Y/Y³`, and the factors below `Y` must be verified, so `Y ≤ T` and `d ≲ Y^{1/4}(log Y)^{1/4}`: the corpus rung `d⁴ ≲ T log T` is optimal for this method. The non-LP part of an off-line quadruple is only `(Im ρ^{−2})²D⁴ ≈ 4δ²γ^{−6}D⁴` (`(1−aD²)(1−āD²) = (1−Re a·D²)² + (Im a)²D⁴`), which is `(δ/γ)²` smaller than what the circle pays. Exploiting it needs strip contraction by products of LP steps, which fails step by step (`heatStep_keeps_triple_edge_root`). Open mechanism.

## A21 — state
Runs: `runStarts_card_bound` with the reflection census `2n + S ≤ N + 2G` gives `runs_L ≥ G + ((L−1)/2)(S − N) − (L−1)`. With `G, S ≈ HD·N` this is positive iff `HD > (L−1)/(L+1)`; `L = 6` needs `HD > 5/7`, the corpus has `HD(1) ≥ 0.6725`. Runs past five need a new census input, not a rearrangement. Logarithmic two-point Chowla (Tao) needs Matomäki–Radziwiłł–Tao Fourier uniformity of `λ` in short intervals plus the entropy decrement argument; none of it is in the corpus.

## Log
- 2026-11-07 — created; A17 found reducible to `eventually_offLineMoment_le_montgomeryTaylor` (`Σ m(β−½) ≤ 0.066 V`) plus `bounded_innerField_iff_depthDensity`.
