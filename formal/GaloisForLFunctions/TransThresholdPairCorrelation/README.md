# TransThresholdPairCorrelation (TTPC)

Namespace `GaloisForLFunctions.TransThresholdPairCorrelation`; umbrella `TransThresholdPairCorrelation.lean`.
A zero-proportion programme, not an RH route. Analytic inputs come from the `Zeta23` lake package
(`Zeta23.paperInputs_zeta`: explicit formula, Riemann–von Mangoldt, Chebyshev, Montgomery–Vaughan, Γ-facts;
`gammaFacts`), which is a proved object, and from `RHTower` Gram infrastructure.

## 1. Motivation

The explicit-formula Gram matrix of a band-limited test at height `T` certifies a simple-zero proportion
`2 − κ`, `κ` = normalized Frobenius norm. At bandwidth `λ ≤ 1` (prime cutoff `X = (T/2π)^λ ≤ T`) every
off-diagonal prime pair is killed by Montgomery–Vaughan and `κ = 1/λ + λ/3 ≥ 4/3`: the method stops at `2/3`.
Beyond `λ = 1` prime frequencies `log n` can be closer than the window resolves. TTPC asks which signed
information about prime pairs beyond `X = T` lowers `κ`, isolates exactly where it is needed, and proves
everything else unconditionally.

## 2. Objects

| Object | Meaning | Lean |
|---|---|---|
| Setting at `λ = 4/3` | `l = log(T/2π)`, `L = λl`, `X = e^L`, grid `τ_k = T + kh`, `h = 2π/L`, test `Φ` with `∫Φ²e^{ixy} = 2πg(y)` | `params43`, `Setting`, `LocalFun`, `LocalHypsCoreW` (RHTower/Zeta23) |
| Density | `ν_X = μ + Π_X + P_X`, `P_X(τ) = −π⁻¹Σa_n cos(τ log n)`, `a_n = Λ(n)/√n` | `Zeta23.nuX`, `Zeta23.PX`, `acoef` |
| Prime surplus | off-diagonal pairs + sum frequencies + end form | `primeSurplus`, `ppOffDiag`, `ppSumFreq`, `endForm` |
| Half-line kernel parts | `A⁻ = AminusCos + AminusSin`; Fourier-replaced cosine sum | `AminusCos`, `AminusSin`, `ppOffDiagFourier` |
| Prime Dirichlet polynomials | `C_g = Σa_n g(log n)cos(τ log n)`, `S_g` | `primeDirichletCos`, `primeDirichletSin` |
| Form-factor Frobenius norm | `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)` | `frobeniusFormFactor`, `transThresholdIntegral`, `generalPrimeSurplusRatio` |
| Affine models | `F = β + γ(α−1)` on `α > 1` | `affineTransModel` |
| Narrow strip | `λ = 1+δ`, Cesàro energy `E(δ)`; gain under `β ≤ Bδ²/(1+δ)²` | `narrowStripCesaroEnergy`, `narrowStripGain` |
| Window profile | smooth `u: ℝ → [0,1]`, collar `ε₁ ≤ 1/8`; `u_T`, `W_T = u_T²`, `Ω_T = u_T⁴` | `WindowProfile`, `profileU`, `profileW`, `profileΩ` |
| Smooth form | `𝓜_Ω[u,v] = ∬Ω(τ)Φ(τ−τ')²u(τ)v(τ')` | `smoothForm`, `smoothPair`, `cosTransform` |
| Coalescent sum | `π⁻¹Σ a_na_m g(log m)Ω̂(log n − log m)` over `0 < |log(n/m)| ≤ θ₀` | `coalSum`, `primeCoalSum`, `oddEvenShiftPrimeCoalSum` |
| Coalescent surplus | `coalSum(Ω_T, g, X, T^{−1+η})/(aL)²` | `coalescentSurplus`, `primeCoalescentSurplus`, `oddEvenShiftPrimeCoalescentSurplus` |
| Budget predicates | certificate and surplus `≤ (β+ε)N(T,2T)` | `CoalescentSurplusAtMost`, `PrimeCoalescentSurplusAtMost` |
| Ramanujan / singular series | `c_q(h)`, weight `μ²(q)/φ(q)` | `ramanujanLagCoefficient` (BVI), `RHTower.Sieve.sqfreeTotientInv` |
| Stabilizer model | parity-locked `2Σ_{q odd}(μ²/φ²)(q)c_q(h)`; literal model and retained discrepancy | `parityStabilizerWeight`, `stabilizerModelOddCoalSum`, `stabilizerDiscrepancyOddCoalSum` |
| Parity-twin germs | odd core of an order; cyclotomic digamma/harmonic kernels; odd-frequency torsion energy | `oddCore`, `cyclotomicDigamma`, `cyclotomicHarmonic`, `oddTorsionEnergy` |

## 3. Language

- **Sub-/trans-threshold**: `λ ≤ 1` / `λ > 1`.
- **Coalescent band**: prime pairs with `0 < |log(n/m)| ≤ T^{−1+η}`; window cannot resolve them.
- **Budget**: share of `N(T,2T)` the coalescent surplus may cost; `1/18` at `λ = 4/3` buys `3/4`.
- **Core**: archimedean + pole + prime diagonal; `43/36` at `λ = 4/3` (`= 1/λ + λ/3`).
- **Channels**: the nine bilinear pieces of `𝓜_Ω[ν_X, ν_X]`; only prime–prime carries the coalescent kernel.
- **Collar**: grid points where the weight `W_T < 1`; costs `32πε₁` of proportion.
- **Parity lock**: coalescent prime pairs are odd primes at even shifts; `c_2 = +1` on them.
- **Survival cone**: coefficient vectors on which a renormalized germ's counterterm vanishes.

## 4. Mechanisms

**A. Anatomy of the prime surplus (sharp window).**
1. Even `Φ`: eight half-line moments collapse to cosine + sine parts; `S⁺` is Lipschitz so the sine part has no
   close-pair pole, `|AminusSin| ≤ 2∫Φ²|x|` (`abs_AminusSin_le`).
2. Cosine part → Fourier kernel `πg` with `O(T⁻²)` tail (MV on the tail); exact identity
   `ppOffDiagFourier = 2π∫_T^{2T}(C_gC_1 + S_gS_1) − 2πTΣa_n²g`: diagonal cancels, surplus = mixed mean value
   (`ppOffDiagFourier_eq_primeDirichlet_integral`).
3. End form split bilinearly along `μ + Π_X + P_X`; archimedean part `X`-free, `O(Ll³ log l)` (`exists_abs_endForm_mu_mu_le`).
4. Jackson grid weights band-limit the pair kernel to `|θ| < 4b`; alias separation; far pairs paid by outer mass
   (`abs_weighted_frobenius_pp_sub_closeKernel_le`).

**B. Spectral side.**
5. `κ(4/3) = 9/8 + (9/8)I`; `≤ 5/4 ⇔ I = ∫_1^{4/3}(4/3−α)F ≤ 1/9` (twice GUE `1/18`); prime surplus ratio
   `(9/8)(I − 1/18) − 1/144`, GUE value `−1/144` (`primeSurplusRatio_bridge`).
6. General λ: `κ = (1/λ + λ/3) + (2/λ²)∫_1^λ(λ−α)(F−α)`; affine models give the five-model calibration
   (`calibration_five_models_four_thirds`): HL/GUE `−1/144`, uncorrelated `0`, Poisson `+1/16` (fails),
   spectral sieve `F ≤ Υ` passes iff `Υ ≤ 2`, unsigned additive sieve needs `Υ ≤ 8/9` (impossible).
7. Coalescent linearization `T log(1+h/m) → Th/m` with explicit error; Frullani: the Poisson linear term of
   `C_HL(H) = H − ½log H` integrates to zero against the dyadic kernel; the `−½log H` deficit gives
   `−(λ−1)³/(3λ²)` (`hl_coalescent_deficit_integral`).

**C. Localization.**
8. Height averaging (IBP `k` times against a smooth height weight): far pairs `|log(n/m)| > T^{−1+η}` and all
   sum frequencies are `o((aL)²Tℓ₁)`; only the coalescent band carries trans-threshold mass (`abs_avg_ppOffDiag_sub_close_le`).
9. Fejér: `∫F_b P_X²` is an exact positive pair sum over `|log(n/m)| < b`; two Fejér profiles dominate a Lorentzian
   ⇒ Lorentz mean square `≪ log X(3ψ(X) + RΣΛ/n)` — MV shape without Hilbert (`integral_lorentz_mul_PX_sq_le`).
10. Sub-Nyquist vanishing: `(n−m)/n ≤ log n − log m`, so pairs with `max(n,m) < θ₀⁻¹` (odd pairs: `< 2/θ₀`) vanish.

**D. Smooth-window certificate (the engine).**
11. Smooth grid weights: exact kernel difference identity, Lorentz grid sums, cell averaging at cost `√ℓ`
    (`KfunW_sub_mul_Kfun_eq`, `sum_lor_grid_le`); lattice deficit inside the window.
12. Continuous form: `Φ²⋆P_X = −2C_g`, so `𝓜_Ω[P_X,P_X] = π⁻¹Σa_na_m g(log m)[Ω̂(Δ) + Ω̂(Σ)]` exactly
    (`smoothPair_PX_PX_eq`); pairs beyond `θ₀` pay `‖Ω^{(k)}‖₁/θ₀^k`.
13. Nine channels: archimedean diagonal via Stirling increments; pole by decay; prime-linear channels by
    half-period shift; prime–pole by Cauchy–Schwarz against window mean squares (`smoothPair_nuX_le`).
14. Grid comparison: weighted Frobenius = `L²·𝓜_{W²}` up to Lipschitz sampling and lattice deficit, both
    against the window Lorentz weight (`abs_weightedFrobenius_sub_smoothForm_le`).
15. Weighted trace loses only its collar: telescoping cosine sums + Abel summation + Jordan on the alias
    interval (`sum_weighted_trace_ge`, `trace_ge_at`).
16. Rates in `v = T^{1/12}`: channel and grid errors `O(lT⁶v¹¹) = o(T log T)`; linear errors `O(T)`; `N_II = O(√T log T)`.
    `certificate_combine` is pure algebra: case `cs ≥ N` trivial, else `‖Ĝ‖² ≤ 3N`.

**E. Arithmetic reduction of the coalescent band.**
17. `p = 2` has no coalescent partner for `θ₀ < 1/3`; prime-only coalescent sum = odd primes at even shifts
    (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`). Partner window `|m−n| ≤ 2θ₀n`, `≤ 4θ₀n` partners, factor `n`
    cancels; Mathlib `ψ − θ ≤ 2√X log X` kills prime powers: `O(T^{−1/3+η}N)` (`abs_coalSum_sub_primeCoalSum_le`).
18. Parity-halved 2D Selberg prime-pair sieve, valid for every shift range `K` (`sum_card_primePair_le_parity_unrestricted`).

**F. Signed Ramanujan transfer.**
19. Inner lobe: `Ω̂(θ) ≥ ½Ω̂(0)` for `|θ| ≤ π/(3b)` ⇒ unsigned shift sums diverge like `T^{α−1}`.
20. Trapezoidal Dirichlet kernel `2sin(ϕ/2)(½ + Σcos rϕ + ½cos Mϕ) = sin Mϕ cos(ϕ/2)`; for Ramanujan sums the
    `1/θ` pole cancels across `d | q` because `Σμ(q/d) = 0` (`trapezoidal_ramanujan_cos_eq`); cotangent residual
    `≤ x` gives an `R`-uniform bound `σ₂(q)θ/4`.
21. Weighted by `μ²/φ²`, the HL singular series transfers to the negative Ward–Mertens sum
    `−½Ω̂(0)Σ_{q≤Q}μ²/φ` (`abs_sum_singularSeries_cosTransform_add_le`).
22. Even shifts: `c_q(2r) = c_{2q}(2r) = c_q(r)` (odd `q`), `c_2(2r) = 1`, `4|n` drops; mod-4 pairing doubles odd
    weights with a nonnegative top-octave bonus; the `q = 1,2` baseline transfers by IBP of the cotangent pole;
    full parity-locked series → `−Ω̂(0)Σ_{q odd}μ²/φ`; dynamic horizon `Q = ⌊m/b⌋` removes the cutoff premise.
23. Exact split: odd/even-shift coalescent sum = stabilizer model + centred discrepancy.

**G. Multiplicity and germs.**
24. Rank–trace with multiplicity excess: `4trÂ_w − ‖Â_w‖² − 2N + M_off ≤ s₁`; the certificate counts simple
    critical zeros minus off-line multiple mass (`seamA_weighted_mult2_offLineMultiple`).
25. Even-shift Ramanujan germs collapse to odd cores; Cesàro Gram `φ(oddCore)` on shared fibres; survival cone
    `{Σ_{fibre}C = 0}` for every renormalization. Pole-node erasure: any kernel depending only on the fibre
    pairs to `0` on the cone, so `−orbitIntersection` (the `Λ` term) drops out exactly.
26. Pole-node doubling ⇒ cyclotomic-harmonic kernel `H(x)+H(y)−H(x+y)` is PSD; as `u → ∞` the off-diagonal
    recovers `−φ(m)Λ(t)`, the diagonal regenerates `φ(m)log u` (counterterm moves UV → IR, cone `{0}`).
27. Dyadic split `E(r;q,2q) = ½E(r²;q,q) − E_odd(r;q,q)`: `I(q,2q) = φ(q)log 2` is a scale anomaly between
    even and odd frequencies.
28. Midpoint centring `T_{−v/2}(g − T_vg)` swaps even/odd Weil sectors with no cross term; with the AIP
    odd-window coercivity this gives short-cycle positivity at the `p = 2` shift.

## 5. Pillar theorems

| Statement | Lean | Status |
|---|---|---|
| Sine part has no close-pair pole; cosine part = mixed Dirichlet mean value with diagonal cancellation | `abs_AminusSin_le`, `ppOffDiagFourier_eq_primeDirichlet_integral`, `abs_ppDiag_add_ppOffDiagFourier_sub_integral_le` | unconditional |
| `κ(4/3) ≤ 5/4 ⇔ I ≤ 1/9`; surplus ratio `(9/8)(I−1/18) − 1/144` | `frobeniusFormFactor_four_thirds_le_five_fourths_iff`, `primeSurplusRatio_bridge` | identities |
| Five-model calibration: budget needs repulsion, unsigned sieves cannot meet it | `calibration_five_models_four_thirds` | identities |
| Height averaging leaves only the coalescent band | `abs_avg_ppOffDiag_sub_close_le`, `abs_avg_ppSumFreq_le` | unconditional |
| Narrow-strip exchange rate: gain `δ(2−(3E−4)δ)/(3(1+δ)²)` | `narrowStrip_beats_two_thirds_iff`, `narrowStrip_optimal_delta_gain` | identities |
| **Smooth-weighted certificate**: eventually `(29/36 − 32πε₁ − ε)N(T,2T) − coalescentSurplus ≤ N₀*(T,2T)` | `zeta_coalescent_certificate_four_thirds`, `zeta_coalescent_certificate` | unconditional |
| Simple-zero form: `(29/36 − ε)N − coalescentSurplus + M_off ≤ N₀ˢ`; prime-only version for `0 < η < 1/3` | `zeta_coalescent_certificate_simple_and_offLineMultiple`, `zeta_primeCoalescent_certificate_simple_and_offLineMultiple` | unconditional |
| Actual shape-one cosine certificate for `0<λ≤2`: `(Hcos(λ)+δλ−ε)N−Sλ≤N0simple`, `δλ=1/[200(10+720π²λ²)²]` | `zetaCosine_surplus_certificate` | unconditional; signed surplus retained |
| Explicit cosine coefficients `3/4+79/1250+δ(4/3)` and `5/6+43/3750+δ(2)` | `zetaCosine_fourThirds_surplus_certificate`, `zetaCosine_two_surplus_certificate` | unconditional; signed surplus retained |
| Raw odd-pair model mean `β/2`; actual prime-minus-model mean `1−β/2` | `StabilizerIncompletePeriods.lean`, `StabilizerPrimeRectangleDiscrepancy.lean` | raw rectangles only |
| Off-line ceiling `S_off + 2M_off ≤ (7/36 + ε)N + primeCoalescentSurplus` | `offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus` | unconditional |
| Coalescent surplus = odd primes at even shifts, up to `O(T^{−1/3+η}N)` | `primeCoalSum_eq_oddEvenShiftPrimeCoalSum`, `coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost` | unconditional |
| Parity-locked singular series transfers to negative Ward–Mertens repulsion | `abs_sum_full_evenShift_singularSeries_cosTransform_add_le`, `abs_sum_dynamic_poissonHorizon_singularSeries_add_le` | unconditional |
| Odd conductor cost `Σ μ²σ₂/φ²≤64Q`; horizon error `≤64Ωhat(0)`; odd main sum `∼(1/2)log Q` | `sum_odd_sqfree_sigma2_totient_sq_le`, `abs_dynamic_poissonHorizon_row_add_le`, `tendsto_sum_odd_sqfreeTotientInv_div_log_half` | unconditional; endpoint errors retained |
| Exact C² Poisson row and primitive-sample equality criterion; sharp horizon `Qb≤πm` | `stabilizerLinearRow_eq_dual`, `ramanujanSpatialDual_eq_primitive`, `stabilizerLinearRow_eq_neg_iff` | unconditional |
| Horizon coefficient `−Ωhat(0)/2`; positive complete and finite rows arbitrarily close beyond the horizon | `tendsto_stabilizerLinearRow_horizon_div_log`, `exists_positive_stabilizerLinearRow`, `exists_eventually_positive_finite_stabilizerRow` | unconditional; fixed-cutoff negative-row shortcut false |
| C⁴ aperture tail `≤2O(Q)D₄(m/2)⁴/R³`; row envelope `≤4D₄m⁴` independent of Q | `abs_stabilizerLinearRow_truncation_le`, `abs_stabilizerLinearRow_le`, `abs_sum_stabilizerLinearRow_le` | unconditional |
| Fixed-base limits: row/log Q→0; primitive correction/log Q→`Ωhat(0)/(2πm)` | `tendsto_stabilizerLinearRow_fixed_div_log_zero`, `tendsto_stabilizerSpatialDual_fixed_div_log` | unconditional; differs from moving horizon |
| Unsigned inner-lobe divergence | `sum_Icc_abs_cosTransform_ge_inner_lobe` | unconditional (no-go) |
| Parity-twin survival line; closed-form germ limits; Λ erased on the cone | `parityTwinPair_unrestricted_vs_evenShift_survivalCone`, `tendsto_shiftedMode_ramanujanGerm_closedForm`, `quad_torsionAlignedLimit_eq_neg_cyclotomicHarmonic_on_cone` | unconditional |
| PSD cyclotomic-harmonic kernel; IR relocation | `cyclotomicHarmonicKernel_nonneg`, `completedTwinKernel_infrared_survivalCone_eq_zero` | unconditional |
| Short-cycle Weil positivity at shift `log 2` | `even_shortCycle_m_one_re_W_ge` | unconditional, aperture `≥ 3/200` |

## 6. Tools

**Developed.**
- Smooth-window Gram pipeline at `λ = 4/3`: `WindowProfile` → grid comparison → nine channels → weighted
  trace → rates → `certificate_combine`. Reusable with any window and any surplus definition.
- Exact identities: `ppOffDiagFourier_eq_primeDirichlet_integral`, `smoothPair_PX_PX_eq`, `KfunW_sub_mul_Kfun_eq`,
  `trapezoidal_ramanujan_cos_eq`, `sum_singularSeries_evenShift_eq_odd_split`, `torsionEnergy_dyadic_parity_split`.
- Lorentz/Fejér mean squares without Hilbert (`integral_lorentz_mul_PX_sq_le`, `integral_lorentz_mul_primeDirichletCos_sq_le`).
- Trace tools: `abs_sum_mul_cos_le_abel`, `two_min_div_le_abs_sin`, `abs_weighted_P_part_le_lipschitz`.
- Prime-power elimination in short multiplicative windows (`abs_coalSum_sub_primeCoalSum_le`).
- Parity-halved prime-pair sieve for all shift ranges (`sum_card_primePair_le_parity_unrestricted`).
- Ramanujan cotangent-pole cancellation and `R`-uniform transfer (`abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le`).
- Cross-programme identifications: `ramanujanSum_eq_ramanujanLagCoefficient` (AET), `ramanujanMode_eq_ramanujanLagCoefficient` (RBG).
- Germ calculus: divisibility germ limits (`tendsto_divisibilityGerm_add_log`, `tendsto_shiftedDivisibilityGerm_add_log`),
  `harmonicFn` asymptotics, pole-node erasure.

**To build.**
- An actual signed upper bound for `zetaCosineFrobSurplus`; the matched certificate is proved through `λ=2`.
- A literal stabilizer-model calibration under the signed logarithmic kernel. The raw scalar `1/4` has mean `1/8`; scalar two has unit raw mean.
- A signed estimate for `stabilizerDiscrepancyOddCoalSum` on odd primes at even shifts within `T^{−1+η}`.
- A sieve that keeps lobe signs (`1_ℙ(m)1_ℙ(m+2r)` against the signed coalescent kernel).
- Transfer from the height-averaged prime-pair sum to `F(α)` on `(1, 1+δ]`.
- A quadratic narrow-strip surplus bound `β(δ) ≤ Bδ²/(1+δ)²`.

## 7. Open questions

1. `oddEvenShiftPrimeCoalescentSurplus u η T ≤ (1/18 + o(1))N(T,2T)` for one profile and one `0 < η < 1/3`
   (gives `3/4`; any `β < 5/36` beats `2/3`; `β ≤ 577/4500` beats `HD(1)` — thresholds in ACS).
2. Control the centred stabilizer discrepancy (prime-pair correlation minus truncated HL series) against the
   signed coalescent kernel below budget, uniformly in the cutoff. Truth (HL/GUE) is `−1/144`.
3. Narrow strip: any `β(δ) = O(δ²)` gives a proportion `> 2/3` with explicit gain.
4. Signed mixed mean value `∫_T^{2T}(C_gC_1 + S_gS_1)` at `X = T^{4/3}`.
5. Does the parity-twin survival line (rank 1 on `{q,2q}`) carry any prime information once the counterterm
   is relocated, or is erasure of `Λ` on every survival cone structural?
6. Extend short-cycle positivity beyond aperture `181/500 − (log 2)/2` or to shifts `log p`, `p > 2`.

## 8. Traps

| Trap | Truth |
|---|---|
| Triangle inequality on the eight moments | `O(L²X) ≫ Tl³` for `λ > 1`; all cancellation lost |
| Sharp window `1_{[T,2T]}` | endpoint leakage `O(1/|θ|)`; smooth or Jackson weights needed |
| Jackson weights reach the coalescent band | only `|θ| < 4b` is exact; far pairs cost `jacksonOuterErr`; the band is reached by smooth windows (`smoothPair_PX_PX_eq`), not by Jackson |
| Height averaging with `X` moving in `T` | the averaged identities fix `L`; average the Gram before evaluating the prime side |
| Prime–pole channel by sup norms | `|Π_X| ≤ 3√X`, `|P_X| ≤ π⁻¹Σa_n` over a length-`T` window lose a power; use `O(√X/τ)` decay of `Φ²⋆Π_X` and Cauchy–Schwarz against window mean squares |
| Lorentz/Fejér mean values settle close pairs | size bounds; the problem is signed |
| Positive spectral majorants | Fejér shift gives `I ≤ 8/27`, factor `8/3` short of `1/9` |
| Unsigned sieve on `|Ω̂|` at prime shifts | inner lobe diverges like `T^{α−1}`; additive sieve needs `Υ ≤ 8/9 < 1` |
| Poisson model = HL main term | Poisson without repulsion gives `+1/16 > 1/18`; the budget uses `−½log H` |
| Budget = power saving | must land below `1/18` against truth `−1/144` (slack `1/16`) |
| `CoalescentSurplusAtMost` / `PrimeCoalescentSurplusAtMost` as results | they are Props (premises); only their equivalence is proved |
| Survival-cone positivity speaks about primes | pole-node erasure removes `−orbitIntersection` (`Λ`) exactly on the cone |
| Short-cycle positivity is a global Weil statement | one shift `log 2`, symmetric tests, support `≤ 0.0153` |
| Zero-side slack instead of prime surplus | refuted for `λ ∈ (0,3/4)` by the grid-dimension ceiling (ACS) |
| Higher moments bypass pair correlation | arithmetic cap `kλ ≤ 1` only |

## 9. Context

| Relation | Programme | Interface |
|---|---|---|
| imports (17) | RHTower | Gram/trace/seam infrastructure: `ZetaTraceWide`, `ZetaFrobeniusSurplusSplit`, `ZetaThreeQuartersOfPrimeSurplus`, `ZetaThreeQuartersOfSurplus`, `ZetaThreeQuartersReduction`, `ZetaWeighted*`, `ZetaFejerWeight`, `PairCorrelationExchangeRate`, `Sieve.PrimePairAverageSharp`, `Zeta23OffLineMultipleExclusion`, `ThmEUniformEnds` |
| imports (3) | RenormalizedBiarithmeticGeometry | periodic germs, survival cones, Ramanujan twins, pole node |
| imports (2) | BezoutValuationIncidence | `ramanujanLagCoefficient`, HL singular series of the damped source |
| imports (1 each) | AET, ACS, AIP, ACT | Ramanujan sums as torsion energy; short cycles; odd-window Schur lending (`0.362`); parity-folded gauge |
| imported by | ArithmeticCastelnuovoSeveri | `CoalescentSurplusAndTransThresholdProportionLaws`: budgets → proportions, `HD(1)` and off-line moments |
| imported by | ArithmeticCorrelationGeometry, SelectivePositivityAndThresholdLaws, RenormalizedArithmeticPotentialTheory, MainTheorems | coalescent surplus as gauge charge; parity-lobe obstruction; Ramanujan pole profiles |
| sibling | SquareRootThreshold | phase transition of `L²` methods at `X = T`; TTPC is its finite form |
| sibling | ScaleSignedIncidenceCriticality | `2/3` as a resolution limit (double zero vs coalescing pair) |
| sibling | TransHorizonIncidenceMechanics | parity barrier of sieves beyond the cutoff |

## 10. Big picture

TTPC isolates the signed prime correlation required beyond the unconditional bandwidth range.
The smooth box certificate retains a coalescent surplus; the shape-one cosine certificate now
retains its matching Frobenius surplus and explicit pinching credit through bandwidth two.
Neither source surplus has the upper bound needed for 75% simple critical zeros.

The affine HL/GUE calibration predicts a negative coalescent contribution. It is not yet an
evaluation of the literal finite Ramanujan model, whose raw normalization and conductor cutoff
must be retained. Unsigned factor-two bounds alone cannot replace the signed input: smooth
densities arbitrarily close to one can have logarithmically divergent phase-weighted discrepancy.
