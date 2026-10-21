# SRT explicit-lag loop (goal: 100 significant contributions toward `P_v ≥ 0` for `v ≥ V`)

- **ID:** srt-explicit-lag-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md (research topics 1, 2, 4)
- **Statement:** For `ζ` and one generic width, prove `P_v ≥ 0` for all `v ≥ V` with explicit `V`,
  knowing that every crystal and every finite off-line set has a first negative lag.

## Goal
100 contributions, each meeting one of: (1) explicit unconditional `V`; (2) visibility at
`ζ`-density for a non-attained top with controlled lag; (3) off-diagonal prime pairs at `λ > 1`
with the consequence for `P_v`; (4) exact aperture/height/length tradeoff with the strongest
unconditional estimate; (5) the proof says what replaces the attainment premise of grids.
Not counted: nonselective positivity apertures, invisibility without witness, pair-correlation
restatements.

## Coordination
Other agents work in `SquareRootThreshold/` (window prime polynomial, Stieltjes, zero-count
remainder, ground-energy bridges). Check `ls SquareRootThreshold/` before naming a module. My lane:
effective (finite-window) visibility of the lag family, records, non-attained tops, grids.

## Conjecture queue
1. Finite Laplace windows: `P_v ≥ 0` on `[0, V]` bounds the Laplace pole of every off-line zero
   by the potential of the others (effective Landau inequality; record-potential law).
2. Non-attained tops (chains) seen by the continuum lag family at an explicit lag.
3. `ζ`: companion law at the Legendre record from finite lag positivity, with the corpus
   zero-free region, local count and 6/5 density.
4. Grids: z-transform (Pringsheim) version; the attainment premise replaced by a non-aliasing
   condition at the record.
5. Clusters: Toeplitz/positive-definite version of the Laplace window in the height variable.

## Contribution ledger (append-only)
- **L1 · Finite lag windows: the record-potential law** — `FiniteLagWindowRecordPotentialLaw`.
  Criteria 2, 5. `norm_evenCoeff_mul_lapWin_le`: if the difference family is nonnegative on a
  finite range `[0, V]`, then for every exponent `z₀` and `s = σ + it`,
  `|D(z₀)E_V(z₀−s)| ≤ |M|(|E_V(−σ)|+|E_V(−s)|) + Σ_z|D||E_V(z−σ)| + Σ_{z≠z₀}|D||E_V(z−s)|`,
  `E_V(z) = ∫_0^V e^{zu}du` (`lapWin`), via `|G(σ+it)| ≤ G(σ)` for the Laplace window of the
  nonnegative `φ(0) − φ` (`norm_integral_cexp_mul_le`, `integral_lagWindow_eq`). Effective Landau:
  every exponent is tested, not only the top. `loudness_bound_of_lag_nonneg` /
  `exists_lag_neg_of_loudness`: with `|Im z| ≥ η`, separation `g` from `s`, `κ = 1/η + 1/g`,
  `θ = Re z₀ − σ`, `2κNθ ≤ 1` and loudness ratio `Σ|D|e^{Re z V} ≤ N|D(z₀)|e^{Re z₀ V}`, negativity on
  `[0, V]` once `κN|D(z₀)|(e^{θV} − 2) > 4|M|/σ + κΣ|D|`: first negative lag
  `≤ θ⁻¹ log(2 + (4|M|/σ + κΣ|D|)/(κN|D(z₀)|))`, valid for non-attained tops (the record exists at
  every lag). `zeta_crowding_of_lag_primeWindow_nonneg`: for ζ (η = 4), `P_v ≥ 0` on `[0, V]` forces
  every loud off-line zero to be crowded. What replaces attainment: the loudness ratio at the lag
  itself. Axioms: [propext, Classical.choice, Quot.sound]. Olean built; wired.
- **L2 · Lag grids: the aliasing-potential law** — `LagGridAliasingPotentialLaw`. Criterion 5.
  Grid window `G(ζ) = Σ_{k≤K}(φ(0) − φ(kℓ))ζ^k` has nonnegative coefficients, `|G(ζ)| ≤ G(|ζ|)`;
  termwise `G(e^{−sℓ}) = φ(0)Q_K(e^{−sℓ}) − Σ_z D(z)Q_K(e^{(z−s)ℓ})`, `Q_K(w) = Σ_{k≤K} w^k`
  (`geomWin`, `sum_lagGrid_eq`, `norm_sum_cexp_mul_le`). `norm_evenCoeff_mul_geomWin_le`: grid
  record-potential law. `grid_loudness_bound_of_lag_nonneg` / `exists_grid_lag_neg_of_loudness`:
  distances `|Im z|`, `|z − s|` become aliasing gaps `|1 − e^{(z−σ)ℓ}| ≥ η`, `|1 − e^{(z−s)ℓ}| ≥ g`;
  with `κ = 1/η + 1/g`, `2κN(e^{θℓ} − 1) ≤ 1`, some grid lag `≤ Kℓ` is negative once
  `κN|D(z₀)|(e^{θ(K+1)ℓ} − 2) > 4|M|/(1 − e^{−σℓ}) + κΣ|D|`. What replaces attainment on a grid:
  no loud zero aliases onto the positive real axis or onto the record. C54's hidden chain is
  exactly the case `η → 0` (grid images `e^{δ_n + iθ_n}` accumulate at `e^{1/4}`).
  `zeta_grid_crowding_of_lag_primeWindow_nonneg`: ζ version on prime windows `X = e^{kℓ}`.
  Axioms: [propext, Classical.choice, Quot.sound]. Olean built; wired.
- **L3 · Grid-hidden chains have an explicit continuum lag** —
  `GridHiddenChainsHaveAnExplicitContinuumLag`. Criteria 2, 5 (non-attained top, explicit lag).
  Abstract record law for real exponential sums over any countable index
  (`norm_coeff_mul_lapWin_le_of_le`, `record_bound_of_le`: `|p_{j₀}|(e^{θV} − 1)/θ ≤ 4|M|/σ +
  (1/η + 1/g)Σ|p_j|(e^{(Re μ_j−σ)V} + 1)`), real parts via the doubled family
  (`re_tsum_eq_doubled`). For the C54 chain (`δ_n ↑ ¼` unattained, `Re ≤ 0` at every integer lag):
  at `V = 2^{m+3}` the term `m` is the Legendre record, `c_n e^{δ_nV} = (e^{2^{m+1}}/2^{m+1})x_ne^{−x_n}`,
  `x_n = 2^{m−n}`, loudness ≤ 4e× record (`gridChain_loudness_le`); `gridChain_lag_bound`: if
  `Re Σ ≤ M` on `[0, V]` then `4e^{V/20}/V ≤ 9|M| + 1`; `exists_re_gridChainSum_gt`: level `M` is
  exceeded at a lag `≤ 2^{m+3}` once `(9|M|+1)2^{m+3} < 4e^{2^{m+3}/20}` — continuum lag `O(log M)`,
  grid lag never. Replaces Landau's non-effective unboundedness (`not_bddAbove_re_gridChainSum`).
  Axioms: [propext, Classical.choice, Quot.sound]. Olean built; wired.
- **L4 · The Fejér lag window: a cubic record potential** — `FejerLagWindowCubicPotentialLaw`.
  Criteria 2, 5. Weight `sin²(πu/V)` keeps the positivity of the Laplace window; kernel
  `F_V(z) = ½E_V(z) − ¼E_V(z+2πi/V) − ¼E_V(z−2πi/V) = 2π²(e^{zV} − 1)/(z(V²z² + 4π²))`
  (`fejerWin`, `fejerWin_eq`, `sin_sq_mul_cexp_eq`), cubic decay
  `|F_V(z)| ≤ (8π²/3)(e^{Re z V}+1)/(V²|z|³)` for `V|z| ≥ 4π` (`norm_fejerWin_le_cube`).
  `integral_fejerWindow_eq`, `norm_evenCoeff_mul_fejerWin_le` (weighted record law),
  `fejer_loudness_bound_of_lag_nonneg` / `exists_lag_neg_of_fejer_loudness`: with `κ₃ = 1/η³ + 1/g³`,
  `Vη, Vg ≥ 4π` and `(8/3)κ₃Nθ(V²θ² + 4π²) ≤ V²`, negativity on `[0, V]` once
  `(4/3)κ₃N|D(z₀)|(e^{θV} − 2) > |M|(1/σ³ + 8/(3η³)) + (4/3)κ₃Σ|D|`. With `θ = κ/V` the side
  condition is `V³ ≥ (8/3)κ₃Nκ(κ² + 4π²)`: loudness ratio enters as `N^{1/3}` (L1: `N`). Residual
  requirement: resolution `V ≳ 1/g` of the record's gap (square-root-threshold scale at ζ spacing).
  `zeta_fejer_crowding_of_lag_primeWindow_nonneg` (η = 4). Axioms clean; olean built; wired.
  - Correction to L2 (docstrings fixed, oleans rebuilt): C54's chain defeats the grid law because
    its grid images alias onto the record and the real axis at the record's own scale `θℓ`
    (gaps `O(θℓ)`, side condition off by `N`), not because `η_ℓ → 0`.
- **L5 · Lag positivity forces close companions for ζ** — `ZetaLagPositivityForcesCloseCompanions`.
  Criteria 2, 5 (ζ itself, ζ-density via the corpus local count, non-attained tops allowed).
  Counting: `card_carrier_window_le`, `card_exponent_window_le`, `card_exponent_unitWindow_le`
  (≤ 160 log(180(|a|+5)) exponents with height in `[a, a+1]`, from `RHTower.card_le_of_ordinates_in_window`).
  Cubic potential: `sum_window_weight_le`, `sum_inv_cube_le`, `tsum_inv_cube_le`
  (`Σ|z−s|^{−3} ≤ 480 log(180(|Im s|+6))(1/r³ + 3)` over exponents at distance ≥ r).
  Records: `exists_right_record` (Legendre record of right exponents exists at every lag),
  `exists_right_exponent_of_offLine`. `zeta_companion_law`: if `P_v ≥ 0` on `[0, V]`, `V ≥ π`,
  for the right record `z*`, `σ = Re z* − κ/V`, no other exponent within `r` of `s = σ + iIm z*`
  (`Vr ≥ 4π`), `V³ ≥ (8/3)κ(κ²+4π²)Π`, `Π = 480 log1080(1/64+3) + 480 log(180(|Im z*|+6))(1/r³+3)`:
  `(4/3)Π|D(z*)|(e^κ − 2) ≤ |M|(1/σ³ + 1/24) + (8/3)Σ|D|(1/64 + 1/r³)`.
  `zeta_lag_negative_or_record_bound`: for all but countably many `w`, if RH fails then at every
  `V ≥ π`: some `P_v < 0` on `[0,V]`, or the record obeys the bound — i.e. it is quiet or has a
  companion within `r ≍ κ(log|Im z*|)^{1/3}/V` of `(Re z* − κ/V, Im z*)`. Only the local zero count is
  used. Axioms clean; olean built; wired.
- **L6 · Hiding requires loud twins** — `ZetaHidingRequiresLoudTwins`. Criterion 2 (ζ, no exclusion
  hypothesis). `norm_lapWin_le_max`, `norm_fejerWin_le_max` (`|F_V(w)| ≤ V max(1, e^{Re w V})`),
  `norm_mul_fejerWin_le_near`. `zeta_twin_law`: with the near zone `0 < |z − s| < r` charged rather
  than excluded, `P_v ≥ 0` on `[0, V]` forces `(4/3)Π|D(z*)|(e^κ − 2) ≤ |M|(1/σ³ + 1/24) +
  (8/3)Σ|D|(1/64 + 1/r³) + (V³/2π²)Σ_near|D(z)|(1 + e^{(Re z−σ)V})`. With `V³ ≥ (8/3)κ(κ²+4π²)Π`
  a non-quiet record hides only if the near zone carries loudness `≳ |D(z*)|e^κ/κ³` (the record's own
  loudness at σ, up to κ³): loud twins within `r ≍ κ(log|Im z*|)^{1/3}/V`. Lag-side form of the
  corpus' clustering wall ("any shallow-pair producer must work inside clusters").
  Axioms clean; olean built; wired.
- **L7 · The unconditional lag envelope of ζ** — `ZetaLagFamilyUnconditionalEnvelope`. Criteria 1, 4
  (explicit unconditional V, exact zero-free-region/envelope tradeoff, strongest corpus estimate).
  `norm_lagCoeff_le_decay` (`|F(z)| ≤ m e^w B_b²(1+|Im z|)^{−4}` from `h_K = h_b·conj h_b`),
  `summable_norm_evenCoeff_mul_sq` (`S₂ = Σ|D|(1+|Im z|)² < ∞`, tempered).
  `abs_two_re_lagStructure_le_of_zeroFree`: zero-free width η below height G ⟹
  `|φ(v)| ≤ e^{v/2}(W e^{−ηv} + S₂/(1+G)²)` (exact tradeoff of height cut vs width).
  ζ profile: `re_le_of_mem_zetaCarrier_low` (`Re ρ ≤ 1 − η₀`, `η₀ = zeroFreeConst/(2·25⁹)`,
  `|γ| ≤ e^{23}`, from `Sieve.riemannZeta_ne_zero_of_re_gt` at `N = ⌈e^{24}⌉`),
  `re_le_of_mem_zetaCarrier_high` (`1 − 1/(100 log|γ|)` above `e^{23} ≥ e^{29K/63}`,
  `exp_dlvpSharpConstant_le`), `re_le_of_evenCoeff_zeta`. **`zeta_lag_envelope`**: for every
  `w ∈ (0, ½log2)` and `v ≥ V₀ = max(230², 1/(100η₀²))`:
  `P_v ≥ −|φ(0)| − (W + S₂)e^{v/2 − √v/10}` — explicit lag, explicit rate (dlVP strength).
  Axioms clean; olean built; wired.
- **L8 · The two-parameter lag family sees near-top zeros of ζ (up to twins)** —
  `ModulatedLagFamilySeesNearTopZerosOfZeta`. Criteria 2, 5 (non-attained tops, controlled lag,
  ζ itself). `zeta_twin_law_of_bump` (twin law for any C² bump), `four_le_abs_im_of_mem_zetaCarrier`,
  `mult_le_log_zeta` (`m ≤ 40 log(180|γ|)` from the local count via `xiDivisorZetaCarrierEquiv`),
  `norm_paperFT_scaledBump_le`, `norm_lagCoeff_modScaledBump_le`, `norm_evenCoeff_modScaledBump_le`
  (two-sided decay `(1+|Im z ∓ c|)^{−4}`), `norm_evenCoeff_modScaledBump_center_ge`
  (`|D_c(z₀)| ≥ a_w² − 40log(180c)(e^{w/2}B_w)²/(1+2c)⁴` at `c = Im z₀`),
  `abs_im_le_of_norm_evenCoeff_modScaledBump_ge` (records stay at height ≤ max(2c, (2880K)^{1/3})).
  **`zeta_modulated_near_top_twin`**: for a zero `½+z₀` that is `1/V`-near the top (exists for every
  V if RH fails, attained or not), modulated to `γ₀`, the record keeps `|D(z*)| ≥ a_w²/(2e)`
  uniformly in V; with explicit `κ = twinKappa(...)`, `V ≥ 2κ/Re z*`, `V³ ≥ (8/3)κ(κ²+4π²)Π`:
  positivity on `[0,V]` forces another zero within `r` of `(Re z* − κ/V) + iIm z*`. What replaces
  attainment: a near-top zero plus modulation to its height. Escapes: loud twins, or near-top zeros
  at heights `log γ₀ ≳ (V/κ)³`. Axioms clean; olean built; wired.
- **L9 · Fejér power lag windows (order-k record potential)** — `FejerPowerLagWindowKernel`.
  Weight `sin^{2k}(πu/V)`, kernel `K_k(z) = ∫_0^V sin^{2k}(πu/V)e^{zu}du`; recursion
  `(z² + ((2k+2)π/V)²)K_{k+1} = (2k+2)(2k+1)(π/V)²K_k` by one FTC (`fejerPowWin_succ`); decay
  `|K_k(z)| ≤ (4/3)^k(2k)!(π/V)^{2k}(e^{Re zV}+1)/|z|^{2k+1}` for `V|z| ≥ 4πk`; real lower bound
  `K_k(x) ≥ (2k)!(π/V)^{2k}(e^{xV}−1)/(x(x²+(2πk/V)²)^k)`; archimedean `|K_k(−σ)| ≤ 2(2k)!(π/V)^{2k}/σ^{2k+1}`;
  window identity and order-k record-potential law for any tempered config. Axioms clean; wired.
- **L10 · The twin radius of ζ at the uncertainty scale** — `ZetaTwinRadiusAtTheUncertaintyScale`.
  Criteria 2, 4, 5. `zeta_powTwin_law` (order-k twin law, general C² bump), `exists_loud_record_of_near_top`,
  `zeta_powTwin_of_record`, **`zeta_near_top_twin_radius`**: for every k ≥ 1 with `log L ≤ 2k+1`
  (`L = log(180(|γ*|+6))`), positivity of the modulated family on `[0,V]` with
  `V ≥ 73(κ+2πk)max(1,2/Re z*)` forces a twin within `73(κ+2πk)/V`, `κ = log(3+e(|M|+W)/(60La²))`;
  **`zeta_near_top_twin_radius_log_log`**: radius `73(κ + π log log(180(|γ*|+6)) + 4π)/V`.
  Improves L8's `κ(log γ)^{1/3}/V` to the uncertainty scale `1/V` up to `κ + log log γ`.
  Twin closer than mean spacing once `V ≫ (κ + log log γ) log γ`: square-root threshold missed by
  `κ + log log γ`. Open: bound `|M|, W = O(L)` for the modulated family (makes κ a w-constant).
  Axioms clean; olean built; wired.
- **L11 · Uniform twin radius of near-top zeros of ζ** — `ZetaUniformTwinRadiusOfNearTopZeros`.
  Criteria 2, 4, 5. Mass of the modulated family: `|M| ≤ W ≤ 16(e^{w/2}B_w)²(C + log(c+4))` via the
  corpus Lorentzian zero mass (`RHTower.lorentzMass_le_log`) and a copies/multiplicity lemma
  (`sum_mult_le_tsum_copies`); loud records sit at `γ₀/2 ≤ |Im z*| ≤ Γ_w(γ₀)` and depth `≥ Re z₀/2`;
  depth offset uniform: `κ ≤ κ_w = log(3 + 32e(e^{w/2}B_w)²(C+1)/(60a_w²))`.
  **`zeta_uniform_twin_radius`**: near-top zero at height γ₀ (beyond explicit w-height), positivity
  of the modulated family on `[0,V]`, `V ≥ 73(κ_w + π log log(180(Γ+6)) + 4π)max(1,4/Re z₀)` ⟹ twin
  within `73(κ_w + π log log(180(Γ+6)) + 4π)/V`, `Γ ≤ 2γ₀` for large γ₀. All constants explicit in w.
  Also generalized L10's radius theorems to any `κ ≥ twinDepth`. Axioms clean; olean built; wired.
- **L12 · Hiding needs near-top twins at every lag** — `ZetaHidingNeedsNearTopTwinsAtEveryLag`.
  Criteria 2, 5. `exists_high_near_top_zero` (non-attained top ⟹ 1/V-near-top zeros above every
  height), `nearTopHeight` `T_w = 1 + 700000(e^{w/2}B_w)²/a_w²` with `nearTopHeight_conditions`,
  **`zeta_hiding_needs_near_top_twins`**: RH fails with non-attained top ⟹ ∀V,T ∃ 1/V-near-top zero
  above max(T,T_w): negative modulated lag ≤ V, or `V < hidingLag` (log log γ₀ ≳ V Re z₀), or twin
  within `R_w(γ₀)/V`. Escape height improved from `exp(cV³)` (one-parameter) to `exp exp(c_wΘV)`.
  The remaining barrier (twins closer than log log γ/V) is the pair-correlation barrier. No
  zero-specific hypotheses left. Axioms clean; olean built; wired.
- **L13 · An attained top of ζ is visible at an explicit lag** — `ZetaAttainedTopIsVisibleAtAnExplicitLag`.
  Criteria 2, 4. `exists_separation_in_box` (zeros in `|Im| ≤ H`, `Re ≥ ½+d` are g-separated),
  **`zeta_attained_top_visible`/`zeta_attained_top_first_negative_lag`**: zero of largest real part
  `½+δ₀` at height γ₀ ≥ T_w ⟹ the modulated family has a negative difference test at a lag
  `v ≤ max(V_w(z₀), (R_w + κ_w)max(1, 1/g, 4/δ₀))` = `O_w((1+log log γ₀)/min(g,δ₀))`. Effective
  version of `AttainedDepthIsVisible` for ζ; data: depth, height, local separation only. (L11 now
  exports record depth ≥ δ₀/2 and γ₀/2 ≤ |Im z*| ≤ Γ.) Axioms clean; olean built; wired.
- **L14 · Twins are exponentially tight unless tripled** — `ZetaTwinsAreExponentiallyTightUnlessTripled`.
  Criteria 2, 4, 5. Cluster record-potential law for finite S (`norm_sum_evenCoeff_mul_fejerPowWin_le`),
  ζ cluster noise with explicit bracket (`zeta_powCluster_le`, `clusterBracket_le`),
  **`dipole_elimination`**: `(x₂²+β²)A_{k+1} − cA_k = D₁(x₂−x₁)(x₂+x₁)K_{k+1}(x₁)` (two Fejér orders
  eliminate the twin exactly via the recursion), **`zeta_dipole_law`**, `mirror_alternative`
  (depth κ or 4κ avoids the mirror point), **`zeta_isolated_twin_tight`**, and
  **`zeta_near_top_twin_tight_or_triple`**: near-top record has two other zeros within 2r, or a twin
  within `(4/3)A_w log(180(Γ+6))(4+2π(k+1))/(3^k V)` for every k with `Vr ≥ 2(4+2π(k+1))` —
  i.e. twin distance `≤ C_w log γ₀ · r·e^{−cVr}`, c = log3/(4π). Hiding needs triples or
  exponentially tight pairs. Next: n-cluster elimination (Vandermonde in 1/(x²+β_j²)).
  Axioms clean; olean built; wired.
- **L15 · Near-top clusters collapse beyond the threshold** — `ZetaNearTopClustersCollapseBeyondTheThreshold`.
  Criteria 2, 4, 5. Iterated elimination `elimSeq` (`Φ(ys,m) = Σ D Π(y − x²) K_{m+|ys|}(x)`),
  `elimSeq_cons` (one step = order-raising operator `E_y`), `norm_elimSeq_le` (each elimination
  costs 8/3 in noise units), `elimSeq_eq_record_add`, **`zeta_cluster_collapse`** (all loud
  companions within r of s eliminated at once; quiet members as explicit noise) and
  **`zeta_cluster_collapse_explicit`** (no quiet members):
  `|D(z*)|(e^κ−1)κ^pV^{2k+p+1}r^{2k+1}Π|z−z*| ≤ κ(8/3)^p(4/3)^k(κ²+4π²(k+p)²)^{k+p}Ξ`.
  Geometric-mean radius of a p-cluster hiding a record ≤ O(r e^{−cVr/p}); with p ≤ O(log γ) the
  collapse sets in at Vr ≫ log γ — beyond the square-root threshold: positivity forces approximate
  multiple zeros near the top. Axioms clean; olean built; wired.
- **L16 · An attained top of ζ is visible at a lag logarithmic in the separation** —
  `ZetaAttainedTopIsVisibleAtALogarithmicLag`. Criteria 2, 4. `finite_evenCoeff_ball`,
  `exists_depth_avoiding_mirrors` (pigeonhole over P+1 depths in [κ₀,2κ₀]),
  `zeta_full_cluster_collapse` (eliminate every companion), `near_top_record_facts`,
  `mass_le_of_record_height`, `xi_ratio_le`, `attained_log_arith`, `exists_box_count_and_separation`,
  **`zeta_attained_top_visible_log`**: first negative lag of an attained top
  `O_w((P log(P/g) + log log γ₀)/δ₀)` (explicit inequality with V^{2k+p+1} vs g^p), improving L13's
  `O(1/g)` exponentially in the separation. Axioms clean; olean built; wired.
- **L17 · Near-top zeros of ζ hide only in collapsed clusters** — `ZetaNearTopZerosHideOnlyInCollapsedClusters`.
  Criteria 2, 4, 5. **`zeta_near_top_cluster_collapse`**: for every 1/V-near-top zero above T_w
  (attained or not), positivity on [0,V] ⟹ the record has a cluster C of p ≤ P zeros (all within
  r − 2κ₀/V, none beyond r + 2κ₀/V) with `Π_C|z − z*|·(κ₀/(2(P+1)))^p V^{2k+p+1} r^{2k+1} ≤ B(p)`
  (`clusterCollapseBound`). p = 0 impossible for large V (twin law); p ≥ 1 gives geometric-mean
  radius `λ^{−2k/p}`-small: approximate multiple zeros of multiplicity ≤ P+1. Unifies L10–L16.
  Axioms clean; olean built; wired.
- **L18 · Local-count refinement of L16–L17** — the box count hypothesis replaced by the local zero
  count `P ≥ 80 log(180Γ)` (companions within 1 of the record, `card_exponent_window_le`). Attained
  tops: first negative lag `O_w((log γ₀·log(log γ₀/g) + log log γ₀)/δ₀)`; collapsed clusters have
  multiplicity `p + 1 ≤ 80 log(180Γ) + 1`. Both modules rebuilt, axioms clean.
- **L19 · The one-parameter lag family hides only in collapsed clusters** —
  `OneParameterLagFamilyHidesOnlyInCollapsedClusters`. Criteria 2, 5 — for the goal's own family
  (one fixed width, c = 0). `two_mul_sq_le_norm_evenCoeff_zero` (|D(z₀)| = 2m|h_w(γ₀−iδ₀)|²),
  `exists_loud_record` (any bump), `one_param_record_facts` (height ≤ Γ₀(η) ~ η^{−2/3}, depth ≥ δ₀/2),
  `xi_ratio_le_general`, **`one_param_cluster_collapse`**: positivity of P_v on [0,V] ⟹ the record
  of any 1/V-near-top zero with η = |h_w(γ₀−iδ₀)| > 0 carries a cluster of p ≤ 80 log(180Γ₀) zeros
  with Π|z−z*|·(κ₀/(2(P+1)))^p V^{2k+p+1}(δ₀/8)^{2k+1} ≤ B₀(p) (`oneParamCollapseBound`).
  Constants explicit in w, η. Axioms clean; olean built; wired.
- **L20 · The one-parameter lag family sees attained tops at an explicit lag** —
  `OneParameterLagFamilySeesAttainedTopsAtAnExplicitLag`. Criteria 1(partial), 2, 4 — for P_v itself.
  **`one_param_attained_top_visible`** / **`one_param_attained_top_primeWindow_neg`** (prime side,
  2w < log 2): attained top of ζ with η = |h_w(γ₀−iδ₀)| > 0 ⟹ P_v < 0 for some v ≤ V under explicit
  conditions; first negative lag `O_w((log(1/η)·log(log(1/η)/g) + log log(1/η))/δ₀)`. Effective
  version of AttainedDepthIsVisible for the goal's family; covers every finite off-line set.
  Axioms clean; olean built; wired.
- **L21 · Isolated twins of ζ cannot hide** — `ZetaIsolatedTwinsCannotHide`. Criteria 2, 5.
  New insight: coefficients D_c(z) = m(h(−iz−c)² + small) of nearby zeros are phase-coherent
  (`re_coherent_squares_nonneg`: nearby squares of a smooth transform cannot cancel), so an
  exponentially tight twin ADDS to its record (`norm_coherent_pair_ge`) and cannot hide it.
  Ingredients: `norm_fejerPowWin_sub_ofReal_le`, `norm_paperFT_scaledBump_sub_le` (via corpus
  `RHTower.norm_paperFT_sub_le`), `evenCoeff_modScaledBump_eq_mult_mul`, `norm_reflected_le`,
  `evenCoeff_conj`, `le_norm_paperFT_of_loud`, `re_twin_mul_conj_nonneg`, `quiet_record_arith`.
  **`zeta_isolated_twins_cannot_hide`**: positivity of the modulated family on [0,V] (explicit
  conditions) forces ≥ 2 further zeros within 2r of the near-top record. Twin alternative of L10–L14
  reduced to triples. (L14's ζ theorem now exports record facts.) Axioms clean; olean built; wired.
- **L22 · Coherent cores add up** — `ZetaCoherentCoresAddUp`. Tools for removing the cluster
  alternative: `norm_sum_coherent_ge` (coherent weighted sums keep the record), `exists_empty_annulus`
  (P+1 nested annuli, one empty: core/loose split with gap G), `norm_prod_sub_prod_le`,
  `zeta_partial_elimination_le` (eliminate only the loose members), `norm_mul_sub_mul_le`,
  `norm_core_sum_ge` (eliminated coherent core ≥ |F*|K(θ)|D*|/2). Axioms clean; olean; wired.
- **L23 · Near-top zeros are visible (no attainment)** — `ZetaNearTopZerosAreVisibleBelowAnExplicitHeight`.
  `zeta_near_top_visible`: a zero `1/V`-near the top at height `γ₀` forces a Weil-negative difference
  test of the bump modulated to `γ₀` at some lag in `[0, V]`, under explicit numeric conditions on
  `(k, κ₀, ρ, G, H₀)`. Mechanism: empty annulus (core radius `ρ/G^{j+1}`, loose beyond `ρ/G^j`),
  partial elimination of the loose members only, phase coherence of the core
  (`eliminated_core_ge`), then the L17 arithmetic with `Π|y−z*|` replaced by `ρ₁^p/2`. Closes the
  collapsed-cluster door of L17. Heuristic parameter count: hypotheses hold for
  `V ≫_w log²γ₀ · log log γ₀ / δ₀` (to be made explicit in L24). Axioms clean; olean; wired.
- **L24 · Explicit polylogarithmic lag for near-top zeros** — `ZetaNearTopZerosAreVisibleAtAPolylogarithmicLag`.
  `zeta_near_top_visible_at_polylog_lag`: explicit `V_w(γ₀, δ₀) = nearTopLag` (closed form via
  `nearTopCount/Coherence/Gap/Ratio/Order/Scale`); a zero `1/V`-near the top with `V ≥ V_w(γ₀, δ₀)` and
  `1280 log(180Γ)(e^{w/2}B_w)² ≤ a(1+γ₀)⁴` is seen by a modulated difference test at a lag in `[0, V]`.
  `V_w ≍_w (log γ₀)² log log γ₀ / δ₀`. Corollary `zeta_depth_gap_of_lag_positivity`: positivity on
  `[0, V]` ⟹ a zero more than `1/V` deeper exists. Replaces the attainment premise: an unattained top
  is approached only by zeros of depth gap ≥ 1/V_w(γ, δ) ≍ δ/((log γ)² log log γ). Criteria (1), (2), (5).
  Axioms clean; olean; wired.
- **L25 · The one-parameter family P_v sees near-top zeros** — `OneParameterLagFamilySeesNearTopZeros`.
  For the problem's own family (c = 0): `evenCoeff_modScaledBump_zero_eq_two_mul` (D = 2m h_w(−iz)²,
  no reflected term), `re_one_param_mul_conj_nonneg` (coherence without height condition),
  `le_norm_paperFT_of_loud_zero`, and `one_param_near_top_visible`: a zero 1/V-near the top with
  η = |h_w(γ₀ − iδ₀)| > 0 makes some P_v < 0, v ∈ [0, V], under explicit conditions. Closes the
  collapsed-cluster door of L19. Axioms clean; olean; wired. The L24 parameters were refactored into
  η-free generic `explicitCount/Coherence/Gap/Ratio/Order` + `collapse_form_lt` for reuse.
- **L26 · Explicit lag for P_v itself** — `OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag`.
  `one_param_near_top_visible_at_explicit_lag`: for the problem's family P_v (unmodulated, c = 0), a
  zero 1/V-near the top with 0 < η ≤ |h_w(γ₀ − iδ₀)| and V ≥ V₀(w, η, δ₀) = `oneParamLag` gives
  P_v < 0 for some v ∈ [0, V]; no height condition; V₀ ≍ (log Γ₀)² log log Γ₀/δ₀, Γ₀ ≍ η^{−2/3}.
  `one_param_depth_gap_of_lag_positivity`: P_v ≥ 0 on [0, V] ⟹ every zero with V₀ ≤ V lies ≥ 1/V
  below the top. Criteria (1), (2), (5) for the single family P_v. Axioms clean; olean; wired.
- **L27 · Horizon law for P_v** — `OneParameterLagFamilyHorizonLaw`. `oneParamHorizon w z = V₀(w,
  |h_w(−iz)|, Re z)`. `one_param_horizon_law`: for a width with h_w(−iz) ≠ 0 at all zeros, P_v ≥ 0 on
  [0, V] ⟹ from every zero inside the horizon (V₀ ≤ V) a zero beyond it (V₀ > V) is reached, deeper
  by > 1/V (iterated depth gap, < V/2 steps). `one_param_visible_of_horizon`: if all zeros deeper than
  z₀ + 1/V are inside the horizon, some P_v < 0 on [0, V] — the attainment premise replaced by a
  condition on zeros beyond the horizon. `one_param_near_top_primeWindow_neg`: prime-window form of
  L26 (2w < log 2). Criterion (5). Axioms clean; olean; wired.
- **L28 · Loud records are visible at an explicit lag** — `OneParameterLagFamilyRecordsAreVisibleAtAnExplicitLag`
  (+ refactor of L25). `one_param_record_visible` (L25 file): the record z* of P_v at lag V with
  |D(z*)| ≥ a, |Im z*| ≤ Γ, Re z* ≥ σ is visible under explicit conditions (bound `recordCollapseBound`);
  `one_param_near_top_visible` is now a corollary. `one_param_record_visible_at_explicit_lag`:
  V ≥ V(a, σ) = `recordLag` with Γ(a) = `recordHeightOf` ⟹ P_v < 0 on [0, V];
  V(a, σ) ≍ log²(1/a)·loglog(1/a)/σ. Every near-top variant now reduces to a record lemma.
  Axioms clean; olean; wired.
