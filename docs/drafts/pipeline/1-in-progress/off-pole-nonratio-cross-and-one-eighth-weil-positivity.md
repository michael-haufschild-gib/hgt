# Off-Pole Non-Ratio Cross Norm and Weil Positivity Up to the Eighth-Root Ceiling

- **ID:** off-pole-nonratio-cross-and-one-eighth-weil-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Σ-2 / Σ-3 (remaining `c⁹ → c⁸`)
- **Statement:** For every `0 < α < 1/8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
  `completeWeilMatrix tiltedUnitSpline c N` is positive definite on all vectors.

## Goal
Matches the eighth-root receiver (`RH ⇔` eventual sign at every `α > 1/8`): the unconditional
exponent would equal the RH-detection exponent of the tilted spline, so
`log edge(N)/log log N → 1/8` along falsifying subsequences under `¬RH`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
The `1/9` proof loses `c⁹` (vs. the necessary `c⁸`) at three places; each must drop to `c⁸·polylog c`.

1. **Two-region reserve (`K c⁹ ≤ θ₁ log N`).** On `w ∈ V_{R₁}^⊥`, reserves are `≍ log N · P`
   (prefix `[1, M]`, `M = N/L_c`) and `≍ (log N / c⁷) S` (terminal `(M, N]`). The prefix→terminal
   non-ratio block `NR_{PT}` has Schur row `≍ c` (prefix) and column `≍ c log N` (terminal), hence
   `‖NR_{PT}‖² ≲ c² log N`; paying it needs `c² log N ≤ log N · log N/c⁷`, i.e. `c⁹ ≤ log N`.
   *Tightness:* the column `Σ_{|j|≤ec} Σ_{k | n−j} Λ(k) ≈ 2ec log n` is pointwise sharp, and the
   Schur test is attained near the Perron vector `n ↦ n^{−1/2}`, i.e. the pole mode `v_{1,N}`.
2. **Band–terminal cross (`c⁹(1+log c)/log N`).** Same block, paired against `u ∈ V_{R₁} ∩ V_1^⊥`.
3. **Inverse-energy residual sum (`Σ_{m≤Q₁} ‖r_m‖²/E_m ≪ c⁹/log N`).** `‖r_m‖² ≍ c²/log N` comes
   from near-center/near-gamma rows on `N/(R_c+1) < n ≤ N`; on `[1, M]` those rows vanish.

**Terminal-pole-orthogonality is not enough (refuted).** The bound
`|⟨NR_PT x, y⟩|² ≤ C c (1+log c)^A log N ‖x‖²‖y‖²` for `y ⊥ v_{1,N}` is false. Take `x = P v₁`
(prefix pole) and `y(n) = n^{−1/2}(log n − μ_S)` on `S = (M, N]`, with `μ_S` the `1/n`-weighted mean,
so `y ⊥ v_{1,N}`. The prefix-pole column is exact, `Σ_{k | n'} Λ(k) = log n'`, so
`Σ_m NR(m,n) m^{−1/2} ≈ n^{−1/2} |W(n)| log N` with window `|W(n)| ≈ 2cn/N`. The pairing reads the
*unweighted* moment `(c/N) Σ_{n∈S} Y(n) ≍ c log c`, not the pole moment `Σ Y(n)/n = 0`:
`⟨NR_PT x, y⟩ ≍ c log c log N`, `‖x‖² ≍ log N`, `‖y‖² ≍ (log c)³`, ratio to the bound `≍ c/(log c)^{A+1}`.
No PNT enters; only the divisor identity. The orthogonality that can work is the global one below.

## Global orthogonality and the coherent cross term

The actual condition is `w ⟂ v₁` before the prefix–terminal split. Neither
piece is separately pole-orthogonal. If `p=P v₁` and `q=S v₁`, then
`⟨Pw,p⟩=−⟨Sw,q⟩`; hence
`|⟨Pw,p/‖p‖⟩|≤(‖q‖/‖p‖)‖Sw‖`.
For cutoff `M≈N/c`, the ratio is `O(sqrt(log c/log N))`.

A second candidate is therefore an input-pole decomposition
`NR_PT = a ⊗ (p/‖p‖) + E`, with
`‖a‖=O(c sqrt(log N))` and `‖E‖²=O(c·polylog(c)·log N)`.
Global orthogonality would reduce the coherent cross payment to
`O(c sqrt(log c))‖Sw‖²`; the terminal reserve then asks only for
`c⁸ sqrt(log c)=o(log N)`. The remainder has the desired eighth-power
Schur cost. The divisor-jet cancellation with the near-Gamma row is the
available source identity for identifying `a`.

This decomposition is unproved. The earlier output-pole projection alone
does not supply it; the coherent output need not be proportional to `q`.
Band–terminal and inverse-energy residual improvements remain required.

## Structure of `NR_PT` (paper, heuristic where marked)

- **The coherent part is rank one.** `NR_PTᵀ â ∝ p` with `â(n) ∝ √n` on `S`, because
  `Σ_{k≤X} Λ(k) k ≈ X²/2`. Star poles and low conductors are coherent only through their overlap with
  `p`: `NR_PT(P x_d) ≈ (c log N/d) â`. So `a = σ â`, `σ ≍ c √log N`.
- **The remainder on `x ⊥ p` is a shifted-correlation problem.** With `X(m) = √m x(m)` and
  `F = Λ ∗ X`, `‖NR_PT x‖² ≈ Σ_{|h|≤2c} ω_h Σ_{n∈S} F(n)F(n−h)/n`, `Σ ω_h ≍ c²`. The `h = 0` term is
  `≤ 2c log c log N ‖x‖²` (Cauchy–Schwarz over `k | n`), which is the target level. The `h ≠ 0`
  terms count prime pairs `km − k'm' = h`; no unconditional bound with a saving is available.
- **What suffices.** With reserves `θ log N · P` and `κ log N/c⁷ · S`, positivity needs
  `‖E‖² ≤ c (log N)^{1+δ}`, `δ = 1 − 8α`: a saving `(log N)^{9α−1}` over the trivial `c² log N`.
- **Terminal reserve is small on two families.** `archForm` of a terminal atomic test is
  `≈ ∫ |φ̂(wξ)|² |D_y(ξ)|² Θ(ξ) dξ`, `D_y(ξ) = Σ y_n n^{−iξ}`. It is `≈ (κ/c⁷) log N` per unit mass
  for Mellin-smooth `y` (`|ξ| ≲ 1`) and for destructive-overlap `y` (local period `< c`, where
  `φ̂(wξ)` is small). It is `≈ c log|t|` per unit mass at Mellin frequency `|t| ≪ N/c`.

## Proof plan (paper; `α < 1/8`, `δ = d/c⁷`, `k₁ ≍ θ₁ log N`)

The `1/9` proof needs `c⁹ ≲ log N` in exactly three places: the far two-region reserve, the
band–far cross, and the `V_{Q₁}`–complement Schur. Each is replaced as follows.

**T1. Far reserve.** For `w ∈ V_{R₁}^⊥`, `w = x + y` (prefix `[1,M]`, top `S = (M,N]`):
`E(w) = arch(f)/G − prime(f)/G` (pole term zero), and
`prime(f) = prime(f_x) + prime(f_y) + 2⟨f_y, f_z⟩`, `z = a ∗ x`, `a_k = Λ(k)k^{−1/2}`
(the prime translate of an atomic test is the atomic test of the Dirichlet convolution).
- Prefix block `≥ (7/8)D_M − O(c)P` (separated atoms); top self-prime `≤ C c(1+log c) S`
  (multiples of `k` in a window); top arch `≥ (log T − C)·HM_T(f_y) + (δ/2) log N · S − C c S`,
  `HM_T = (1/2πG)∫_{|r|≥T}|f̂_y|²`.
- Cross, coherent part: `x = α p̂ + x_⊥`, `|α| ≤ ‖q‖‖y‖` from `w ⊥ v₁`; costs `O(c log c) S`.
- Cross, remainder: `z_⊥ = ρ·(a ∗ x_⊥)` (`ρ` smooth log-cutoff, `=1` where `f_y` lives),
  `Π` = log-smoothing at scale `1/T₁` (`Πv(n) = Σ v(n')K(log n/n')/n'`). `Πz_⊥` loses its
  coherent part exactly (`Σ_m x_⊥(m)m^{−1/2} = 0`); rows `n/m ≥ K'` pay the PNT error
  `exp(−c₀√log X)` (`RHTower.exists_psi_error_eventually`) times `T₁`, rows `n/m < K'` are
  averaged: `‖Πz_⊥‖² ≲ (log K')² P`, `log K' ≍ (log T₁)²`. High part: `f̂_{z−Πz}` is
  `(1 − K̂(r)) f̂_z` up to Euler–Maclaurin error (`RHTower.sum_Ioc_floor_eq_integral`), small
  below `T = T₁/c⁵`; above `T` it is paid by `HM_T(f_y)` at cost `(c log N log c/log T) P`.
  With `log T₁ ≍ C c log c` every cost is `≤ k₁P/16 + c^{6+o(1)}/log N · S`.
- Conclusion: `E(w) ≥ (k₁/4)P + (b k₁/(2c⁷))S` whenever `c⁸ (log c)^A ≤ ε log N`.

**T2. Band–far cross.** In `⟨W u, w⟩` (`u ∈ V_R ∩ V_Q^⊥`, `w ∈ V_R^⊥`) the corpus bounds the
center, separated, `overlap − downward` and upward channels one at a time
(`exists_completeWeil_cross_le_c9_split_reserves`). Two of them carry `c⁹`:
`X = c²(1+log R)(1+log c) G / log N`, `G = Σ (1+log m) a_m²`, from the center collar and from
`K₂ᵦ·v_jet` (`overlap − downward = K₁ + K₂ₐ + K₂ᵦ v_jet`, `Down(c_m) = log n·c_m − jet_m`).
Both live on the top rows.

- **Coherent parts cancel.** `jet_m` has the pole component `Λ(m) c_1`, so `K₂ᵦ v_jet` contains
  `s·(α n/N) v_1`, `s = Σ a_m Λ(m)/√φ(m)` (`α = completeWeilPoleShift`, the `K₂ᵦ` row mass is
  `α n/N`). An exact band vector is `u = Σ a_m v_m + (s/ℓ) v_1 + …`, since
  `⟨v_m, v_1⟩ = −Λ(m)/(ℓ√φ(m)) + O(m/N)` (`Σ_{n≤N} c_m(n)/n = −Λ(m) + O(σ(m)/N)`). The center
  collar `−(α/N) ω` on `(s/ℓ) v_1` returns `−(s/ℓ)(α/N)√n (log n + O(1))/√ℓ`, which is
  `−s(αn/N)v_1` on the top rows up to a relative `O(1/ℓ)`. Separately, each channel's coherent
  cross is `≍ α s/√ℓ`; together, `O(α s/ℓ^{3/2})`.
- **Oscillating remainders need sharp bounds.**
  (b) center collar on high conductors: near kernel `1/(2|h|)` has multiplier
  `M_D(ξ) = Σ_{h≤D} cos(2πhξ)/h`, `|M_D(r/m)| ≤ log(m/min(r,m−r)) + 2`, so
  `φ(m)⁻¹ Σ_{(r,m)=1} M_D(r/m)² = O(m/φ(m))` instead of `(1+log R)²`;
  (c) `K₂ᵦ` on spiky packets (conductors `> c^{2+ε}`): `‖K₂ᵦ x‖² ≲ (c + c²τ(k)/φ(k))‖x‖²` per
  conductor `k`, via the shifted Gram `Σ_{n<M} c_k(n+i)c_l(n+j) = [k=l] M c_k(|i−j|)`
  (`sum_range_ramanujanLagCoefficient_shift_mul`) plus period boundaries `O(R⁵/N)`.
  With (b), (c): center `c⁹ loglog R/log² N`, jet `c⁸ θ log c/log N` per unit band reserve.
- **Upward:** split by rows; prefix rows against the prefix reserve, top rows read only `u|_S`.

**T3. `V_{Q₁}`–complement Schur.** Pair `y ∈ V_{Q₁}` with `z = u₀ + u₁ + w` blockwise.
- `y–w` closes with the existing residual sum (`Σ ‖r_m‖²/E_m ≲ (c⁷+Q²)c²(log N)^{ε−1}`):
  prefix rows against the prefix reserve `≍ log R` (`c⁹/log² N`), top rows against
  `κ log N/c⁷` (`c^{16}/log² N`).
- `y–band` needs the residual on deep rows `n ≤ N/X_*`. Upward channel: available per row,
  `|affineShellCorrection − c_q(n)·shellCorrection| ≤ C c/(log Y)^k` for every `k`,
  `Y = N/(2cn)` (`exists_conductor_uniform_affineShellCorrection_linear_log_rate`). Near
  channels vanish for `n < N/(2c)`; center and separated decay like `n/N`. Prime residual,
  self, pole and downward channels: deep-row bounds not yet extracted.

**T4. Assembly.** Four blocks `y, u₀, u₁, w` with the corpus band coercivities and band–band
cross, replacing the three `c⁹` inputs above.

## No-go closure
- **Killed:** terminal-pole-orthogonal smallness of `NR_PT` (counterexample above).
- **Positive survivor:** rank-one coherent structure `NR_PT ≈ σ â ⊗ p̂ + E`; exact prefix-pole
  column law from `Σ_{k|n} Λ(k) = log n`; target `‖E‖² ≤ c (log N)^{1+δ}`.
- **Status:** proof plan T1–T4 above; Lean in progress (CACT modules listed below as built).

## Lean modules
CACT, compiled, wired into the umbrella (T1):
- `TheTopPrimeSelfFormCostsOnlyALogarithm` — top prime self-form `≤ C c(1+log c) S`.
- `TheGammaFormPaysEveryFrequencyAboveAThreshold` — `arch ≥ (log T − G₀)·HM_T − (G₀+log 2)·LM_T`; Fourier split of `2|∫fh|`.
- `ThePrimeCrossOfAPrefixAndATopIsADirichletConvolution` — `P(f_{x+y}) = P(f_x)+P(f_y)+2∫f_y f_{ρ(a∗x)}`.
- `TheWindowAverageOfAnAtomicTest` — window smoothing `g_h`, multiplier `|1−m_h| ≤ |r|h`, `∫(f_V^{(h)})² ≤ (∫g)² h⁻² ∫W_V²`.
- `TheWindowSumsOfThePrimeTranslateCancelOffThePole` — dlVP short windows; `∫W² ≤ windowSumBound`; `‖ρ(a∗x)‖² ≤ log B·log(2B/A)·P`.
- `TheFarReserveThroughTheWindowAverage` — explicit reserve `(7/8)D_M + (3/8)δ log N·S − costs(h,T,K')` on `(V_1)ᗮ`.
- `TheFarReserveBelowTheEighthRoot` — `eventually_completeWeilEnergy_far_reserve_below_one_eighth`: for `α < 1/8`, `θ > 0`, on `(V_1)ᗮ`, `(7/8)D_M + κ/(4c⁷)·log N·S − θ log N·P ≤ E`.
- `ThePolynomialConductorComplementIsCoerciveBelowTheEighthRoot` — on `(V_{⌊N^θ⌋})ᗮ`, `(c_orth log N/c⁷)‖z‖² ≤ E` for `α < 1/8`; nonpositive subspaces have dimension `≤ ⌊N^θ⌋` (corpus had both below `1/9`).

T2, compiled, wired into the umbrellas (details on `band-far-cross-below-one-eighth.md`):
- `CompletedArithmeticForms.TheNearCollarCostsTheMeanLogarithmicMultiplier` — sharp near collar.
- `TheNearGramFormOfAPacketCostsItsDivisorMean`, `TheReducedDivisorJetCostsItsDivisorMean` — `K₂ᵦ` on the jet.
- `TheJetPoleComponentCancelsThePole` — coherent pole pair.
- `TheBandFarCrossBelowTheEighthRoot` — `exists_band_far_cross_le_channels`: the cross with every
  channel paid by a free reserve parameter; non-prime channels share `bandFarChannelBudget`
  (`c^{8+o(1)}/log N` per unit band reserve at `M = N/L_c`).

Open: T2 specialization to the assembly shape (`(1/32)E + (1/4)‖u‖² + (k₁/32)P + (bk₁/(32c⁷))(S + ‖w‖²)`,
eventual smallness, `ρ` from the quadratic residual bound), T3 deep rows (no paper proof yet),
T4 assembly.
