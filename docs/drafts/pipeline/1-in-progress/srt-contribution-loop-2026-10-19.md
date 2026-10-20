# SRT contribution loop (goal: 100 field-native contributions)

- **ID:** srt-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md (read-only)
- **Statement:** Develop the Square-Root Threshold field by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field.

## Goal
100 significant contributions: native to SRT (its objects: configurations, apertures, heights,
windows, depth, lattices, prime polynomial), expanding what the field explains or solves.

## Coordination
A second agent works in the same folder on the window / off-diagonal direction (README open
problem 1; e.g. `DoubleWindowMinApertureAndPairCorrelationExchange`). This loop works on the
configuration side (open problem 2: clusters, depth profiles, visibility geometry) unless a
queue item needs otherwise. Check `ls SquareRootThreshold/` before naming a module.

## Conjecture queue
1. Periodic depth profiles: exact Poisson formula with symbol
   `D(m) = Σ_r 2cosh(δ_r mL/P) e^{2πirm/P}`; Toeplitz visibility law.
2. Sparse off-line sublattice (density `1/P`): discrete isolated-pair law below `L/2`.
3. Smooth depth ramps: visibility aperture grows with ramp length (roughness law).
4. Transfer of the edge law to `ζ` via single-height positivity (`X ≲ (log T)²`).

## Log
- 2026-10-19 — loop started; README and review read; queue seeded.

## Contribution ledger (append-only)
- **C1 · Off-line run edge law** — `OffLineRunEdgeVisibilityLaw`.
  `W_runConfig_eq_integral`: a run of `N` off-line pairs of depth `δ` replacing doubled on-line
  lattice points has `W = 2L‖f‖² + ∫ k(u)·2(cosh δu − 1)·Σ_run e^{2πiku/L} du` below Nyquist.
  `re_W_runConfig_nonneg`: invisible whenever `2δa sinh(2δa) ≤ 1`, `4a ≤ L`, uniformly in `N`
  and position. `exists_re_W_runConfig_neg`: if `cosh(δa) > 1 + 8π²`, one test detects every run
  `1..N` with `N ≥ N₀(L)` in every background `L ≥ L₀`. Visibility is carried by the edges
  (kernel `e^{iθ}/(1 − e^{iθ})`, `Im ≥ 2/(πθ)`; far edge removed by Riemann–Lebesgue). Threshold
  `Θ(1/δ)`, independent of `L` and `N`: an isolated pair hides to `log(4δL)/2δ`, the infinite
  lattice to `L/2`. Answers README open problem 2 for runs. Standard axioms.
- **C2 · Toeplitz visibility law for periodic depth profiles** — `PeriodicDepthProfileToeplitzLaw`.
  `profileConfig`: residue `r mod P` carries the pair `½ ± d_r` (double on-line point if `d_r = 0`).
  `W_profileConfig`: at every aperture, `W(f,f) = (L/P) Σ_m k(mL/P) D(m)` with depth symbol
  `D(m) = Σ_r 2cosh(d_r mL/P) e^{2πirm/P}` (Poisson on each residue class).
  `profileConfig_weil_nonneg_iff`: invisible at aperture `a` ⟺ the `n×n` Toeplitz matrix
  `[D(j−j')]` is PSD, `n = ⌈2aP/L⌉` (⇐ by periodization `lagSum_eq_integral_toeplitzSum` into
  Toeplitz sums of samples `f(s+kL/P)` on one cell; ⇒ by narrow bumps at the lag points).
  Turns every periodic visibility question into finite-dimensional Toeplitz positivity; the
  lattice law is the case `P = 1`. Standard axioms.
- **C3 · Depth profiles are seen through the Fourier modes of cosh(depth)** —
  `DepthProfileFourierModeLaw`. `depthSymbol_zero` (`D(0) = 2P`), `depthSymbol_neg`
  (`D(−m) = conj D(m)`). `norm_depthSymbol_le_of_weil_nonneg`: invisibility at aperture `a` forces
  `|D(m)| ≤ 2P` for `1 ≤ m < ⌈2aP/L⌉`. `re_toeplitzForm_ge` + `profileConfig_weil_nonneg_of_modes`:
  `Σ_{0<|m|<n}|D(m)| ≤ 2P` suffices (Gershgorin). `profileConfig_weil_nonneg_iff_first_mode`: on
  `L/(2P) < a ≤ L/P`, invisible ⟺ `|Σ_r cosh(d_r L/P) e^{2πir/P}| ≤ P`.
  `twoProfile_weil_nonneg_iff`: two interleaved lattices of depths `δ₀, δ₁` are invisible on
  `L/4 < a ≤ L/2` ⟺ `|cosh(δ₀L/2) − cosh(δ₁L/2)| ≤ 2`. New insight: below Nyquist a test sees the
  discrete Fourier modes of `r ↦ cosh(d_r mL/P)`; uniform depth has none and hides to `L/2`, depth
  contrast is visible (alternating `(δ,0)` seen at `L/4` once `cosh(δL/2) > 3`). Standard axioms.
- **C4 · Nyquist ceiling for periodic depth profiles** — `DepthProfileNyquistCeiling`.
  `exists_re_W_profileConfig_neg_of_nyquist_lt`: every periodic profile with an off-line residue
  is visible at every aperture `a > L/2` (period mode `D(P) = 2Σ_r cosh(d_r L) > 2P`).
  `profileConfig_weil_nonneg_nyquist_iff`: it hides up to the ceiling `L/2` ⟺ its `P×P` Toeplitz
  matrix is PSD. `uniformProfile_weil_nonneg_of_le_nyquist` (via `depthSymbol_const_eq_zero`):
  constant depth reaches the ceiling for every period. New insight: the square-root threshold
  `L/2` is the maximal hiding aperture over the whole periodic class at density `L/2π`; the
  lattice law is the extremal case, and extremality is Toeplitz positivity. Standard axioms.
- **C5 · Smooth depth modulations hide up to a logarithmic aperture** —
  `SmoothDepthProfileHidingLaw`. Periodic summation by parts (`one_sub_mul_sum_pow`,
  `norm_sum_pow_le`), the mean-value bound for second differences of `cosh(v·d)`
  (`abs_second_diff_cosh_le`) and `|1 − e^{2πim/P}| ≥ 4m/P` give
  `norm_depthSymbol_le_of_smooth`: `|D(m)| ≤ P³(2vκ₂ sinh vδ + 4v²κ₁² cosh vδ)/(16m²)`, `v = mL/P`.
  `profileConfig_weil_nonneg_of_smooth`: invisible at `a ≤ L/4` when
  `PLκ₂ sinh(2δa)(1+log n)/8 + nL²κ₁² cosh(2δa)/4 ≤ 1`, `n = ⌈2aP/L⌉`. For a smooth profile of
  amplitude `δ` and period `P` (`κ₁ ≍ δ/P`, `κ₂ ≍ δ/P²`) this is `e^{2δa} ≲ P/(δL log P)`: the
  modulation hides up to `≈ (1/2δ) log(P/(δL))`. New insight: the visibility aperture of a depth
  profile is set by its smoothness scale — edges `O(1/δ)` (C1), smooth modulations of length `Λ`
  logarithmic in `Λ/δ`, uniform depth the ceiling `L/2` (C4). Standard axioms.
- **C6 · Total-variation blindness of off-line clusters** — `ClusterTotalVariationBlindness`.
  `clusterConfig`: finitely many lattice ordinates pushed off-line to variable depths `d_k`.
  `W_clusterConfig_eq_integral`: `W = 2L‖f‖² + ∫ k(u) Σ_k 2(cosh(d_k u) − 1) e^{2πiku/L} du`.
  Summation by parts along the lattice (`one_sub_mul_tsum_zpow`) and `|cosh x − cosh y| ≤
  sinh M |x − y|` give `norm_cluster_sum_le`: `|Σ| ≤ (L/2) TV(d) sinh(δ|u|)`.
  `re_W_clusterConfig_ge`/`_nonneg`: `Re W ≥ 2L(1 − a·TV(d)·sinh(2δa))‖f‖²`, so any cluster with
  `a·TV(d)·sinh(2δa) ≤ 1` is invisible (`4a ≤ L`). `depthVariation_runSet_const`: a constant run
  has `TV = 2δ`, recovering C1's blindness. New insight: blindness depends only on the total depth
  variation (edges included) and the maximal depth — not on length, position or profile shape.
  Standard axioms.
- **C7 · Height averages are blind to small-variation clusters and Toeplitz-positive profiles** —
  `WindowedBlindnessForClustersAndProfiles`. `temperedConfig_clusterConfig`,
  `temperedConfig_profileConfig`; `re_windowedW_clusterConfig_nonneg`: every windowed form at
  resolution `r` (`4r ≤ L`, `r·TV(d)·sinh(2δr) ≤ 1`) of every cluster is nonnegative for tests of
  every aperture; `re_windowedW_profileConfig_nonneg` (Toeplitz PSD of size `⌈2rP/L⌉`) and
  `re_windowedW_profileConfig_nonneg_of_smooth`. Extends the averaging no-go from lattices to all
  small-TV clusters and smooth/Toeplitz-positive profiles: an edge visible at `O(1/δ)` to single
  tests is invisible to every height average at resolution `r ≲ 1/δ`. Standard axioms.
- **C8 · Band-limited depth modulations hide up to half the Nyquist aperture** —
  `BandLimitedDepthProfileHidingLaw`. `cosProfile δ P r = δ(1 + cos(2πr/P))/2`.
  `sum_cosProfile_pow_mul_root_eq_zero`: the discrete Fourier coefficient at `m` of `d^{2n}`
  vanishes for `2n < m ≤ P/2` (`d_r = (δ/4)(1+ζ^r)(1+ζ^{-r})`). `cosh_sub_taylor_le`: Taylor
  remainder of cosh. `norm_depthSymbol_cosProfile_le`: `|D(m)| ≤ 2P (eℓδ)^m e^{mℓδ}`, `ℓ = L/P`.
  `cosProfile_weil_nonneg`: if `e(L/P)δ e^{(L/P)δ} ≤ 1/3` (period ≳ 8δL) the modulation is
  invisible at every aperture `a ≤ L/4`. New insight: the square-root threshold is not a privilege
  of uniform lattices — slow band-limited depth modulations hide within a factor 2 of it, far
  beyond the generic smoothness bound (C5); what is seen early is roughness (edges, few derivatives).
  Standard axioms.

### C9 — Crystalline fragility of off-line lattices (`CrystallineFragilityOfOffLineLattices.lean`)
- **Abstract Toeplitz law** `weil_nonneg_iff_toeplitz_of_lagFormula`: any `ZeroConfig` with lag formula `W(f,f) = ℓ Σ_m k(mℓ) D(m)` is Weil-nonnegative at aperture `a` iff the Toeplitz form of `D` of size `⌈2a/ℓ⌉` is PSD. Decouples the Toeplitz law (C2) from lattice profiles.
- **Periodic off-line patterns** `patternConfig`, `W_patternConfig`: `P` off-line pairs per period `2π/ℓ` at arbitrary ordinate offsets `c_r`; symbol `D(m) = Σ_r 2cosh(d_r mℓ) e^{i c_r mℓ}`.
- **Jitter law** `jitterConfig_weil_nonneg_iff`: lattice of depth `δ`, ordinates `2πk/L + (−1)^k ε`; for `L/4 < a ≤ L/2` invisible iff `cosh(δL/2)|sin(εL/2)| ≤ 1`.
- **Crystalline fragility** `jitterConfig_visible`: relative jitter `η` with `cosh(δL/2) sin(πη) > 1` ⇒ visible at the Nyquist aperture `L/2`. Hiding a dense off-line configuration up to the square-root threshold requires arithmetic-progression ordinates to relative precision `e^{−δL/2}` (≈ `T^{−δ/2}` at height `T`).
- Axioms: [propext, Classical.choice, Quot.sound]. Olean built single-threaded; wired after BandLimitedDepthProfileHidingLaw.

### C10 — Crystal rigidity at the square-root threshold (`CrystalRigidityAtTheSquareRootThreshold.lean`)
- Fixed-shape periodic off-line pattern: `P` pairs per period, depths `d_r ∈ (0,½]`, relative ordinates `θ_r` distinct mod 1; at scale `ℓ` ordinates `(2π/ℓ)(θ_r + j)`, Nyquist aperture `Pℓ/2`.
- **Spectral crystallinity** `norm_powerSum_le_of_hiding`: uniform depth `δ`, hiding at `a > (P−1)ℓ/2` ⇒ `|Σ_r e^{2πiθ_r m}| ≤ P/cosh(δmℓ)` for `1 ≤ m < P`.
- **Crystal rigidity** `uniform_crystal_of_hiding`: hiding above `(P−1)ℓ/2` at unboundedly many scales ⇒ all depths equal and `P(θ_r − θ_r') ∈ ℤ`. Mechanism: deepest pairs dominate every mode as `ℓ → ∞`; Newton's identities (`aeval_esymm_eq_zero_of_powerSums`, `not_forall_powerSum_eq_zero`, `pow_card_eq_of_powerSums`) force the deepest group to be all `P` points and a coset of the `1/P` lattice.
- **Visibility below threshold** `exists_visible_of_not_uniform_crystal`: any other shape is visible for all large `ℓ` at every `a > (P−1)ℓ/2` (strictly below `Pℓ/2`). **Partner** `uniform_crystal_hides`: the uniform crystal hides up to `Pℓ/2` at every scale (rotation lemma `powerSum_eq_zero_of_pow_eq`).
- Corpus link: same `2×2`-minor mechanism as `RHTower.norm_le_of_pair_form` (WeilLagCompressedToeplitzPositivity); here applied to zero-configuration lag symbols rather than the compressed ζ lag.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after CrystallineFragilityOfOffLineLattices.

### C11 — Hodge index on lag-lattice configurations (`HodgeIndexOnLagLatticeConfigurations.lean`)
- **Polar blindness** `hodgeIndex_iff_toeplitz_of_lagFormula`, `hodgeIndex_iff_weil_nonneg_of_lagFormula`: for any configuration with lag formula `W = ℓ Σ_m k(mℓ) D(m)`, `RHTower.HodgeIndexAtLevel Z a` ⟺ Toeplitz PSD of size `⌈2a/ℓ⌉` ⟺ full Weil positivity at aperture `a`. Witness: translates of the corpus polar-free bump `RHTower.scaledBumpPolarFree w 0` (`exists_polarFree_bump`; general complex-bump lag identity `lagSum_bumpTest_eq_toeplitz`).
- **Corpus sharpening** `offLineLattice_hodgeIndex_iff`: `HodgeIndexAtLevel (offLineLatticeConfig) a ⟺ a ≤ L/2` — exact form of the masking half of `RHTower.offLineLattice_masks_at_linear_level`.
- **Hodge Nyquist ceiling** `profileConfig_not_hodgeIndex_of_nyquist_lt`; **Hodge crystal rigidity** `hodgeIndex_frequently_iff_uniform_crystal` (iff); `exists_hodge_violation_of_not_uniform_crystal`; **Hodge jitter law** `jitterConfig_hodgeIndex_iff`.
- Meaning: the linear-level masking witness of `RHTower.not_forall_hodge_exclusion_sublinear_level` is crystalline; among fixed-shape periodic off-line patterns only the uniform crystal masks to the square-root threshold.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after CrystalRigidityAtTheSquareRootThreshold.

### C12 — On-line shadows: invisibility is mimicry (`OnLineShadowIndistinguishability.lean`)
- **Indistinguishability principle** `weil_nonneg_iff_onLineShadow_of_lagFormula`: a configuration with lag formula `W = ℓ Σ_m k(mℓ) D(m)`, Hermitian symbol, `D(0) = d₀ > 0`, is invisible at aperture `a` ⟺ there is a weighted on-line periodic configuration (`onLineShadow ℓ c w`, weights `w ≥ 0` at `c_k + 2πℤ/ℓ`) with `Σ w = d₀` zeros per period, `2⌈2a/ℓ⌉ − 1` ordinates per period, and `W(f,f) = Sh(f)` on every aperture-`a` test.
- Mechanism: Toeplitz PSD section → corpus Carathéodory–Fejér factorization `HTGeometry.exists_atomic_caratheodoryFejer_psd_factorization` (via `circleToeplitzGram_posSemidef`, `exists_atomic_lagSymbol`) → each atom `e^{iφ}` is the on-line translate `φ/ℓ + 2πℤ/ℓ` by Poisson (`lagSum_translate_eq_onLine`); kernel vanishes at lags `≥ 2a` (`weilTest_eq_zero_of_two_mul_le`).
- Corollaries: Hodge version `hodgeIndex_iff_onLineShadow_of_lagFormula`; profiles `profileConfig_weil_nonneg_iff_onLineShadow`; patterns `patternConfig_weil_nonneg_iff_onLineShadow`; `offLineLattice_onLineShadow` (one ordinate of weight 2 for `a ≤ L/2`).
- First use of the HTGeometry Carathéodory–Fejér development inside SRT.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after HodgeIndexOnLagLatticeConfigurations.
- README restructured (user request): foundational why/what/how, mechanisms grouped zero side / windows / prime side (incl. other agent's Kronecker, reality/mean-zero, minimum-aperture mechanisms), traps, open problems, principles.

### C13 — Weil ground state of lag-lattice configurations (`WeilGroundStateLawOnLagLattices.lean`)
- **Ground-state law** `weil_floor_iff_toeplitz_floor`, `hodge_floor_iff_toeplitz_floor`: for any `μ`, `Re W(f,f) ≥ ℓμ∫|f|²` on all aperture-`a` tests ⟺ same on the Hodge class ⟺ `Re T_D(c) ≥ μ‖c‖²` on the Toeplitz section of size `⌈2a/ℓ⌉`. Weil ground energy = `ℓ·λ_min`; the polar constraint does not raise it. Mechanism: shift symbol by `μ` at lag 0 (`shiftSymbol`, `lagSum_shiftSymbol`, field lemma `weilTest_self_zero`), lag-point bump mass `integral_norm_sq_bumpTest`.
- **Rank-two floor** `rankTwo_floor`, `rankTwo_floor_attained`: `2Re(A B̄) ≥ (⟨x,y⟩ − ‖x‖‖y‖)‖c‖²`, attained at `c = ‖y‖x − ‖x‖y` (Cauchy–Schwarz + polarization).
- **Off-line lattice ground energy** `offLineLattice_weil_floor`, `offLineLattice_hodge_floor_sharp`: exactly `L(n − √(S₊S₋))` (`latticeFloor`), `S_± = Σ_{j<n} e^{±2δjL}`, sharp within the Hodge class for `a > L/2`.
- **Depth-exponent growth** `latticeFloor_aperture_bounds`: `−(2a+L)e^{2δa} ≤ L·latticeFloor ≤ 2a + L − L e^{δ(2a−L)}`: ground energy decays like `−e^{2δa}` with exponent exactly the depth — exact model of the corpus floor-growth law `RHTower.XiRestrictedWeilFloorGrowthUniversalityLaw` (aperture exponent ≥ transverse depth off RH).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after OnLineShadowIndistinguishability.

### C14 — Nyquist pinning of on-line configurations (`OnLineNyquistPinning.lean`)
- **Moments** `onLineShadow_eq_lagSum`, `shadowMoment_eq_of_onLineShadow_eq`: `Sh(f) = ℓ Σ_m k(mℓ) M(m)`, `M(m) = Σ_k w_k e^{ic_k mℓ}`; agreement of two shadows on aperture-`a` tests ⟺ agreement of moments on `|m| < ⌈2a/ℓ⌉` (universal lag-point test `exists_bumpTest_universal`; vanishing Hermitian Toeplitz forms `eq_zero_of_toeplitzForm_eq_zero`).
- **Atomic pinning** `atomic_pinning`: `r` distinct unit nodes + any nonnegative atomic measure with equal moments for `|m| ≤ r` ⇒ same nodes, same weights. Mechanism: atomic Toeplitz form `= Σ w_i |P_c(z_i)|²` (`toeplitzForm_atomic`), vanishing polynomial `Π(z − z_k)` and Lagrange polynomials.
- **Nyquist pinning** `onLineShadow_pinning`: two weighted on-line periodic configurations, the first with `r` ordinates per period, agreeing on all tests of an aperture with `r < ⌈2a/ℓ⌉` ⇒ same ordinates and weights, and agreement at every aperture.
- **Sharpness** `onLineShadow_crystal_unpinned` (crystal vs half-step rotation agree for `⌈2a/ℓ⌉ ≤ r`), `exists_onLineShadow_crystal_distinguished` (told apart for `⌈2a/ℓ⌉ > r`).
- Meaning: position, like depth, is invisible below the Nyquist aperture and visible above — configuration-side counterpart of the corpus Landau-height Krein pinning for ζ (`RHTower.LandauHeightKreinPinning`).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after WeilGroundStateLawOnLagLattices.

### C15 — Relaxed Hodge exponent of off-line lattices (`RelaxedHodgeExponentOfOffLineLattices.lean`)
- Corpus interfaces `RHTower.RelaxedHodgeIndexAtLevel Z θ a` (`Re W ≥ −e^{θa}∫|f|²` on polar tests) and `RHTower.WeilFloorAtLevel Z a η` evaluated exactly for `offLineLatticeConfig`.
- **Exact floors** `offLineLattice_weilFloor_iff`, `offLineLattice_relaxedHodge_iff` (`a > L/2`): floor `η` holds iff `η ≥ L(√(S₊S₋) − n)`; relaxed index iff `e^{θa} ≥ L(√(S₊S₋) − n)`.
- **Exponent = 2δ** `offLineLattice_relaxedHodge_eventually_of_lt` (`θ > 2δ`: holds at all large levels, even for unconstrained tests), `offLineLattice_not_relaxedHodge_eventually_of_lt` (`θ < 2δ`: violated at all large levels by polar tests, any constant `C`).
- Meaning: the depth-exponent threshold of `RHTower.exists_relaxed_violation` is sharp without losses; the lattice also attains the exponent `2η` of `RHTower.re_W_ge_of_depth_offLineDensity` (remark, up to polynomial factor).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after OnLineNyquistPinning.

### C16 — Dilution: sparse off-line lattices in a dense on-line background (`DilutedOffLineLatticeHidingLaw.lean`)
- `dilutedLatticeConfig`: doubled on-line lattice `{½ + 2πik/L}` ∪ off-line lattice `{½ ± δ + 2πij/ℓ}`. Lag formula below the background Nyquist (`W_dilutedLatticeConfig`, tests in `[−L/2, L/2]`): symbol `2cosh(δmℓ) + (2L/ℓ)[m=0]` (background = pure diagonal mass; uses SRT `hasSum_Wsummand_onLineLattice` and new `hasSum_Wsummand_offLineLattice`).
- **Dilution law** `dilutedLattice_weil_nonneg_iff`, `dilutedLattice_hodgeIndex_iff` (`0 < a ≤ L/2`): invisible ⟺ Hodge index ⟺ `ℓ(√(S₊S₋) − n) ≤ 2L`, `n = ⌈2a/ℓ⌉`.
- **Hiding aperture logarithmic in density ratio** `dilutedLattice_weil_nonneg_of_le` (invisible if `(2a+ℓ)e^{2δa} ≤ 2L`), `dilutedLattice_not_hodgeIndex_of_lt` (Hodge-visible if `ℓe^{δ(2a−ℓ)} > 2L + 2a + ℓ`): hiding aperture `(1/2δ)log(L/ℓ)` + lower order. Interpolates isolated-pair law (`log(δL)/2δ`) and lattice law (`L/2`); fixed off-line density in ζ-density background hides only to `≍ (1/2δ)log log T`.
- C13 refactor: `toeplitz_floor_of_hodge_floor`, `weil_floor_of_toeplitz_floor` now need the lag formula only on aperture-`a` tests (C13, C15 oleans rebuilt).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after RelaxedHodgeExponentOfOffLineLattices.

### C17 — Rigidity of periodic depth profiles (`ProfileRigidityAtTheSquareRootThreshold.lean`)
- C10 core lemma `uniform_crystal_of_frequently_bounded_modes` generalized to depths `≥ 0` with one positive (C10–C16 oleans rebuilt).
- `profile_hides_frequently_iff_uniform`, `profile_hodge_frequently_iff_uniform`: a periodic depth profile (lattice ordinates, residues may be on-line) with an off-line residue hides / satisfies the Hodge index at some `a > (P−1)L/(2P)` for unboundedly many `L` ⟺ constant depth (converse: C4 uniform extremality up to `L/2`).
- `exists_visible_profile_of_not_uniform`: any profile mixing on-line and off-line residues, or with varying depth, is visible at every `a > (P−1)L/(2P)` for all large `L`.
- Axioms: [propext, Classical.choice, Quot.sound].

### C18 — Variational principle for crystals (`CrystalVariationalPrinciple.lean`)
- `exists_weil_le_diagonal`: every lag-lattice configuration has, at every aperture, a test with `Re W ≤ ℓ·Re D(0)·∫|f|²` (Toeplitz floor ≤ diagonal).
- `eq_zero_of_toeplitz_floor_diagonal`: Hermitian section with floor `Re D(0)` is diagonal (2×2 minors of `T − D(0)`).
- `crystal_iff_weil_floor_diagonal`, `crystal_iff_hodge_floor_diagonal`: at uniform depth, every scale `ℓ` and every `a ∈ ((P−1)ℓ/2, Pℓ/2]`, the maximal floor `Re W ≥ 2Pℓ∫|f|²` (on-line value) holds iff crystal. Non-asymptotic counterpart of C10.
- Axioms: [propext, Classical.choice, Quot.sound].

### C19 — Optimality of the depth exponent in the corpus depth–density bound (`DepthDensityLowerBoundExponentOptimality.lean`)
- `offLineLatticeConfig_offLineDensityBound`: the off-line lattice satisfies corpus `RHTower.OffLineDensityBound` with `D = L/π + 2`; `offLineLatticeConfig_depth`: depth exactly `δ`.
- `depthDensity_exponent_optimal`: for every `δ`, `θ < 2δ`, `C > 0` there is a configuration of depth `δ` and density `≤ 1/π + 2` with, at all large `a`, a polar test `Re W < −C e^{θa}∫|f|²` — the exponent `2η` of `RHTower.re_W_ge_of_depth_offLineDensity` cannot be lowered.
- Axioms: [propext, Classical.choice, Quot.sound]. All three wired after DilutedOffLineLatticeHidingLaw.

### C20 — Relaxed Hodge exponent of periodic configurations = 2 × maximal depth (`RelaxedHodgeExponentOfPeriodicConfigurations.lean`)
- Abstract `CoshSymbolData`: Hermitian symbol `D(m) = Σ_r 2cosh(d_r mℓ) z_r^m`, distinct unit nodes, depths `≥ 0`, one positive.
- `eq_zero_of_moments_eq_zero` (Lagrange), `exists_powerSum_window_lower` (compactness of the torus): power sums of distinct unit nodes are `≥ c > 0` somewhere in every window of `|ι|` consecutive exponents.
- `toeplitz_floor_eventually_of_gt` (Gershgorin: floor `≥ −4P(2a+ℓ)e^{2d_max a}`), `not_toeplitz_floor_eventually_of_lt` (deepest nodes dominate a mode in `[n−P, n)`; 2×2 minor `floor_le_diagonal_sub_mode`).
- Corpus language: `patternConfig_relaxedHodge_eventually_of_lt` / `patternConfig_not_relaxedHodge_eventually_of_lt` and `profileConfig_…` versions: `RHTower.RelaxedHodgeIndexAtLevel` holds at all large levels for `θ > 2d_max` (even unconstrained tests), fails at all large levels for `θ < 2d_max` (polar tests, any constant). Generalizes C15 from the lattice to every periodic pattern/profile: the relaxed exponent reads off exactly the maximal depth.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after DepthDensityLowerBoundExponentOptimality.

### C21 — Depth tomography at twice the Nyquist aperture (`DepthTomographyAtTwiceNyquist.lean`)
- `symbol_eq_of_weil_eq`: two lag-lattice configurations (same `ℓ`) agreeing on aperture-`a` tests have equal symbols on `|m| < ⌈2a/ℓ⌉`.
- `card_fiber_eq_of_moments_eq`: two families of nonzero complex numbers, total size `≤ 2N+1`, with equal two-sided moments on `|m| ≤ N`, take every value equally often (shift by `N` + Lagrange).
- `patternSymbol_eq_nodes`: `D(m) = Σ_r (λ_r^m + μ_r^m)`, `λ_r = e^{d_rℓ+2πiθ_r}`, `μ_r = e^{−d_rℓ+2πiθ_r}`.
- **Tomography** `depthTomography`: patterns with `P`, `P'` pairs agreeing on all tests of an aperture with `⌈2a/ℓ⌉ ≥ P+P'+1` have the same (depth, ordinate class) pairs (outer nodes `|λ| > 1` carry them). For `P'=P`: aperture `Pℓ` = twice Nyquist.
- **Partner** `crystal_weil_eq_below_nyquist`: uniform crystals of any two depths have identical Weil forms on tests of aperture `≤ Pℓ/2` — depth unreadable below Nyquist. Tomography threshold lies in `[Nyquist, 2×Nyquist]`.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after RelaxedHodgeExponentOfPeriodicConfigurations.

### C22 — Sampling by on-line configurations stops exactly at Nyquist (`OnLineSamplingAtTheNyquistAperture.lean`)
- `atomic_form_pos`, `exists_atomic_floor`: for `n ≤ r` distinct nodes, `Σ_k w_k|P_c(z_k)|² ≥ A₀‖c‖²`, `A₀ > 0` (polynomial of degree `< r` vanishing at `r` points is zero; compactness of the unit sphere).
- **Sampling law** `onLineShadow_sampling_iff`: a weighted on-line periodic configuration (positive weights, `r` distinct ordinates per period `2π/ℓ`) satisfies `Sh(f) ≥ A∫|f|²` with `A > 0` on all aperture-`a` tests ⟺ `⌈2a/ℓ⌉ ≤ r`. Above Nyquist the vanishing polynomial `Π(z − z_k)` gives a lag-point test with positive mass and zero shadow.
- Corpus link: exact, model-level form of the Beurling–Landau sampling premise of `RHTower.NyquistDichotomy` (`sampling_forces_mass`): critical zeros contribute mass against an off-line pair exactly below the Nyquist aperture of their ordinates, and can be dodged above it.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after DepthTomographyAtTwiceNyquist.

### C23 — Crystallization hides off-line zeros: visibility is not monotone (`CrystallizationHidesOffLineZeros.lean`)
- `twoMode_visible`: lag-lattice configuration with `|D(1)| > Re D(0)` is visible at every `a ∈ (ℓ/2, ℓ]`.
- `exists_offLine_superset_hiding`: off-line lattice `Z = {½±δ+2πij/L}` ⊆ two-point uniform crystal `Z'` (add half-step translate), all zeros off-line and simple; at every `a ∈ (L/2, L]`, `Z` is visible and `Z'` invisible. Adding off-line zeros can hide; positivity is collective (counterpart of dilution C16 for on-line additions).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after OnLineSamplingAtTheNyquistAperture.

### C24 — Two-bump lag-structure law for arbitrary tempered configurations (`TwoBumpLagStructureLaw.lean`)
- `lagStructure Z β v = Σ_ρ m_ρ h_{k_β}(γ_ρ) e^{iγ_ρ v}` (smeared lag structure; for on-line zeros the bump-smeared structure factor of the ordinates); `summable_lagStructure` for `TemperedConfig` via corpus decay `RHTower.norm_paperFT_le_decay`.
- `W_twoBump`: for `f = β(t+v/2) + τβ(t−v/2)`, `W(f,f) = (1+|τ|²)S(0) + τS(v) + τ̄S(−v)` — no periodicity.
- `norm_lagStructure_le_of_weil_nonneg`: invisible at `a` ⇒ `|S(v) + conj S(−v)| ≤ 2Re S(0)` for `0 ≤ v ≤ 2(a−w)`; `exists_visible_of_lagStructure`: any violation is a two-bump visibility witness at aperture `v/2 + w`.
- First general (aperiodic) visibility tool of the field: open problem 2 reduces to a scalar inequality on the smeared lag structure.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after CrystallizationHidesOffLineZeros.

### C25 — Ground energy of the off-line lattice: closed form and step law (`LatticeGroundEnergyStepLaw.lean`)
- `sqrt_latticeSums_eq`, `latticeFloor_eq`: `√(S₊S₋) = sinh(nδL)/sinh(δL)` (centred sum, telescoping `two_sinh_mul_centredSum`), so the ground energy at aperture in `((n−1)L/2, nL/2]`, `n ≥ 2`, is `L(n − U_{n−1}(cosh δL))`.
- `latticeFloor_succ_lt`: strictly decreasing in `n` (`sinh((n+1)u) − sinh(nu) > sinh u`).
- `offLineLattice_ground_energy_drops`: floor `μ_n` at `a = nL/2`, polar tests below fixed `μ' < μ_n` at every `a ∈ (nL/2, (n+1)L/2]` — ground energy is a strictly decreasing step function, right-discontinuous at every `nL/2` (contrast: corpus continuity `RHTower.tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture` for ζ's restricted operator).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after TwoBumpLagStructureLaw.

### C26 — Isolated off-line pair in an arbitrary on-line background (`IsolatedPairInArbitraryBackground.lean`)
- `onLineMass Z β γ₀ = Σ_{on-line} m_ρ|h_β(γ_ρ − γ₀)|²` (local on-line mass seen by the bump at height `γ₀`); `modBump` (bump modulated to height `γ₀`, corpus `RHTower.paperFT_modulate`).
- `onLine_summand`: on-line summands of the modulated lag structure are positive multiples of unimodular phases ⇒ background lag terms bounded by background mass at lag 0. `pair_summand`, `pair_lag_identity`: pair contributes `2e^{iγ₀v}(Qe^{δv} + Q̄e^{−δv})`, `Q = h_β(−iδ)conj h_β(iδ)`.
- **`isolatedPair_visible`**: tempered `Z`, all zeros on the line except one simple pair `½±δ+iγ₀`; if `|h_β(−iδ)||h_β(iδ)|(sinh δv − 1) > M`, then visible at aperture `v/2 + w` (two-bump test, C24). Visibility aperture `≈ (1/2δ)log(M/|Q|)` — logarithmic in the local zero count for ANY arrangement of on-line zeros (`≍ (1/2δ) log log T` at ζ-density). Generalizes the lattice isolated-pair law to arbitrary backgrounds.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after LatticeGroundEnergyStepLaw.
- (C26 refactor) core now general in the bump: `isolatedPair_lagStructure_gt` (any `b`, `pairWeight`, `onLineMassOf`); `isolatedPair_visible` is the modulated corollary.

### C27 — An isolated off-line pair violates the Hodge index at a logarithmic level (`IsolatedPairHodgeViolation.lean`)
- `paperFT_twoBump_eq_zero`: two-bump tests vanish wherever the profile transform does ⇒ polar-free profile gives Hodge-class tests.
- `norm_lagStructure_le_of_twoBump_nonneg`: the two-point minor from two-bump tests alone.
- **`isolatedPair_not_hodgeIndex`**: with the corpus polar-free modulated bump `RHTower.scaledBumpPolarFree w γ₀`, tempered `Z` with all zeros on the line except one simple pair `½±δ+iγ₀`, `|Q_b|(sinh δv − 1) > M_b` ⇒ `¬ RHTower.HodgeIndexAtLevel Z a` for all `a ≥ v/2 + w`. Level `≈ (1/2δ)log(M_b/|Q_b|)`, logarithmic in local on-line mass for any on-line arrangement; contrast `RHTower.not_hodgeIndex_below_cluster_horizon` (linear in window count, but robust to clusters).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after IsolatedPairInArbitraryBackground.

### C28 — Equal-depth clusters in an arbitrary on-line background (`EqualDepthClusterInArbitraryBackground.lean`)
- Addresses open problem 2 (clusters without a depth gap) in its extreme case: `n` simple pairs `½±δ+iγ_k`, one common depth, arbitrary tempered on-line background.
- `exists_weighted_powerSum_window_lower`: distinct unit nodes, nonzero weights ⇒ `∃ c > 0`, every window of `n` consecutive exponents has `|Σ q_r z_r^m| ≥ c` (compactness on the torus + Vandermonde).
- `equalDepthCluster_lagStructure_gt`: `e^{δv}|Σ Q_k e^{iγ_k v}| > 2M_b + 3Σ|Q_k|` ⇒ two-point minor fails at lag `v`.
- **`equalDepthCluster_visible`**: lag grid `ℓ` separating heights, nonzero `Q_k` ⇒ visible at every `a ≥ (1/2δ)log⁺((2M_b+3Σ|Q_k|)/c) + (n+2)ℓ/2 + w`. Mutual cancellation among equal-depth pairs costs only `(n+2)ℓ/2` and the constant `1/c`; aperture stays logarithmic in on-line mass.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after IsolatedPairHodgeViolation.

### C29 — Finite off-line sets are visible at a logarithmic aperture (`FiniteOffLineSetsAreVisible.lean`)
- `lagTerm`, `offLineWeight` (`q_t = m_t h_b(γ_t − iδ_t) conj h_b(γ_t + iδ_t)`), `pair_lagTerm` (any multiplicity, via `mult_reflect`), `lagStructure_split` (on-line tsum + finite pair sum over `T = carrier ∩ {Re > ½}`), `onLinePart_bounds`.
- `finiteOffLine_lagStructure_gt`: `|Σ_T q_t e^{δ_t v}e^{iγ_t v}| > 2M_b + 3Σ|q_t|` ⇒ two-point minor fails. Generalizes C26/C28 to arbitrary depths and multiplicities.
- `pairWeight_modScaledBump_ne_zero`: corpus bump `κ_w` modulated to `γ₀` has nonzero weight at the pair at `γ₀` (via `RHTower.norm_paperFT_scaledBump_I_mul_ge`).
- **`finiteOffLine_visible`**: for `T`, multiplicities `m`, top point `t₀`, gap `g ∈ (0, D]`: `∃ c ℓ > 0` (depending only on `T, m, w`) such that EVERY tempered `Z` with right-off-line zeros exactly `T` (mult `m`) is visible at all `a ≥ (1/2g)log⁺((2M_b+4Σ|q_t|)/c) + (|T|+2)ℓ/2 + w`. Uniform in the on-line background; background enters only via `log M_b`.
- **`exists_weil_neg_of_finite_offLine`**: tempered `Z`, off-line set finite and nonempty ⇒ `∃ f` C², compact support, `Re W(f,f) < 0`. No hypotheses on the on-line zeros. (Corpus analogue for ξ only via global lag function: `RHTower.exists_pow_integerLag_gt_of_finite_offLine`.)
- README: mechanism 9 extended; open problem 2 refined to "depths accumulating at the top (no gap)".
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after EqualDepthClusterInArbitraryBackground.
- (C29 refactor) core now `finiteOffLine_minor_fails` (any bump `b` with `q_{t₀} ≠ 0`, gap required only at nonzero-weight points, conclusion = failed minor at lag `v`, `v/2 + w ≤ a`); `finiteOffLine_visible` uses corpus `RHTower.modScaledBump` (removed local duplicates `contDiff_modScaledBump`/`modScaledBump_support`). C27 gained `not_hodgeIndex_of_polarFree_minor` (factored out of `isolatedPair_not_hodgeIndex`). C27–C29 oleans rebuilt.

### C30 — Weil/Hodge classification for finite off-line sets (`HodgeClassificationOfFiniteOffLineSets.lean`)
- `weil_nonneg_of_onLine`: all zeros on line ⇒ `Re W(f,f) ≥ 0` for EVERY `f`, no growth hypothesis (summable or tsum = 0).
- `hodgeIndex_of_onLine_or_poles`: zeros on line or at `0, 1` ⇒ Hodge index at every level (`gammaOf 0 = i/2`, `gammaOf 1 = −i/2`, Hodge tests vanish there).
- `pairWeight_polarFree_ne_zero` (polar factor `(γ∓iD)²+¼ = 0` only for the zero `1`), `offLineWeight_polarFree_one = 0`.
- **`finiteOffLine_not_hodgeIndex`**: uniform-in-background Hodge violation at level `(1/2g)log⁺((2M+4Σ|q|)/c) + (|T|+2)ℓ/2 + w` with the polar-free modulated bump; `t₀ ≠ 1`, gap among `T \ {1}`.
- **`hodgeIndex_forall_iff_of_finite_offLine`**: tempered, finite off-line set ⇒ (Hodge index at all levels ⟺ every off-line zero ∈ {0, 1}).
- **`weil_nonneg_iff_onLine_of_finite_offLine`**: tempered, finite off-line set ⇒ (Weil positivity on C² compactly supported tests ⟺ all zeros on the line).
- README: mechanism 12 extended (Hodge blind exactly at 0, 1; classification); new trap row.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after FiniteOffLineSetsAreVisible.

### C31 — An attained maximal depth is always visible (`AttainedDepthIsVisible.lean`)
- `rightZeros Z`, `carrier_countable` (unit height windows finite), `summable_indicator_of_subset`, `lagTerm_eq_weight` (`lagTerm = q_t e^{δ_t v} e^{iγ_t v}`).
- `lagStructure_split_right`: S(v) = on-line part + absolutely convergent Σ' over right zeros of pair terms (indicator decomposition + reflection involution `Function.Involutive.toPerm`).
- `rightZeros_lagStructure_gt`: infinite-set lag criterion `‖Σ' q e^{δv}e^{iγv}‖ > 2M + 3Σ'‖q‖` ⇒ minor fails.
- `norm_geom_mean_le`, `tendsto_geom_mean` (Cesàro means of `w^k`, `|w| ≤ 1`, `w ≠ 1` → 0).
- **`attainedDepth_visible`**: tempered `Z`, zero `t₀` with `Re t₀ > ½` and `Re ρ ≤ Re t₀` ∀ρ ⇒ `∃ f` C² compact support, `Re W(f,f) < 0`. NO gap, NO finiteness. Proof: invisibility ⇒ off-line sum bounded; normalize by `e^{−(D+iγ₀)kℓ}` → `Σ' q_t w_t^k → 0`; Cesàro + dominated convergence → `q_{t₀}`; grid `ℓ` avoids countably many resonances (measure-zero argument); `q_{t₀} ≠ 0` by modulated `κ`.
- **`exists_re_gt_of_weil_nonneg`**: Weil positivity on C² compactly supported tests ⇒ every zero right of the line is exceeded in real part by another zero (sup not attained). Matches corpus ξ boundary (`RHTower.exists_pow_integerLag_gt_of_attainedTop`), now for arbitrary tempered configurations at finite aperture.
- README: mechanism 9 extended; open problem 2 now: aperture for attained-depth accumulation + whether non-attained sup can hide.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after HodgeClassificationOfFiniteOffLineSets.

### C32 — A bounded exponential sum has no top pole (`BoundedExponentialSumsHaveNoTopPole.lean`)
- Pure analysis: `F(v) = Σ_t q_t e^{λ_t v}`, `Σ|q_t| < ∞`, `0 < Re λ_t ≤ A`, `F` bounded on `[0,∞)` ⇒ `q_{t₁} = 0` for every `t₁` rightmost on its horizontal line, not shared, `η`-separated from other lines. No attained supremum needed.
- `expSumProfile` (Mellin profile `x ↦ Σ q_t x^{−λ_t}` on `(0,1]`), `continuousOn_profileSum`, `differentiableAt_mellin_expSumProfile` (Laplace = Mellin, holomorphic on `Re s > 0` via `mellin_differentiableAt_of_isBigO_rpow`), `integral_Ioc_cpow`, `mellin_expSumProfile_eq` (= `Σ q_t/(s − λ_t)` for `Re s > A`, via `integral_tsum_of_summable_integral_norm`), `differentiableOn_resolventSum` (pole-free strip), **`eq_zero_of_norm_tsum_exp_le`** (identity theorem on convex strip + residue limit along `σ ↓ Re λ_{t₁}`).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after AttainedDepthIsVisible.

### C33 — Every off-line zero is visible; Weil and Hodge criteria for configurations (`WeilPositivityForcesTheCriticalLine.lean`)
- `exists_sep_height` (local finiteness separates heights), `exists_top_at_height` (rightmost zero at a height in a predicate-cut family), `exists_minor_fails_of_top` (top zero with nonzero weight ⇒ some two-point minor fails; via C32 on the subtype of nonzero weights), `exists_rightZero_of_offLine`.
- **`offLine_visible`**: tempered `Z`, any zero with `Re ≠ ½` ⇒ `∃ f` C² compact support `Re W(f,f) < 0`. No finiteness, no attained sup.
- **`weil_nonneg_iff_onLine`**: tempered `Z`: zero-side Weil positivity on C² compactly supported tests ⟺ all zeros on the critical line.
- **`offLine_not_hodgeIndex`**, **`hodgeIndex_forall_iff`**: Hodge index at all levels ⟺ every zero on the line or at `0, 1` (polar-free bump; weight vanishes only at the zero `1`).
- **`zeta_weil_nonneg_iff_onLine`**, **`zeta_hodgeIndex_forall_iff_onLine`**: for `zetaZeroConfig` (tempered by `temperedConfig_zetaZeroConfig`): RH ⟺ zero-side Weil positivity ⟺ Hodge index at every level.
- Superseded and removed (nothing stale): C29 `exists_weil_neg_of_finite_offLine`; C30 `exists_rightOffLine_finset`, `hodgeIndex_forall_iff_of_finite_offLine`, `weil_nonneg_iff_onLine_of_finite_offLine`; C31 `exists_re_gt_of_weil_nonneg`. C29–C33 oleans rebuilt (0 messages each).
- README: mechanism 9 (Laplace continuation), 12 (Hodge criterion general), open problem 2 (only aperture size remains open), new trap row.
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after BoundedExponentialSumsHaveNoTopPole.
- (C27 strengthened) `norm_lagStructure_le_of_twoBump_nonneg` now needs positivity only for unimodular `τ` (`|τ| = 1`; X = 0 case via τ = 1). (C33 refactor) `exists_minor_fails_modScaledBump`, `exists_minor_fails_polarFree` + helpers `contDiff_modScaledBump_two`, `modScaledBump_support`, `scaledBumpPolarFree_support`, `paperFT_scaledBumpPolarFree_half`; `offLine_visible`, `offLine_not_hodgeIndex` now one-liners on them. C27–C33 rebuilt (0 messages each).

### C34 — Unimodular two-bump tests decide the critical line (`UnimodularTwoBumpTestsDecideTheCriticalLine.lean`)
- **`onLine_iff_twoBump_nonneg`**: tempered `Z`: `Re W ≥ 0` on every `κ_γ(t+v/2) + τκ_γ(t−v/2)` (`γ ∈ ℝ`, `v ≥ 0`, `|τ| = 1`; κ = corpus `modScaledBump 1 γ`) ⟺ all zeros on the line. Three real parameters suffice.
- **`onLine_or_poles_iff_polarFree_twoBump_nonneg`**: same with polar-free bump (Hodge class) ⟺ every zero on line or at 0, 1.
- **`zeta_onLine_iff_twoBump_nonneg`**: RH ⟺ unimodular two-bump positivity of the zero-side Weil form of ζ.
- README mechanism 9: one sentence. Axioms: [propext, Classical.choice, Quot.sound]. Wired after WeilPositivityForcesTheCriticalLine.

### C35 — The Weil form determines the configuration (`WeilFormDeterminesTheConfiguration.lean`)
- `multDiff` (signed multiplicity `m_Z − m_{Z'}`), `coefTerm` (lag summand with arbitrary coefficient), `multDiff_reflect`, `conj_multDiff`, `coefTerm_eq_weight`, `coefTerm_reflect_eq_weight`, `coefTerm_onLine`, `lagStructure_sub_eq`, `lagStructure_eq_of_weil_twoBump_eq` (polarization at τ = 0, 1, i), `tsum_split_reflect` (generic on-line + reflected-pair split over ℂ).
- `multDiff_eq_zero_of_right` (bounded right sum ⇒ C32 kills the top nonzero coefficient on each line), `multDiff_eq_zero_of_offLine`, `multDiff_eq_zero_of_onLine` (Cesàro extraction on a non-resonant grid), `hasCompactSupport_twoBump`.
- **`eq_of_weil_twoBump_eq`**: tempered `Z, Z'` agreeing on all modulated two-bump tests ⇒ same carrier and same multiplicities. **`eq_of_weil_eq`**: same on all C² compactly supported tests ⇒ equal configurations. The zero-side Weil form is spectrally faithful.
- README: new mechanism 10 "Faithfulness" (later items renumbered; references updated: height phase now mechanism 18).
- Axioms: [propext, Classical.choice, Quot.sound]. Wired after UnimodularTwoBumpTestsDecideTheCriticalLine.
- (C35 refactor) `lagStructure_eq_of_weil_twoBump_eq_at` (pointwise polarization, both `±v`), `eq_of_multDiff_eq_zero` factored out. C35 rebuilt.

### C36 — Resolution of the Weil form at a finite aperture (`NyquistResolutionOfTheWeilForm.lean`)
- **`eq_of_weil_eq_of_separated`**: tempered on-line `Z, Z'`, union heights `g`-separated, Weil forms equal on all C² tests in `[−a, a]` with `a > 13/g` ⇒ `Z = Z'` (carrier + multiplicities). Proof: two-bump polarization on lags `|v| ≤ V`, signed sum vanishes on `[−V,V]`, finite truncation with small tail, corpus Montgomery–Vaughan interval bound `HTGeometry.interval_integral_normSq_expSum_ge` (constant 26/(πD) = 52/g).
- `simpleHalfLatticeConfig` (simple on-line lattice of spacing π/L), `temperedConfig_simpleHalfLatticeConfig`, `W_simpleHalfLatticeConfig` (= 2L⟨f,g⟩ below aperture L).
- **`lattice_resolution_sharp`**: corpus double lattice `onLineLatticeConfig` (spacing 2π/L, mult 2) and simple half lattice are distinct, on-line, tempered, union π/L-separated, equal Weil forms on all tests in `[−L/2, L/2]`. ⇒ resolution aperture of a g-separated union ∈ [π/(2g), 13/g].
- README mechanism 10 extended. Axioms: [propext, Classical.choice, Quot.sound]. Wired after WeilFormDeterminesTheConfiguration.

### C37 — Ingham's inequality for separated real spectra (`InghamInequalityForSeparatedSpectra.lean`)
- `integral_exp_I_mul_symm`, `inghamKernel` (`∫_{−T}^{T} cos(πt/2T) e^{ixt}`), `inghamKernel_eq` (closed form `cos(xT)(1/(x+a) − 1/(x−a))`, `a = π/2T`), `inghamKernel_zero` (`4T/π`), `norm_inghamKernel_le` (`2a/(x²−a²)`), `integral_cos_mul_normSq_expSum` (weighted mean square = Re of kernel quadratic form), `hasSum_two_div_four_sq_sub_one` (telescoping `Σ 2/(4n²−1) = 1`), `tsum_two_div_sq_sub_one_lt_one` (`b > 2`), `sum_side_le_tsum`, `sum_offDiag_le_two_tsum` (n-th neighbour at ≥ ng), `inghamConst`, `inghamConst_pos` (`Tg > π`), **`ingham_inequality`**: `C(T,g) Σ|c_j|² ≤ ∫_{−T}^{T} |Σ c_j e^{iγ_j t}|²` for g-separated γ, `Tg > π`.
- Proof is elementary (no cot series): the exact threshold comes from the telescoping sum.
- (C36 upgraded, nothing stale) `eq_of_weil_eq_of_separated` now uses Ingham: threshold `a > π/(2g)` (was `13/g` via Montgomery–Vaughan; MV import and `mvExp_div_two_pi` removed). With `lattice_resolution_sharp` (equality at `a = π/(2g)`), the resolution aperture of g-separated on-line configurations is EXACTLY `π/(2g)`.
- README mechanism 10 updated. Axioms: [propext, Classical.choice, Quot.sound]. Umbrella: Ingham before NyquistResolution.

### C38 — A prime-side criterion on a three-parameter family (`PrimeSideTwoBumpCriterion.lean`)
- `zeta_W_eq_literatureRHS`: `W_ζ(f,f) = EF.literatureRHS (f ⋆ f̃)` for `f ∈ C_c²` (via unconditional `Zeta23.WeilEF.EF_lit_zetaZeroConfig`).
- **`onLine_iff_primeSide_twoBump_nonneg`**: all nontrivial zeros of ζ on the line ⟺ `Re P(f⋆f̃) ≥ 0` for `f = κ_γ(t+v/2) + τκ_γ(t−v/2)`, `γ ∈ ℝ`, `v ≥ 0`, `|τ| = 1` (P = pole terms − Σ Λ(n)/√n (k(log n)+k(−log n)) + archimedean). Weil's criterion cut to three real parameters.
- **`onLine_iff_primeSide_polarFree_twoBump_nonneg`**: Hodge-class version (pole terms vanish); uses ζ has no zeros at 0, 1.
- README: new mechanism 21 (lag v sees exactly primes n ≤ e^{v+2w}). Axioms: [propext, Classical.choice, Quot.sound]. Wired after NyquistResolutionOfTheWeilForm.

### C39 — The three-parameter criterion for Dirichlet L-functions (`DirichletLFunctionTwoBumpCriterion.lean`)
- `temperedConfig_LZeros` (primitive χ mod q > 1; from `ThmE.localCountChi` + `WeilEF.zero_sum_inv_sq_gen`), `LZeros_W_eq_literatureRHSchi` (from unconditional `ThmE.EF_lit_chi_L`).
- **`grh_iff_weil_nonneg`**, **`grh_iff_primeSide_twoBump_nonneg`**, **`grh_iff_primeSide_polarFree_twoBump_nonneg`**: GRH for L(s,χ) ⟺ zero-side Weil positivity ⟺ twisted prime-side positivity on unimodular two-bump tests (also Hodge class).
- README mechanism 21: one sentence. Axioms: [propext, Classical.choice, Quot.sound]. Wired after PrimeSideTwoBumpCriterion.

### C40 — The growth rate of an exponential sum is the abscissa of its top poles (`ExponentialGrowthRateOfExponentialSums.lean`)
- **`eq_zero_of_norm_tsum_exp_le_exp`**: `Σ|q_t| < ∞`, `Re λ_t ≤ A`, `|Σ q_t e^{λ_t v}| ≤ K e^{σv}` on `v ≥ 0` ⇒ `q_{t₁} = 0` for every line-top, separated, unshared `t₁` with `Re λ_{t₁} > σ`. Reduced to C32 by splitting off `Re λ ≤ σ` and shifting by σ. Module now imported directly after C32; C33 imports it.

### C41 — The negativity rate of two-bump tests equals the maximal depth (`NegativityRateEqualsMaximalDepth.lean`)
- Refactors: C31 `rightZeros_minor_bounds` (two-sided bounds of `|S(v)+conj S(−v)|` by `2|A(v)| ± (2Σ|q|+2M)`, `|Re S(0) − M| ≤ 2Σ|q|`; `rightZeros_lagStructure_gt` now a 3-line corollary). C33 `exists_minor_gt_of_top` (growth version via C40: `|X(v)| > 2Re S(0) + K e^{σv}` for some v, any K, `0 ≤ σ < depth(t₀)`); `exists_minor_fails_of_top` is its σ = K = 0 corollary. C31–C39 rebuilt (0 messages each).
- `minorDeficit Z b v := 2 Re S(0) − |S(v) + conj S(−v)|`; `re_W_unit_twoBump`, `minorDeficit_le_re_W`, `exists_unit_re_W_eq_minorDeficit` (= min of Re W over unimodular two-bump tests, attained).
- **`minorDeficit_ge`**: all depths ≤ D ⇒ `μ(v) ≥ −C e^{Dv}`. **`exists_minorDeficit_lt`**: a zero of depth > σ ≥ 0 ⇒ ∀K ∃ height, lag with `μ(v) < −K e^{σv}`. Exact negativity rate = sup depth.
- **`zeta_primeSide_twoBump_ge`**, **`zeta_exists_primeSide_twoBump_lt`**: prime-side version for ζ: at lag log X, min Re P ≥ −C X^{D} if all Re ρ ≤ ½ + D; not O(X^σ) for σ below any depth. RH ⟺ no power growth (square-root threshold).
- README mechanisms 9, 21 extended. Axioms: [propext, Classical.choice, Quot.sound]. Wired after DirichletLFunctionTwoBumpCriterion.

### C42 — Weil positivity of ζ below aperture 1/100 (`ZetaWeilPositivityBelowApertureOneHundredth.lean`)
- `re_digamma_quarter_ge_log` (`Re ψ(¼+iτ/2) ≥ log(|τ|/2) − 6/|τ|`, `|τ| ≥ 4`), `mu_eq_re_digamma`, `mu_ge_log_abs`, `mu_ge_neg` (`μ ≥ −(7+log π)/2π`), three-band constants `muHigh/muMid/muLow`, `integral_norm_sq_paperFT_mul_mu_ge_three_band` (spectral mass of `[−R,R]` ≤ `4aR‖f‖²`), `pairEnergy_half_le_sq`.
- **`zetaZeroConfig_re_W_ge_of_aperture_le_hundredth`**: `(1/25)‖f‖² ≤ Re W_ζ(f,f)` for every C² test supported in `[−a,a]`, `0 < a ≤ 1/100` (was `e^{−50}`). `zetaZeroConfig_re_W_nonneg_of_aperture_le_hundredth`, `re_windowedW_zetaZeroConfig_nonneg_of_hundredth` (height windows of aperture 1/100).
- Import narrowed to `ZetaSmallApertureHeightWindowPositivity`. README open problem 3 updated. Axioms: [propext, Classical.choice, Quot.sound]. Wired after NegativityRateEqualsMaximalDepth.

### C43 — Large dyadic prime windows decide the critical line (`LargeDyadicPrimeWindowsDecideTheCriticalLine.lean`)
- **`exists_minor_gt_of_top_of_ge`**, **`exists_minorDeficit_lt_of_ge`** (any bump width w > 0): tail visibility — minor excess `> K e^{σv}` at some lag `v ≥ V`, every K, V. Proof: a priori bound on `[0,V]` from `minorDeficit_ge` with D = ½, then C33 with an enlarged K (no upstream edit).
- **`onLine_iff_twoBump_nonneg_of_ge`**: for every V, tempered config on the line ⟺ Weil ≥ 0 on unimodular two-bump tests with lag `v ≥ V`.
- `twoBump_apply`, **`weilTest_twoBump_eq_zero`** (kernel vanishes off `[−2w,2w] ∪ ±[v−2w,v+2w]`), `lagPrimeWindow v w` (`|log n − v| ≤ 2w`), `vonMangoldt_eq_zero_or_weilTest_twoBump_eq_zero`, `tsum_vonMangoldt_twoBump_eq_window` (twisted prime tsum = finite window sum for `2w < log 2`, v ≥ 0).
- `lagPrimeWindowRHS`, `lagPrimeWindowRHSchi`, `literatureRHS_twoBump_eq_lagPrimeWindowRHS`. **`onLine_iff_primeWindow_nonneg`**: RH ⟺ window functional ≥ 0 at every height, every lag `v ≥ V` (any V ≥ 0), `|τ| = 1`; each test reads Λ only on one dyadic window ⊂ (X/2, 2X), X = e^v. **`zeta_exists_primeWindow_lt`**: off-line zero of depth > σ ⇒ window functional `< −K e^{σv}` beyond every V. **`grh_iff_primeWindow_nonneg`**: same for primitive Dirichlet L.
- README mechanism 21 rewritten (kernel support, tail law, finite prime data irrelevant), new trap. Axioms: [propext, Classical.choice, Quot.sound]. Wired after C42.

### C44 — The sharp archimedean horizon of the symbol of ζ (`SharpArchimedeanHorizonOfTheZetaSymbol.lean`)
- Solves README open problem 3 (second half): horizon `68√X` → `(4+ε)√X`, coefficient optimal.
- `sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt`; **`exists_sum_vonMangoldt_div_sqrt_le`** (`Σ_{n≤X} Λ(n)/√n ≤ (2+ε)√X + C_ε`, from corpus PNT asymptotic `RHTower.FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt` + Chebyshev `34√N` below the threshold).
- **`exists_PX_ge`** (`P_X ≥ −((2+ε)√X + C)/π`, uniform in τ), **`exists_mu_add_PX_ge`** (sharp horizon `μ + P_X ≥ (log(1+|τ|/4) − C − (4+ε)√X)/2π`), `PX_zero`, **`not_exists_PX_ge_of_lt_two`** (no height-uniform bound with coefficient c < 2: optimal).
- `zetaZeroConfig_re_W_heightShift_ge_of_symbol` (single-height lower bound from any symbol bound E; the corpus theorem is the E = 10 + 68√X instance), **`exists_sharp_zetaZeroConfig_re_W_heightShift_ge`**, **`zetaZeroConfig_re_W_heightShift_nonneg_of_horizon`**: localized ζ forms positive once `C + (4+ε)e^a + 2S(a) + 1 ≤ log(1 + π|ξ|/4)` (√X ≤ (¼ − ε) log T).
- README open problem 3 rewritten. Axioms: [propext, Classical.choice, Quot.sound]. Wired after C43.

### C45 — The depth-deficit transform replaces the gap (`DepthDeficitTransformReplacesTheGap.lean`)
- Open problem 2 (part): quantitative visibility of an attained top depth with finitely many top-level heights, no gap required (shallower zeros may accumulate at the top; infinitely many off-line zeros allowed).
- `exists_level_window_lower` (window lower bound for one level, standalone form of the C29 grid argument), `depthDeficit Z b r v = Σ_{Re t<r} |q_t| e^{(Re t − r)v}`, `summable_norm_offLineWeight`, `depthDeficit_term_le`, `summable_depthDeficit`, `depthDeficit_anti`, **`tendsto_depthDeficit`** (G → 0, dominated convergence), **`depthDeficit_le_of_gap`** (gap g ⇒ G ≤ e^{−gv}Σ|q|).
- **`norm_offLineSum_sub_level_le`**: off-line sum = top-level sum + remainder of norm ≤ e^{Dv}G(v).
- **`exists_minor_fails_of_depthDeficit`**: ∃ c, ℓ > 0 (top-level data only) s.t. for every V ≥ 0 with G(V) ≤ c/2 and 2M_b + 3Σ|q| < (c/2)e^{DV}, the minor fails at some lag in [V, V + (|T₀|+1)ℓ]. **`eventually_minor_fails_in_every_window`**: failures recur with bounded gaps beyond some V₀ (quantitative strengthening of C31 for finite top level).
- README mechanism 9 + open problem 2 updated. Axioms: [propext, Classical.choice, Quot.sound]. Wired after C44.
- (C45 extended, same contribution) `InghamWindowsForAnAttainedTopLevel.lean`: `inghamConst_two_pi_div_ge` (C(2π/g, g) ≥ 6/g via termwise comparison with the telescoping sum), **`exists_ingham_window_lower`** (heights g-separated ⇒ every interval of length 4π/g has a lag with |Σ_F q_t e^{iγ_t v}| ≥ |q_{t₀}|/2), **`exists_minor_fails_of_ingham`** (explicit: level tail ≤ |q₀|/8, G(V) ≤ |q₀|/8, 2M+3Σ|q| < (|q₀|/4)e^{DV} ⇒ minor fails in [V, V+4π/g]), `exists_levelTail_le`, `exists_height_sep_of_level`, **`eventually_minor_fails_in_every_ingham_window`** (every attained top level, finite or infinite: failures in every window of length 4π/g beyond some lag).
- C45's level split generalized to a finite part of the level (`levelTail`); superseded and removed (nothing stale): `exists_level_window_lower`, `exists_minor_fails_of_depthDeficit`, `eventually_minor_fails_in_every_window` (compactness constant, finite top only). README mechanism 9 / open problem 2: only the non-attained top remains open. Axioms clean; wired after DepthDeficitTransformReplacesTheGap.

### C46 — Local visibility of an off-line level: deficit, excess and level tail (`LocalVisibilityOfAnOffLineLevel.lean`; supersedes the file name `InghamWindowsForAnAttainedTopLevel.lean` of the C45 extension, renamed, old olean removed)
- New in `DepthDeficitTransformReplacesTheGap.lean`: `depthExcess Z b r v = Σ_{Re t>r} |q_t| e^{(Re t − r)v}`, `depthExcess_term_le`, `summable_depthExcess`, `depthExcess_mono`, `depthExcess_eq_zero_of_top`; **`norm_offLineSum_sub_level_le`** now needs no top hypothesis: off-line sum = level part over finite F + error ≤ e^{Dv}(τ + G(v) + E(v)).
- **`exists_minor_fails_of_level`** (local visibility): for any zero t₀ right of the line (not necessarily deepest), F ∋ t₀ finite on its level with g-separated heights, τ, G(V), E(V + 4π/g) each ≤ |q₀|/12 and 2M+3Σ|q| < (|q₀|/4)e^{DV} ⇒ minor fails in [V, V+4π/g]. Deeper zeros elsewhere are allowed as long as their weight at this bump has not taken over by the end of the window: quantitative handle on non-attained tops.
- `eventually_minor_fails_in_every_ingham_window` now derived via E = 0 on a top level. README mechanism 9, open problem 2 updated. Axioms clean.
- (C43 extension, not counted) `PoleFreeDyadicWindowsDecideTheCriticalLine.lean` (separate module: C43 is imported by an APT module, so C43 itself is left untouched): `exists_minor_fails_polarFree_of_ge` (Hodge-class tail visibility, any bump width), `onLine_or_poles_iff_polarFree_twoBump_nonneg_of_ge` (tail Hodge criterion), `polarFreeKernel`, **`onLine_iff_polarFree_primeWindow_le_arch`**: RH ⟺ for all heights γ, lags v ≥ V, |τ| = 1: Re Σ_{|log n − v| ≤ 2w} Λ(n)/√n (k(log n)+k(−log n)) ≤ Re (1/2π)∫ h_k Γ — dyadic prime window vs archimedean term, no pole terms. Axioms clean; wired after C43. README mechanism 21 sentence.

### C47 — Even and odd two-bump tests decide the critical line (`EvenAndOddTwoBumpTestsDecideTheCriticalLine.lean`)
- Reduces the three-parameter criterion (C34/C38) to two parameters and a sign: τ = ±1 suffices.
- `lagCoeff` (coefficient F(z) of the zero ½ + z), `I_mul_gammaOf_half_add`, `gammaOf_reflect_eq_conj`, **`lagStructure_eq_tsum_lagCoeff`** (S(v) = Σ_z F(z)e^{zv} over ℂ), `lagCoeff_neg_conj` (F(−z̄) = conj F(z)), **`conj_lagStructure_neg`** (conj S(−v) = S(v): the minor X(v) = 2S(v)), `evenCoeff` (D(z) = F(z) + conj F(z̄)), **`two_re_lagStructure_eq`** (2Re S(v) = Σ_z D(z)e^{zv}), **`abs_re_lagStructure_le`** (τ = ±1 positivity ⇒ |Re S(v)| ≤ Re S(0)).
- `mem_of_evenCoeff_ne_zero`, `re_le_of_evenCoeff_ne_zero`, `countable_evenCoeff_support`, `finite_evenCoeff_line`, **`evenCoeff_eq_zero_of_evenOdd_nonneg`** (C40 on the merged exponential sum: every exponent with Re > 0 has D = 0).
- `paperFT_scaledBump_neg`, `conj_paperFT_scaledBump`, `gammaOf_half_add`, `lagCoeff_modScaledBump` (F = m h(−iz − c)²), **`exists_center_evenCoeff_ne_zero`** (non-cancellation: D = m h(x−iδ)² + m* h(2γ−x−iδ)²; if zero for all centers then m φ(x) = m* φ(x − 2γ) with φ = |h(·−iδ)|², so φ(±2nγ) ≥ φ(0) > 0 against the decay `norm_paperFT_le_decay`; height-zero case direct).
- **`onLine_iff_evenOdd_twoBump_nonneg`** (all tempered configs), **`onLine_iff_primeSide_evenOdd_twoBump_nonneg`** (ζ, prime side). README mechanisms 9 and 21 ("Two parameters decide the line"). Axioms: [propext, Classical.choice, Quot.sound]. Wired after C46.

### C48 — Difference two-bump tests decide the critical line: one sign (`DifferenceTwoBumpTestsDecideTheCriticalLine.lean`)
- For configurations without real zeros (ζ: |Im ρ| ≥ 4 via corpus `RHTower.riemannZeta_ne_zero_of_abs_im_lt_four`), the difference tests κ_γ(t+v/2) − κ_γ(t−v/2) alone decide the line: one-sided bound + corpus Landau (`RHTower.exists_differentiable_extension_of_le_exp`).
- **`eq_zero_of_resolventSum_eq_differentiable`**: general residue lemma (any F holomorphic on Re s > c agreeing with Σ q/(s−λ) on Re s > A kills the top residue; C32's argument with an abstract extension). **`integral_tsum_exp_mul_exp_neg`**: ∫_0^∞ (Σ q e^{λu}) e^{−su} du = Σ q/(s−λ) for Re λ ≤ A < Re s.
- `abs_re_le_of_lagCoeff_ne_zero`, `summable_norm_lagCoeff`, `norm_lagCoeff_mul_exp_le`, **`continuous_lagStructure`**, `exists_abs_im_ge_of_evenCoeff` (no real zeros ⇒ exponents η₀ away from ℝ), **`evenCoeff_eq_zero_of_difference_nonneg`**.
- **`onLine_iff_difference_twoBump_nonneg`** (tempered, no real zeros), `zetaZeroConfig_im_ne_zero`, **`zeta_onLine_iff_difference_twoBump_nonneg`**, **`onLine_iff_primeSide_difference_twoBump_nonneg`** (RH ⟺ prime-side positivity on the autocorrelations of difference tests). README mechanisms 9, 21. Axioms: [propext, Classical.choice, Quot.sound]. Wired after C47.
- Note (consolidation): C32's `eq_zero_of_norm_tsum_exp_le` could be derived from `eq_zero_of_resolventSum_eq_differentiable` (F = Mellin transform); not refactored to avoid invalidating ~12 downstream SRT modules and APT importers.
- (C48 extension) tails and windows: `evenCoeff_eq_zero_of_difference_nonneg` now needs positivity only for lags v ≥ V (on [0,V] the a priori bound K e^{v/2} keeps φ one-sided bounded); **`onLine_iff_difference_twoBump_nonneg`** (any bump width w, any V); **`onLine_iff_difference_primeWindow_nonneg`**: RH ⟺ window functional P_v ≥ 0 on difference tests at every height γ and lag v ≥ V (2w < log 2): two real parameters, one sign, one dyadic prime window per test. (Removed the special-case `zeta_onLine_iff_difference_twoBump_nonneg`, subsumed.)
- (C48 extension, Hodge class) `lagCoeff_scaledBumpPolarFree` / `evenCoeff_scaledBumpPolarFree` (polar-free merged coefficient = (¼ − z²)² × modulated one), **`onLine_iff_polarFree_difference_twoBump_nonneg`**, **`onLine_iff_polarFree_difference_primeWindow_le_arch`**: RH ⟺ for every height γ and lag v ≥ V, Re Σ_{|log n − v| ≤ 2w} Λ(n)/√n (k(log n)+k(−log n)) ≤ Re (1/2π)∫ h_k Γ for k the kernel of the polar-free difference test — no τ, no pole terms, one dyadic window per test. Module now imports PoleFreeDyadicWindows (for `polarFreeKernel`).

### C49 — One parameter decides the critical line (`OneParameterLagFamilyDecidesTheCriticalLine.lean`)
- For all but countably many bump widths w, the one-parameter family κ_w(t+v/2) − κ_w(t−v/2), v ≥ V (no modulation, no τ) decides the line for every tempered configuration without real zeros; for ζ: one real inequality per dyadic window.
- **`evenCoeff_modScaledBump_zero`**: at center 0 the merged coefficient is (m_t + m_{t̄}) h_w(−iz)² (conjugates add — no cancellation). **`countable_setOf_paperFT_scaledBump_eq_zero`**: w ↦ h_w(p) = 4w ĥ(4wp) vanishes for countably many w (entire g(ζ) = ĥ(4ζp), g(0) = ∫κ ≠ 0; Mathlib codiscrete zeros + Lindelöf). **`countable_bad_widths`** (union over the countable carrier).
- **`onLine_iff_lag_twoBump_nonneg`** (hypothesis: h_w ≠ 0 at γ_ρ of off-line zeros), **`zeta_onLine_iff_lag_primeWindow_nonneg`**: ∃ countable E, ∀ w ∈ (0, ½ log 2) \ E, ∀ V ≥ 0: RH ⟺ ∀ v ≥ V, Re P_v(window; f_v ⋆ f̃_v) ≥ 0. Uses C48's one-sided Landau lemma at the single center 0.
- README mechanisms 9, 21 ("One parameter decides the line") + trap (exact but no visibility aperture). Axioms clean; wired after C48.

### C50 — Real zeros cannot hide from the lag family; GRH for Dirichlet L (`RealZerosCannotHideFromTheLagFamily.lean`)
- Removes the no-real-zeros hypothesis of C48/C49 (needed for Dirichlet L of real characters: possible Siegel zeros).
- **`re_evenCoeff_modScaledBump_zero_pos`**: at center 0 a real zero ½+δ has merged coefficient 2m h_w(−iδ)², real positive (h_w(−iδ) real by conj-symmetry + evenness, nonzero by `norm_paperFT_scaledBump_I_mul_ge`).
- **`re_le_zero_of_re_tsum_exp_le`**: abstract Abel-mean lemma: Re Σ q e^{λv} ≤ M on v ≥ 0, Re λ ≤ σ, σ > 0 an exponent ⇒ Re q_σ ≤ 0 ((s−σ)·∫_0^∞ e^{−sv}… → q_σ as s ↓ σ via C48's Laplace identity; real parts ≤ (s−σ)M/s).
- C48 refactors (C48 module only imported by C49/C50): `exists_two_re_lagStructure_le` (one-sided bound on all lags), `exists_im_eq_zero_of_evenCoeff`, **`evenCoeff_eq_zero_of_difference_nonneg_above`** (Landau at any level a ∈ [0,½) above the real exponents); old hreal lemma now a corollary.
- **`evenCoeff_eq_zero_of_lag_nonneg`** (largest real right exponent δ*: Landau above δ*, then Abel mean contradiction; then Landau at 0), **`onLine_iff_lag_twoBump_nonneg_of_lt_one`** (all tempered configs with zeros in Re < 1, generic width), **`grh_iff_lag_primeWindow_nonneg`**: for every primitive χ mod q > 1: ∃ countable E, ∀ w ∈ (0, ½log2)\E, ∀ V ≥ 0: GRH(χ) ⟺ twisted window functional of κ_w(t+v/2) − κ_w(t−v/2) ≥ 0 for all v ≥ V.
- README mechanisms 9, 21. Axioms clean; wired after C49.
- **C51 · The one-parameter lag family determines the configuration, exactly up to conjugation and `s = ½`** —
  `OneParameterLagFamilyDeterminesTheConfiguration`. (i) Uniqueness of exponential sums with locally finite
  heights: `Σ q_t e^{λ_t v} = 0` on `[V, ∞)` kills every coefficient with `Re λ_t ≥ 0` (top poles right of the
  axis, Cesàro means on it) — `eq_zero_of_tsum_cexp_eq_zero`, `eq_zero_of_tsum_exp_eq_zero_of_re_nonpos`.
  (ii) `Re W(f_v,f_v) = 2Re S(0) − 2Re S(v)` (`re_W_lag_eq`); merged coefficient
  `D(z) = (m(½+z)+m(½+z̄)) h_w(−iz)²` for all `z` (`evenCoeff_modScaledBump_zero_eq`); reflection
  `D(−z̄) = conj D(z)` (`evenCoeff_neg_conj`). (iii) `lag_weil_eq_iff_symmMult_eq`: for `h_w` nonvanishing on the
  zero ordinates, equal `Re W` on `κ_w(t+v/2) − κ_w(t−v/2)`, `v ≥ V` ⟺ `m(ρ)+m(ρ̄)` agree for all `ρ ≠ ½`
  (converse holds at every lag, no width condition). (iv) `eq_of_lag_weil_eq_of_conj`,
  `eq_zetaZeroConfig_of_lag_weil_eq`: conjugation-symmetric configurations with equal multiplicity at `½`
  are determined; the zeros of ζ are determined by its lag data. Sharpens mechanism 10 (faithfulness needed
  three parameters τ = 0, 1, i and all centers) to one parameter with the exact kernel. Axioms clean; olean
  built; wired after RealZerosCannotHideFromTheLagFamily; README mechanism 10 extended.
- **C52 · The one-parameter lag family measures the abscissa `Θ = sup Re ρ`** —
  `OneParameterLagFamilyMeasuresTheAbscissa`. For tempered `Z` with zeros in `Re ρ < 1`, generic width `w`
  and every `σ ≥ 0`: all zeros have `Re ρ ≤ ½ + σ` ⟺ `Re W(f_v,f_v) ≥ −C e^{σv}` for large `v`,
  `f_v = κ_w(t+v/2) − κ_w(t−v/2)` (`re_le_iff_lag_twoBump_ge_neg_exp`). Ingredients: upper rate
  `two_re_lagStructure_le_mul_exp`; one-sided growth on all lags `exists_two_re_lagStructure_le_exp`;
  `evenCoeff_eq_zero_of_lag_ge_neg_exp` (Landau at the level of the largest real exponent `δ* > σ`, then Abel
  means after the shift `e^{−σv}` kill its positive coefficient, then Landau at `σ`); nonvanishing
  `evenCoeff_modScaledBump_zero_sub_half_ne_zero`. Prime side: `zeta_re_le_iff_lag_primeWindow_ge_neg_exp`,
  `dirichlet_re_le_iff_lag_primeWindow_ge_neg_exp` — for all but countably many `w ∈ (0, ½ log 2)`, each
  quasi-(G)RH half-plane `Re ρ ≤ ½ + σ` is the single growth condition `P_v ≥ −C X^σ` (X = e^v) on one family
  of dyadic prime windows, real zeros included. Refactor: C48 now has the growth form
  `evenCoeff_eq_zero_of_two_re_lagStructure_le_exp` (Landau with `2Re S ≤ M e^{au}`), from which
  `evenCoeff_eq_zero_of_difference_nonneg_above` follows. Corpus: `RHTower.WeilLagFunctionGrowth` has the
  ζ-only analogue for the canonical weights `1/(ρ(1−ρ))` (no compactly supported tests, no windows, no real
  zeros). Oleans C48–C52 rebuilt; axioms clean; wired; README mechanism 21 extended.
- **C53 · Lag grids see attained tops** — `LagGridsSeeAttainedTops`. Tools: `tendsto_mean_tsum_geom` (Cesàro means
  of `ū^k Σ q_t w_t^k` on the unit disc → `Σ_{w_t=u} q_t`), `tendsto_mean_abs_of_limsup_nonpos` (limsup ≤ 0 ⇒ mean
  |b| → −mean b), `norm_tsum_ite_le_of_limsup_nonpos` (one-sided bound controls every frequency:
  `|Σ_{w_t=u} q_t| ≤ −Re Σ_{w_t=1} q_t`). Resonances: `zeroHeights`, `resonantSteps` (countable),
  `eq_of_cexp_eq_of_not_resonant`. Main: `exists_re_gt_of_grid_lag_ge` — tempered Z, generic width, non-resonant ℓ:
  `Re W ≥ −C` on `κ_w(t+kℓ/2) − κ_w(t−kℓ/2)`, k ≥ N ⇒ every right zero is exceeded (chain or none); real top
  exponents carry positive weight at frequency 1, the top zero's frequency is unshared. Criteria:
  `onLine_iff_topAttained_and_grid_lag_nonneg`, `zeta_onLine_iff_topAttained_and_grid_primeWindow_nonneg` (RH ⟺
  top attained (if any off-line) ∧ window functionals ≥ 0 at X = e^{kℓ}, k ≥ N; generic w, ℓ). No `Re ρ < 1`
  hypothesis needed. SRT form of RHTower's ¬JasOffLineChain progression criteria.
- **C54 · Chains hide from lag grids (no-go with C53 as positive survivor)** — `ChainsHideFromLagGrids`.
  General tool `eq_zero_of_re_tsum_exp_le_of_separated` (Landau for real parts: |Re λ| ≤ ½, heights ≥ η,
  separated ⇒ one-sided bound on v ≥ 0 kills every coefficient with Re λ > 0; doubled family `doubledExp`,
  `doubledCoeff` over ι ⊕ ι). Explicit chain `gridChainExp n = δ_n + i(2π(n+1) + θ_n)`, `δ_n = (1 − 2^{−(n+1)})/4`,
  weights `2^{−(n+1)}`, `θ_n = π/(3(n+3)2^{n+4})`: `re_gridChainSum_nat_nonpos` (Re ≤ 0 at every integer lag;
  dominance `exp_gridChainDepth_le`, balance `gridChain_balance_nonneg`, `gridChain_cos_sum_nonneg`),
  `not_bddAbove_re_gridChainSum` (unbounded on the continuum), non-resonance `gridChainExp_im_sub_eq`,
  `gridChainExp_im_ne`; packaged `exists_chain_hidden_from_grid`. Insight: grids lose exactly the non-attained
  tops (aliasing turns heights → ∞ into exponents accumulating at a real point, defeating Landau); explains why
  every grid/progression criterion in the corpus carries a chain premise. Positive survivor = C53 (proved).
  Oleans built; axioms clean; wired; README mechanism 21 + trap row.
