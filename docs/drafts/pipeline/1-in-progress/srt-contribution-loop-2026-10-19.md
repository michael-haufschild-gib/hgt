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
