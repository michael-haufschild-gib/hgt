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
