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
