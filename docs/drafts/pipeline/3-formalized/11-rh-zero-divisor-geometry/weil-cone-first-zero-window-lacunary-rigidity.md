# Weil-cone rigidity on lacunary sets of ratio 3/2 [Lean] and 4/3 [paper]: the first-zero spectral window

- **ID:** weil-cone-first-zero-window-lacunary-rigidity (loop L165)
- **Stage:** 3-formalized (ratio `3/2`); the ratio `4/3` version is [P]
- **Type:** THEOREM (Lean) + THEOREM (paper)
- **Lean:** `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_threeHalves_lacunary`, in modules
  `RHTower/RiemannKernelModulatedWindowTests` and `RHTower/WeilFullConeThreeHalvesLacunaryRigidity`.
  Both are wired into `RHTower.lean`, `lake build` is green, and the axioms are the standard three.
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md` L164 (annihilation design space), L165
- **Statement:** If `lam` is full-cone Weil-positive and `lam(n) = Λ(n)` for every `n ≥ 2` outside a set
  `S = {n_1 < n_2 < ⋯}` with `n_{i+1} ≥ (4/3)·n_i`, then `lam = Λ`. The deviations on `S` are arbitrary a priori
  (any sign, any size up to the universal box `|lam(n)| ≤ √n(log n + C₀)`).

## Goal
Extend the lacunary rigidity of L158 (ratio `≥ 3`) and L159 (exact powers of 2) to every set whose consecutive
elements have ratio `≥ 4/3`, e.g. `{2^j} ∪ {3·2^j}` (ratios `3/2, 4/3` alternating), and identify what sets the
threshold: the zero-free interval `|t| < γ₁ = 14.1347…` of `Ξ`.

Non-circularity: the proof uses only the full-cone Weil positivity of `lam`, the near-null (radical) test class
`k̂ = Ξ²|ĝ|²`, and the classical fact `ζ(½ + it) ≠ 0` for `0 < t ≤ 13.8` (rigorous zero computations: Gram 1903,
Backlund 1918). No statement about zeros above `13.8` and no RH input is used.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof below
- [x] 2 → 3  formalized, for ratio `3/2`, using the window `|t| ≤ 10.26`.
  - That window comes from the fourth reciprocal trace: two conjugate copies of a critical zero put `2/γ⁴` into a trace below `9/50000` (`phiFourierReal_ne_zero_of_abs_le`).
  - The ratio `4/3` needs a Lean certificate of `Ξ(t) ≠ 0` for `|t| ≤ 13.8`.

## Setup and notation
- `X(ξ) = Ξ(2πξ)` is the Fourier transform of Riemann's kernel `Φ`; `K = Φ⋆Φ̃` has `𝓕K = X²`
  (`RHTower.fourier_riemannAutocorr_eq`).
- `v(n) = (Λ(n) − lam(n))/√n` (`normDeficit`), supported on `S`. Put `λ_n = log n`, `ω(n) = 3 + log n`.
- Box bound: `|v(n)| ≤ log n + C₀` (`abs_le_of_weilPositive`), so `M := sup_{n∈S} |v(n)|/ω(n) < ∞`.
- Window: `L = 13.8/(2π)`, so `2L = 13.8/π = 4.3927…`; `X(ξ) ≠ 0` on `|ξ| ≤ L`. Let
  `w(ξ) = cos²(πξ/(2L))·1_{|ξ|≤L}`. Its transform is, with `u = 2L|y|`,
  `ŵ(y) = ∫ w(ξ)e^{2πiξy}dξ = L·sin(πu)/(πu(1 − u²))`, `ŵ(0) = L`, and
  `r(u) := |ŵ(y)|/ŵ(0) = |sin πu|/(πu|1 − u²|)`.
  Elementary values: `r` decreases on `[1,2]` from `½` to `0`; `r(1.2638) = 0.3108`; on `[2,∞)` the maxima are
  `≤ 0.0257` (near `u = 2.45`), `≤ 0.0083` (near `3.47`), and `r(u) ≤ 1/(πu(u²−1))` in general.
  Write `R(u) = sup_{u' ≥ u} r(u')`.

## Step 1 — admissibility of band-limited radical tests on lacunary supports [PROVED HERE]
**Lemma 1.** Let `lam` be full-cone Weil-positive with `v` supported on `S` as above. Let `ĝ` be `C^∞`, supported
in `|ξ| ≤ L`, and `g = 𝓕⁻¹ĝ` (a Schwartz function). Then
`0 ≤ Re Σ_n v(n)(R_g(log n) + R_g(−log n))`, where `R_g = K⋆g⋆g̃` has `𝓕R_g = X²|ĝ|²`.

*Proof.* L160's `normDeficit_pairing_nonneg` (compactly supported `g`) holds verbatim with the hypothesis
`|v(n)| ≤ A` replaced by `|v(n)| ≤ A(1 + log n)`: its only use of `A` is the domination
`Σ_n |v(n)|·C e^{−2 log n} < ∞`, and `Σ (1 + log n)(n+1)^{−2} < ∞`. The decay version
(`normDeficit_pairing_nonneg_of_decay`, cutoffs `M → ∞`) needs `Σ_n |v(n)|(1 + log n)^{−k} < ∞` and
`|g(x)| ≤ D(1 + |x|)^{−(k+2)}`. On `S`, `log n_i ≥ log n_1 + (i − 1) log(4/3)`, so with `k = 3` the first sum is
`≪ Σ_i i^{−2} < ∞`; a Schwartz `g` has every polynomial decay. ∎

## Step 2 — the tests [PROVED HERE]
Fix `j` and `ε ∈ {±1}`. Let `τ` be a `C^∞` taper, `τ = 1` on `|ξ| ≤ L − η`, `τ = 0` on `|ξ| ≥ L`, and
`s(ξ) = cos(πξ/(2L))τ(ξ)`. Put `ĝ(ξ) = s(ξ)(1 + ε e^{2πiξλ_j})/(√2 X(ξ))`. It is `C^∞` with support in
`|ξ| ≤ L` (because `X ≠ 0` there), and `X²|ĝ|² = w_η(ξ)(1 + ε cos(2πξλ_j))`, `w_η = s²`. Hence
`R_g(y) = ŵ_η(y) + (ε/2)(ŵ_η(y − λ_j) + ŵ_η(y + λ_j))`.

Taper control. `w_η − w = cos²·(τ² − 1)` has `L¹` norm `O(η³)`, so `|ŵ_η − ŵ| ≤ Cη³` uniformly. Because `cos²`
vanishes to second order at `±L`, `‖w_η'''‖_{L¹}` is bounded uniformly in `η`, so `|ŵ_η(y)| ≤ C'/(1 + |y|)³`
uniformly in `η`. The samples entering Step 3 are the points `λ_n`, `λ_n ± λ_j` (`n ∈ S`), each with a weight
`≤ 1 + λ_n/3`. Given `κ > 0`:
- the samples beyond `Y₀` contribute at most `Σ_{λ_n > Y₀}(1 + λ_n/3)·3C'(1 + λ_n − λ_j)^{−3}/ŵ(0)`-type sums, which
  are `< κ` for `Y₀` large because `λ_{n_{i+1}} − λ_{n_i} ≥ log(4/3)`;
- the finitely many samples below `Y₀` move by at most `Cη³/ŵ(0)` each, so by `< κ` in total for `η` small.

So it is enough to prove the contraction below for `ŵ` itself, with margin.

## Step 3 — the contraction [PROVED HERE]
Lemma 1 with the test of Step 2 and `ε = −sign v(n_j)` gives, isolating `n = n_j` (all sums over `n ∈ S`):
`½|v_j|ŵ(0) ≤ Σ_n |v_n||ŵ(λ_n)| + ½Σ_n |v_n||ŵ(λ_n + λ_j)| + ½Σ_{n≠n_j} |v_n||ŵ(λ_n − λ_j)|`.
Insert `|v_n| ≤ Mω(n)` and the weight ratios `ω(n)/ω(n_j) ≤ 1` for `n ≤ n_j`,
`ω(n)/ω(n_j) ≤ 1 + (λ_n − λ_j)/3` for `n > n_j` (write `ρ_{n,j}` for this bound), and divide by `½ŵ(0)ω(n_j)`:
`|v_j|/ω(n_j) ≤ θ·M`, with
`θ = 2Σ_n ρ_{n,j} r(2Lλ_n) + Σ_n ρ_{n,j} r(2L(λ_n+λ_j)) + Σ_{n≠n_j} ρ_{n,j} r(2L|λ_n − λ_j|)`.

With `δ = log(4/3) = 0.28768`, the `d`-th neighbour on either side satisfies `|λ_n − λ_j| ≥ dδ`, i.e. `u ≥ 1.2638 d`.
Bound each term by its worst position, i.e. by `sup_{D ≥ dδ}(1 + D/3) r(2LD)` on the right and by `R(2Ldδ)` on the
left (`r` falls on `[1,2]`, and its later maxima sit near `u = k + ½`):
- right neighbours: `d=1`: `1.0959 × 0.3108 = 0.3406`; `d=2`: `1.1918 × 0.02328 = 0.0278`; `d=3`: `≤ 0.0051`
  (bump near `u = 4.47`); `d≥4`: `≤ 0.0100`. Total `≤ 0.3835`;
- left neighbours (weight `≤ 1`): `0.3108 + 0.0233 + 0.0039 + 0.0060 ≤ 0.3440`;
- base terms: `λ_n ≥ log 2 + (i−1)δ`, so `u ≥ 3.045 + 1.264(i−1)`, and the weight is `≤ 1 + λ_n/3`:
  `Σ ≤ 0.0102 + 0.0050 + 0.0026 + 0.0012 + 0.0009 + 0.0007 + 0.0004 + 0.0010 ≤ 0.0220`, doubled `≤ 0.0440`;
- shifted terms: `λ_n + λ_j ≥ 2 log 2`, so `u ≥ 6.09`: `≤ 0.0040`.

So `θ ≤ 0.776 < 1`, with margin `0.22` that absorbs the taper errors of Step 2. Taking the supremum over `j` gives
`M ≤ θM`, hence `M = 0`, `v = 0` on `S`, and `lam = Λ`. ∎

## What the threshold means (the resolution law)
- The rigid ratio is set by the zero-free window of `Ξ` around `0`: a band-limited radical test of spectral half-width
  `L` resolves log-gaps `≳ c/(2L)`. For lattices (`S ⊂ b^ℕ`) L164's periodization is exact down to
  `log b > π/γ₁ = 0.2223` (`b > 1.249`); the `cos²` window here reaches `log q ≥ 0.2877` for arbitrary lacunary sets.
- Below the first zero no zero information is needed, because `X` has no zeros in the window. Pushing the window
  past `γ₁` requires notches at zeros. Their crosstalk at the samples is a zero exponential sum
  `Σ_γ e^{iγ log n}`. Notches narrower than the zero spacing have transform range `≍ log T`, so these sums are needed at
  `x ≍ T^C`, `C > 1`, beyond Landau–Gonek even under RH, and beyond Selberg's density `x ≤ T^{1/4}` unconditionally.
  The first-zero window is therefore the natural limit of zero-free radical tests.

## Relation to the corpus
- Strictly contains L158 (`n_{i+1} ≥ 3n_i`) and the general-sequence content of L159 (which needed exact powers of 2).
- Not implied by L163 (`Σ(lam−Λ)²/(1+log n)^K < ∞`): lacunary deviations of size `√n` violate that hypothesis.
- Uses a test class not used before in the Weil-cone lane: radical tests whose spectral weight `X²|ĝ|²` is an arbitrary
  window inside the first zero-free interval (L158–L163 used `Φχ_L`-pairs, i.e. spectral weight `X²` times a
  trigonometric polynomial).

## Lean formalization (ratio 3/2)
The Lean proof avoids the taper of Step 2 entirely. It superposes the smooth localized tests of L160 over the window instead.
- **Modulated localized tests.** The profile is `φ((ξ−ξ₀)/η)(1 + σe^{2πiξa})/X` (`modTest`). The pairing is exact: `2η[(1+σ²)cos(2πξ₀y)B(ηy) + σ(…)]` (`riemannPairForm_modTest_add_neg`).
- **Superposition.** Integrating over the centre `ξ₀ ∈ (−L, L]` against `cos²(πξ₀/2L)` gives positivity against `B(η·)W(·)`, with `W` the exact `cos²`-window transform (`superposed_deviation_nonneg`). Since `|B| ≤ B(0)`, the kernel bounds are the explicit ones for `W` (`cosSqWindowTransform_eq`, `abs_cosSqWindowTransform_le`).
- **Parameters.** `L = 163/100`, `η = 3/1000`, weight `12 + log n`. The cubic majorants `|W(z)| ≤ Lc/|z|³` hold with `c = 0.0224, 0.0108, 0.0115, 0.0099` in four regimes. Telescoping tails give `θ ≤ 0.963`, so the atom bound is `|v(n_j)| ≤ (97/100) M (12 + log n_j)`.
- **Log-growth pairing.** `normDeficit_pairing_nonneg_of_log_bound` removes the boundedness hypothesis of L160's lemma, so the theorem needs no size condition on the deviation.

## Log
- 2026-09-30 — created at stage 2 (loop L165). Paper proof complete.
- 2026-09-30 — Lean: ratio `3/2` formalized in 79 declarations across two modules, with standard axioms. The card moved to stage 3. Ratio `4/3` stays [P], pending the `|t| ≤ 13.8` certificate.
