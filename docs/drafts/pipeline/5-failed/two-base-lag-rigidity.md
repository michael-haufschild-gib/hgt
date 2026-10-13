# Two-base lag rigidity (conjecture)

- **ID:** two-base-lag-rigidity
- **Stage:** 5-failed
- **Type:** CONJECTURE
- **Source:** JAS goal loop row 191
- **Statement:**
  - Setting: a locally finite configuration `{(ρ_j, c_j)}` in the strip `|Re ρ − ½| < ½`, closed under `ρ ↦ ρ̄` and `ρ ↦ 1−ρ̄`, with `Re c_j > 0` and `Σ|c_j| < ∞`.
  - Claim: if `Φ(mℓ₁)` and `Φ(mℓ₂)` are two-sided bounded in `m ∈ ℕ` for two spacings with `ℓ₁/ℓ₂ ∉ ℚ`, then every `Re ρ_j = ½`.

## Goal
Decide whether two independent single-base two-sided bounds are a complete receiver.
- One base is blind: MUST-1371 and MUST-1373 give Wolff configurations.
- A dense lag set decides: corpus `WeilLagFunctionDense`.
- A non-meagre set of spacings decides: MUST-1363.

## Evidence for the claim
- **Wolff needs exact wrapping.** The positive disc decomposition cancels all moments only for nodes `x = e^{ℓ(ρ−½)}` of one base, and only with exact aliases `2πiN/ℓ`.
  - For a second base the aliases enter as phases `e^{2πimNℓ₂/ℓ₁}`.
  - Approximate (Dirichlet) aliasing leaves errors `≍ e^{Θmℓ₂}·m·Σ|c|ε`, which are unbounded in `m`.
- **The continuous strip measure is not locally finite after discretisation.** The measure `h(s) dA` on a strip, with `h = 1/(¼ − s²)`, has `F(L) = O(e^{−L/2})` for every real `L`.
  - A disc decomposition of the strip reproduces this identity exactly, but its atoms accumulate at the strip edges, so it is not locally finite (consistent with Landau).
  - Grid quadrature with spacing `2π/ℓ₁` keeps all atoms at one wrapped angle, so the samples grow.
- **Analytic structure.** The generating functions `H_i(s) = Σ_m Φ(mℓ_i)e^{−mℓ_i s}` are analytic on `Re s > 0`, and `H_i = ½W + ℓ_i^{−1}·(periodisation of G with period 2πi/ℓ_i)`, where `G(s) = Σ c_j/(s − (ρ_j − ½))`.
  - Every off-line pole must therefore be non-isolated in both wrapped pictures (shadow law for both bases).
  - Wolff continuation in one wrapped picture is the area-transform mechanism. Doing it in two incommensurable pictures at once has no known construction.

## Attack plan
1. Look for a countermodel built from multi-scale blocks. By Turán, each window around `m ≈ M` needs `≳ Mδ/log M` active atoms with near-cancellation for both bases.
2. Look for a proof via the joint structure of `H₁` and `H₂`: two periodisations of one locally finite pole function, both continuing analytically to `Re s > 0`.

## Status
Open. No Lean.

## Further obstructions (row 191, second pass)
- **One-point quadrature domains are discs.** Exact mean-value cancellation for all monomials forces disc decompositions. Every disc decomposition with full measure accumulates at interior points of the annulus, because finitely many disjoint discs leave gaps of positive area. So exact single-base Wolff configurations are locally finite only after per-disc aliases `2πiN/ℓ₁`.
- **Per-disc aliases rotate the second picture.** They multiply the base-2 node by `e^{2πiNℓ₂/ℓ₁}`.
  - Exact vanishing then needs a positive configuration with prescribed radii and weights whose angles lie in prescribed dense countable sets, with all moments zero.
  - Approximate angles fail, because the errors are amplified by `|x|^m`.
- **A sheet construction gives exact two-base cancellation but is not locally finite.** Take fundamental-domain sections `R_δ = R₀ + τ(δ)` with `∫ w(δ) e^{mℓ₂(δ − iτ(δ))} dδ = 0` for all `m ≥ 1`. This yields exact two-base cancellation for the area-weighted measure. Its disc lift accumulates at bounded heights, so it is not locally finite.
- **Status:** every known mechanism fails exactly at local finiteness, which supports the conjecture. The open step is a rigidity theorem for two incommensurable wrappings of one locally finite pole function `G(s) = Σ c_j/(s − s_j)`.

## Turán structure (row 192 addendum)
- **Single-base two-sided boundedness forces many comparable atoms.** Write `K(m)` for the number of off-line atoms whose terms `c_n|x_n|^m` carry all but a `(K/(2e(m+K)))^K` fraction of `Σ_n c_n|x_n|^m`.
  - On a window where this set is fixed, Turán's first main theorem (corpus `H:PowerSumTuranWeighted`) gives `max |Σ| ≥ (K/(2e(m+K)))^K · Σ_K c|x|^m`, which grows exponentially unless `K(m) ≳ m log|x|/log m`.
  - So a two-sided single-base bound forces `≫ m/log m` off-line atoms of comparable weight at every large scale `m`. Envelope configurations with `O(1)` comparable atoms per scale, such as one conjugate pair per real part, are excluded.
- **Two bases:** at lag `L`, the comparable sets for both bases are the same atoms (comparability depends only on `c|e^{Ls}|`). A proof of the conjecture could therefore pair a two-progression Turán bound with these growing clusters. Open.
- **Lean target:** a quantitative statement with an explicit tail hypothesis, using `H:PowerSumTuranWeighted`.

## Upper-tail cancellation law (row 193, paper sketch; a candidate structural theorem)
- **Mechanism.** On a vertical line `Re z = x`, the 2π/ℓ-periodisation `P_ℓG` of `G(z) = Σ c_n/(z − s_n)` has Fourier coefficients in `Im z`:
  - `ℓe^{−mℓx}F_{<x}(mℓ)` for `m > 0`;
  - `−ℓe^{−mℓx}F_{>x}(mℓ)` for `m < 0`.
  
  Here `F_{>x}(L) = Σ_{Re s_n > x} c_n e^{Ls_n}`. The continuation `E` (bounded on the line by `Mℓ/(1−e^{−ℓx})`) has coefficients `ℓe^{−mℓx}F(mℓ)` for `m ≥ 0` and none for `m < 0`. So `P_ℓG − E` has coefficients `−ℓe^{−mℓx}F_{>x}(mℓ)` for every `m ≠ 0`.
- **Statement.** Suppose the coth-series `Σ c_n (ℓ/2)coth(ℓ(x − s_n + iy)/2)` converges uniformly on the line. This holds for a.e. `x` when `Σ √c_n < ∞` over the off-line atoms, by Borel–Cantelli. Then `P_ℓG − E` is bounded, which forces `F_{>x}(mℓ) = O(e^{mℓx})`.
  - **Reading.** Two-sided single-base boundedness forces depth-graded cancellation: at a.e. depth `x`, the atoms right of `x` cancel down to `e^{mℓx}`.
  - **Checks.** Wolff configurations satisfy it (only straddling discs contribute). An attained top violates it.
- **Possible use.** Combine with the separation-free Turán bound (corpus `exists_norm_weightedPowerSum_ge`) on the zeros above depth `x′ = Θ−η` up to height `T₀`, together with zero density. The arithmetic is borderline under quasi-RH, with `N ≈ m`. A route to "single base two-sided + quasi-RH ⟹ RH" is not excluded. Open.

## Verdict (Opus loop row 1144): FALSE, paper proof below; Lean in progress
**Counterexample.** Take spacings `ℓ₁ = λ`, `ℓ₂ = φλ` (`φ` the golden ratio, `λ > 2 log 10`). There is a locally finite configuration `ρ_i = ½ + z_i/λ` in `½ < Re ρ < 1` with a non-attained top. Its weights satisfy `Re c_i ≥ |c_i|/2` with arguments `→ 0`, and `Σ|c_i|^p < ∞` for every `p > 0`. For it, `Σ_i c_i e^{mℓ₁(ρ_i−½)} = Σ_i c_i e^{mℓ₂(ρ_i−½)} = 0` for every `m ≥ 1`. After closing under `ρ ↦ ρ̄` (weight `c̄`) and `ρ ↦ 1 − ρ̄`, both progressions are two-sided bounded: the mirror terms decay and are at most `Σ|c|`.

**Construction (two-base circle quadrature).**
- Stage `k` uses the product grid `z_{a,b} = r_k + i(T_k + 2π(a + b/φ)/N_k)`, `a, b < N_k`. Here `e^{r_{k+1}} = (1+2^{−k})e^{r_k}` and the heights are `T_k = 20(k+1)`.
- Base 1 sees the node as `X^m ω^{am} β^{bm}`; base `φ` sees it as `Y^m γ^{am} ω^{bm}`. Here `ω = e^{2πi/N}`, `β = e^{2πi/(φN)}`, `γ = e^{2πiφ/N}`.
- Weights `w_{ab} = s + u_a + v_b`.
  - The uniform part `s` has all moments `1 ≤ m < N` zero in both bases, because each base contains a full root-of-unity factor.
  - The `u`-part is invisible to base `φ` (factor `Σ_b ω^{bm} = 0`). Its base-1 moment is `X^m û(m) B(m)` with `B(m) = Σ_b β^{bm}`.
  - Symmetrically, the base-`φ` moment of the `v`-part is `Y^m v̂(m) Γ(m)`.
  - Choosing `û(m) = −R¹_m/(X^m B(m))` and `v̂(m) = −R²_m/(Y^mΓ(m))` kills both residuals for `1 ≤ m < N` exactly.
- Diophantine input: `‖mφ‖ ≥ 1/(3m)`, from `|n² − nm − m²| ≥ 1`. It gives `|B(m)|, |Γ(m)| ≥ 2/(3πφN)`. So `|u|, |v| ≤ O(N)L`, where `L` is the residual bound.
- The shift `s = 2^k·O(N)L` gives the sector and arguments `→ 0`.
- For `m ≥ N` the radius gain `(e^{r_k − r_{k+1}})^{N} ≤ 2^{−4^{k+4}}` (also in base `φ > 1`) absorbs the polynomial losses `N³2^k`.
- Distinct nodes: `a + b/φ` is injective because `φ` is irrational. Local finiteness: stage `k` lies at heights `[T_k, T_k + 11)`.

**Reading.** Two incommensurable bases are blind on the zero side even two-sided, and even with sector weights. The construction extends to any finite family with pairwise Diophantine ratios (product grids). So thin families of lag spacings decide nothing about off-line zeros on the zero side. The positive side is MUST-1363 (a non-meagre family decides). Any two-base criterion must use arithmetic.

## Addendum (JAS row 195, MUST-1379): the open core is exactly the locally finite case
- Without local finiteness, two-sided blindness holds for every family of spacings `≥ ε`, positive weights included (band-limited configuration).
- With local finiteness, an interval of spacings (or a half-line) is rigid: the meromorphic Cauchy series and the identity theorem force all weights to zero.
- Hence any two-base rigidity proof MUST use local finiteness: Jensen, Hadamard, or meromorphy of `Σ c/(z − ρ)`.
- Any two-base blindness construction MUST spread its points to infinite height without the `2πi/ℓ` folding available to a single base.
- Product-grid circle quadrature at growing heights (`HTGeometry/TwoBaseCircleQuadrature`, golden-ratio bases, sector weights, moments `m ≥ 1`) does exactly this. So the two-base receiver is blind for sector weights.
- What remains open: exactly positive weights, and the two-sided (symmetric) version.

## Lean status (Opus loop row 1145; CANNOT-516 [L]) — FALSE, retired
- `HTGeometry/TwoBaseCircleQuadrature` (`exists_two_base_sector_configuration`) and `RHTower/WeilLagTwoBaseWolffConfiguration` (`exists_two_base_lag_configuration_vanishing`, `norm_tsum_mirror_le`). Standard axioms.
- The configuration has spacings `ℓ`, `φℓ`, sector weights with arguments → 0, `Σ|c|^p < ∞` for all `p`, a non-attained top, and local finiteness. Both progressions vanish exactly for `m ≥ 1`.
- **Strongest positive statement (no-go discipline):** a family of lag spacings decides off-line zeros on the zero side only if it is not thin. Thin means finitely many spacings with Diophantine ratios (this card), one spacing (CANNOT-515), or countably many one-sided (MUST-1374). Non-meagre families decide (MUST-1363). For `ζ` itself the open question is arithmetic: does `Φ(mℓ), Φ(mφℓ)` bounded imply RH, using the prime side? Power-gap thickness (MUST-1377) is the only arithmetic mechanism known, and two progressions have gaps `≍ n`.
- Paper and Lean status of the survivor: the zero-side blindness is proved in Lean. The arithmetic two-base question is OPEN, with no mechanism.
