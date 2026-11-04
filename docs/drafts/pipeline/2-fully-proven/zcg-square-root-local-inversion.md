# Local inversion at and above the square-root threshold

- **ID:** zcg-square-root-local-inversion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5.5
- **Statement:** Let `L_T = ½ log(T/2π)` (`T > 2π`) be the square-root bandwidth scale.
  (1) **Sharp Nyquist obstruction on `(0, 1]` for disjoint pairs:** For every `T ≥ 2π e^π` and every
  `0 < λ ≤ 1` (in particular across the entire interval `½ < λ ≤ 1`), the simple critical-line
  configuration `Z_0 = {½ + i k π / L_T}` and its half-shift `Z_1 = {½ + i (k + ½) π / L_T}` are
  reflection-symmetric tempered configurations with Riemann–von Mangoldt local counts
  `|N_{Z_j}(x, y) − (1/2π) log(T/2π)(y − x)| ≤ 1` and identical Weil forms on all windows of
  aperture `λ L_T`, yet have disjoint carriers, nonempty support in `[T − 1, T + 1]`, and uniform
  separation `‖z − w‖ ≥ π / log(T/2π)` across `Z_0 ∪ Z_1`.
  (2) **Uniform sub-spacing and polynomial-precision local inversion above `θ/2`:** For any cluster
  density factor `θ > 0`, any `λ > θ/2`, any excess constant `A ≥ 0`, any tempered difference weight
  `S ≥ 0`, and any polynomial isolation exponent `M ≥ 0`, there exists `T_0` such that for all
  `T ≥ T_0`, any two tempered configurations `Z, Z'` agreeing on windows of aperture `λ L_T` whose
  cancelling cluster `{z | m_Z(z) ≠ m_{Z'}(z)}` has at most
  `θ · (1/2π) log(T/2π)(y − x) + A log T` distinct points in `[x, y] ⊆ [T/2, 3T/2]` and weighted
  global sum `≤ S` satisfy `m_Z(z_0) = m_{Z'}(z_0)` at every `z_0` in `|Im z_0 − T| ≤ T/4` that has
  no other cluster point within `T^{−M}` (hence within `δ / log T` for every `δ > 0`, i.e.
  `o(1/log T)`).
  (3) **Square-root (`λ > ½`) and two-configuration (`λ > 1`) corollaries:** At `θ = 2` (`λ > 1`),
  any two tempered configurations with Riemann–von Mangoldt local counts coincide across
  `|Im z − T| ≤ T/4` outside `T^{−M}` (and `o(1/log T)`) near-collision clusters; at `θ = 1`
  (`λ > ½`, the exact square-root threshold), `zetaZeroConfig` coincides across `|Im z − T| ≤ T/4`
  outside `T^{−M}` (and `o(1/log T)`) near-collision clusters with every tempered mimic whose extra
  carrier near `T` has local density `< (2λ − 1)(1/2π) log(T/2π)`, and a single window pair of
  aperture `λ L_T` recovers the exact integer multiplicity `m_ζ(ρ_0)` within error `1/4` at every
  `T^{−M}`-isolated (or `(δ / log T)`-isolated) zero `ρ_0` of `ζ` in `|Im ρ_0 − T| ≤ T/4`.

## Goal
Resolve `obstacles-summary.md` §2.5.5 unconditionally in both directions: establish the exact
threshold `λ = 1` for arbitrary disjoint-carrier RvM pairs (refuting `½ < λ ≤ 1` by Nyquist
half-shift aliasing), establish `λ = ½` for single-RvM-density clusters and `ζ` zero readout, and
push quantitative local inversion uniformly in `T` past `o(1/log T)` down to arbitrary polynomial
separation `T^{−M}`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Paper proof

### 1. Sharp Nyquist counterexample on `0 < λ ≤ 1`
Let `L > 0` and define `Z_1` on carrier `{½ + i(k + ½)π/L : k ∈ ℤ}` with multiplicity `1`. Reflection
`z ↦ 1 − conj z` sends `k ↦ −k − 1`, preserving `Z_1`. Summability of `(1 + |γ|²)^{−1}` holds by
comparison with `simpleHalfLatticeConfig`. Modulating `f_s(u) = e^{isu} f(u)` at `s = π/(2L)`
preserves `ApertureWindow L` and `f(u) conj g(u)`, shifts `paperFT f_s(w) = paperFT f(w + s)`, and
bijects `Z_1` onto `Z_0 = simpleHalfLatticeConfig L`. By `W_simpleHalfLatticeConfig`, for all `f, g`
supported in `[−L, L]` (hence for all `a = λ L` with `λ ≤ 1`),
\[
W_{Z_1}(f, g) = W_{Z_0}(f_s, g_s) = 2L \int_{\mathbb{R}} f(u)\overline{g(u)}\,du = W_{Z_0}(f, g).
\]
On `[x, y]`, `k ↦ (k + α)π/L` (`α ∈ {0, ½}`) has `⌊Ly/π − α⌋ − ⌈Lx/π − α⌉ + 1` integer hits, which
lies within `1` of `(L/π)(y − x)`. Setting `L = ½ log(T/2π)` gives RvM local count error `≤ 1`,
disjoint carriers, a point in `[T − 1, T + 1]` once `L ≥ π/2`, and minimum separation
`π/(2L) = π/log(T/2π)` across `Z_0 ∪ Z_1`.

### 2. Sub-spacing and polynomial-precision local inversion for `2λ > θ`
Set `u = log(T/2π)`, `a = λ u / 2`, `β = λ − θ/2 > 0`, `ε = β u / 6`, and
`D = ((θ + β)/2)(u/π)`, so `π D / 2 + 2ε = (θ/4 + β/4 + β/3) u = (θ/2 + 7β/6)(u/2) < (θ/2 + β)u/2 = a`
(with `ε = β u / 8`: `π D / 2 + 2ε = (θ/4 + β/4 + β/4)u = (θ/2 + β/2)u/2 < a`).
Near any `z_0` with `|Im z_0 − T| ≤ T/4`, `[Im z_0 − T/4, Im z_0 + T/4] ⊆ [T/2, 3T/2]`, so the
cluster within radius `R = T/4` of `Im z_0` has count `(D, C_0)` with `|C_0| ≤ ℓ D` for a
`T`-independent `ℓ`. Hence `windowSlack (2 D^{−1}) (localSlack D C_0) ≤ σ := ℓ/2 + 6`.

For arbitrary `0 < η` and `D ≥ 1`, put `η' = min(η, D^{−1}) ≤ 1`. Then
\[
\frac{1}{\mathrm{isoConst}(\sigma, \eta')}
= \frac{(\eta' + \sigma)(1 + \sigma)}{\eta'}
\le \frac{(1 + \sigma)^2}{\eta'}
= (1 + \sigma)^2 \max(\eta^{-1}, D),
\]
so `log(1/isoConst(S, η')) ≤ (1 + σ)² + log D + max(0, log(1/η))`. Multiplying `isoRate` by
`nearFarConst(2 D^{−1}, S) ≤ nfRate(σ) D (1 + log D)` yields
\[
\log\bigl(\mathrm{windowFloor}(2D^{-1}, \mathrm{localSlack}(D, C_0), \eta)^{-1}\bigr)
\le F(\ell)\,D(1 + \log D)\bigl(1 + \log D + \max(0, \log(1/\eta))\bigr).
\]
Using the elementary bound `1 + log x ≤ 2√x` (`x ≥ 1`, from `log x = 2 log √x ≤ 2(√x − 1)`), for
`η ≥ T^{−M}` (`log(1/η) ≤ M log T ≤ M(u + 2)`), both `log windowGrowth` and `log(windowFloor^{−1})`
are bounded by `C_1 u^{5/2}` for `u ≥ 2`. Choosing decay order `k = ⌈C_k u^{3/2}⌉₊` and spline order
`m = ⌈windowExponent⌉₊ + k = O(u^{3/2})` gives `m/ε = O(u^{1/2})`, so the explicit spline constant
satisfies `log((4(1 + m/ε))^m) = O(u^{3/2} · u^{1/2}) = O(u^2)`. On the left side of
`one_add_pow_le_of_isolated_cancellation_of_bump`, `1 + T/4 > (π/2)e^u > e^u`, giving
`(1 + T/4)^{2k − 2} ≥ e^{2(k − 1)u} ≥ e^{2 C_k u^{5/2} − 2u}`, which strictly exceeds
`localCameraConst · (1 + |Im z_0|)² S` for `C_k = 2 C_1 + 2` and all `u ≥ u_0`.

### 3. Global RvM tail bound and `ζ` multiplicity readout
For any configuration `Z` with `N_Z(−R, R) ≤ B R log R` (`R ≥ 2`) and `N_Z(−2, 2) ≤ B_0`, partitioning
`ℂ` into `{|γ| ≤ 2}` and dyadic shells `2^n < |γ| ≤ 2^{n+1}` bounds
`∑ ‖m_Z(z)‖/(1 + |γ_z|²) ≤ B_0 + ∑_{n≥0} B 2^{n+1}(n+1)\log 2 / 4^n < ∞`.
Applying the isolating window pair `(F, G)` at `θ = 1`, `λ > ½` directly to `zetaZeroConfig` cancels
all `ρ ≠ ρ_0` in `|Im ρ − Im ρ_0| ≤ T/4` and bounds the far tail `|Im ρ − Im ρ_0| > T/4` by
`≤ ¼ |pointImage F G ρ_0|`, whence `|W_ζ(F, G) / pointImage F G ρ_0 − m_ζ(ρ_0)| ≤ ¼`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** For arbitrary pairs of disjoint simple-zero RvM configurations,
  local inversion on `½ < λ ≤ 1` is false: `simpleHalfLatticeConfig L_T` and its half-shift share all
  Weil images up to aperture `L_T` (`λ = 1`) while maintaining uniform gap `π / log(T/2π)`.
- **Strongest positive survivor:** Uniform polynomial-precision (`T^{−M}`) and `o(1/log T)` local
  inversion holds for `λ > θ/2` (hence `λ > 1` for all RvM pairs and `λ > ½` at the square-root
  threshold for single-RvM-density clusters and exact `ζ`-multiplicity readout).
- **New insight:** Two-window parity splitting halves the aperture demand of the cancelling cluster's
  *distinct-point* density (`π D / 2`), so the square-root threshold `λ = ½` governs single-carrier
  visibility and carrier-contained mimics whereas disjoint two-carrier comparison doubles `D` to
  `λ = 1`; meanwhile `1 + log D ≤ 2√D` with `k ≍ (log T)^{3/2}` defeats `windowFloor^{−1}` down to
  polynomial cluster diameters `T^{−M}`.
- **Status:** Dependency-closed paper proof complete; proceeding immediately to Lean 4 formalization
  in `ZeroConfigurationGeometry/SquareRootInversion/`.
