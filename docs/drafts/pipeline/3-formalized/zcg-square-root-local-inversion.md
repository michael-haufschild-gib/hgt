# Local inversion at and above the square-root threshold

- **ID:** zcg-square-root-local-inversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.5.5
- **Statement:** Let `L_T = ½ log(T/2π)` (`T > 2π`) be the square-root bandwidth scale.
  (1) **Sharp Nyquist obstruction on `(0, 1]` for disjoint pairs:** For every `T ≥ 2π e^π` and every
  `0 < λ ≤ 1` (in particular across the entire interval `½ < λ ≤ 1`), the simple critical-line
  configuration `Z_0 = {½ + i k π / L_T}` and its half-shift `Z_1 = {½ + i (2k + 1) π / (2 L_T)}`
  are reflection-symmetric tempered configurations with Riemann–von Mangoldt local counts
  `|N_{Z_j}(x, y) − (1/2π) log(T/2π)(y − x)| ≤ 1` and identical Weil forms on all windows of
  aperture `λ L_T`, yet have disjoint carriers, nonempty support in `[T − 1, T + 1]`, and uniform
  separation `‖z − w‖ ≥ π / log(T/2π)` across `Z_0 ∪ Z_1`.
  (2) **Uniform sub-spacing and polynomial-precision local inversion above `θ/2`:** For any cluster
  density factor `θ ≥ 0`, any `λ > θ/2`, any excess constant `A ≥ 0`, any tempered difference weight
  `S ≥ 0`, and any polynomial isolation exponent `M ≥ 0`, there exists `T_0 ≥ 2π e` such that for all
  `T ≥ T_0`, any two tempered configurations `Z, Z'` agreeing on diagonal windows of aperture `λ L_T`
  whose cancelling cluster `{z | m_Z(z) ≠ m_{Z'}(z)}` has at most
  `θ · (1/2π) log(T/2π)(y − x) + A log(T/2π)` distinct points in `[x, y] ⊆ [T/2, 3T/2]` and weighted
  global sum `≤ S` satisfy `m_Z(z_0) = m_{Z'}(z_0)` at every `z_0` in `|Im z_0 − T| ≤ T/4` that has
  no other cluster point in `[T/2, 3T/2]` within `T^{−M}` (hence within `δ / log T` for every
  `δ > 0`, i.e. `o(1/log T)`).
  (3) **Square-root (`λ > ½`) and two-configuration (`λ > 1`) corollaries:** At `θ = 2` (`λ > 1`),
  any two configurations satisfying `HasRvMLocalCount` coincide across `|Im z − T| ≤ T/4` outside
  `T^{−M}` (and `o(1/log T)`) near-collision clusters; at `λ > (1 + μ)/2` (in particular `λ > ½` when
  `μ = 0`), `zetaZeroConfig` coincides across `|Im z − T| ≤ T/4` outside `T^{−M}` (and `o(1/log T)`)
  near-collision clusters with every unit-window-bounded mimic whose extra carrier near `T` has local
  density `μ`, and at `λ > ½` a single window pair of aperture `λ L_T` recovers the exact integer
  multiplicity `m_ζ(ρ_0)` within error `1/4` at every `T^{−M}`-isolated (or `(δ / log T)`-isolated)
  nontrivial zero `ρ_0` of `ζ` in `|Im ρ_0 − T| ≤ T/4`.

## Goal
Resolve `obstacles-summary.md` §2.5.5 unconditionally in both directions: establish the exact
threshold `λ = 1` for arbitrary disjoint-carrier RvM pairs (refuting `½ < λ ≤ 1` by Nyquist
half-shift aliasing), establish `λ = ½` for single-RvM-density clusters and `ζ` zero readout, and
push quantitative local inversion uniformly in `T` past `o(1/log T)` down to arbitrary polynomial
separation `T^{−M}`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof

### 1. Sharp Nyquist counterexample on `0 < λ ≤ 1`
For `L > 0`, `Z_0 = simpleHalfLatticeConfig hL` (`{½ + i k π / L}`) and
`Z_1 = shiftedSimpleHalfLatticeConfig hL` (`{½ + i (2k + 1) π / (2L)}`) partition the doubled-density
lattice `Z_{2L} = simpleHalfLatticeConfig (2L)` (`{½ + i m π / (2L)}`) into its even and odd indices.
For all `C²` windows `f, g` supported in `[−L, L] ⊆ [−2L, 2L]` (hence all `a = λ L` with `λ ≤ 1`),
\[
W_{Z_1}(f, g) = W_{Z_{2L}}(f, g) - W_{Z_0}(f, g)
= 4L\int_{\mathbb{R}} f(u)\overline{g(u)}\,du - 2L\int_{\mathbb{R}} f(u)\overline{g(u)}\,du
= W_{Z_0}(f, g).
\]
On `(x, y]`, both lattices satisfy `|N(x, y) − (L/π)(y − x)| ≤ 1`. Setting `L = ½ log(T/2π)`
(`T ≥ 2π e^π`) gives RvM local count error `≤ 1`, disjoint carriers, a zero in `[T − 1, T + 1]`, and
uniform minimum distance `π/(2L) = π / log(T/2π)` across `Z_0 ∪ Z_1`.

### 2. Sub-spacing and polynomial-precision local inversion for `2λ > θ`
Set `u = log(T/2π)`, `a = λ u / 2`, `β = (2λ − θ)/4 > 0`, `ε = β u / 4`, and `D = (θ + β) u / (2π)`,
so `π D / 2 + 2ε = (θ/4 + 3β/4) u < λ u / 2 = a`. Near any `z_0` with `|Im z_0 − T| ≤ T/4`,
`[Im z_0 − T/4, Im z_0 + T/4] ⊆ [T/2, 3T/2]`, so the cancelling cluster within radius `R = T/4` has
count `(D, C_0)` with `|C_0| ≤ ℓ D` for a `T`-independent `ℓ`. Combining `log_inv_windowFloor_le_of_le_one`
(`η ≤ 1`) and `log_inv_windowFloor_le` (`η > 1`) yields, for every `0 < η` without restriction,
\[
\log\bigl(\mathrm{windowFloor}(2D^{-1}, \mathrm{localSlack}(D, C_0), \eta)^{-1}\bigr)
\le \mathrm{floorRate}(\ell)\,D(1 + \log D)\bigl(1 + \log D + \max(0, \log(1/\eta))\bigr).
\]
For `η = T^{−M}` (`max(0, log(1/η)) ≤ 8 M u`) and `1 + log D ≤ D`, both `log windowGrowth` and
`log(windowFloor^{−1})` are `O((1 + M) u³)` independent of the spline decay order `k`. Choosing
`k = ⌈K u²⌉₊` gives `m = ⌈windowExponent⌉₊ + k = O(u²)`, hence `m/ε = O(u)`. Bounding
`log(4(1 + m/ε)) ≤ α · 4(1 + m/ε) + log α⁻¹` at a small `T`-independent `α > 0` makes
`m log(4(1 + m/ε)) ≤ ¼ K u³ + O(u²)` while `(1 + T/4)^{2k − 2} ≥ e^{2(k − 1)u} ≥ e^{2 K u³ − 2u}`,
forcing `|(W_Z(F, G) − W_{Z'}(F, G)) / pointImage F G z_0 − multDiff Z Z' z_0| ≤ ¼`.

### 3. Unit-window tail discharge and `ζ` corollaries
Any configuration satisfying `N_Z(t, t + 1) ≤ A_0 log(|t| + 3)` is automatically `TemperedConfig Z`
with `∑ ‖m_Z(z)‖/(1 + |γ_z|²) ≤ 4 max(A_0, 1) · totalWeight`. `zetaZeroConfig` satisfies
`HasRvMLocalCount` unconditionally via `exists_card_le_sharp`. Applying `(2)` against `Z'` gives
`T^{−M}` and `o(1/log T)` coincidence at `λ > (1 + μ)/2` (hence `λ > 1` for arbitrary RvM pairs and
`λ > ½` for subset-carrier mimics), and applying `(2)` against `emptyZeroConfig` at `θ = 1 + (λ − ½)`
reads `zeroMult ρ_0` within `¼` at every `T^{−M}`-isolated zero of `ζ` for every `λ > ½`.

## Lean

- `GaloisForLFunctions.ZeroConfigurationGeometry.exists_rvm_pair_mimic_disjoint_up_to_one` in
  [ShiftedHalfLatticeCounterexample.lean](../../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/SquareRootInversion/ShiftedHalfLatticeCounterexample.lean).
- `GaloisForLFunctions.ZeroConfigurationGeometry.log_inv_windowFloor_subspacing_le`,
  `exists_subspacing_isolating_windows`, `multDiff_eq_zero_of_subspacing_isolated`,
  `exists_nearCollision_of_mimic_above_half_density`, `multDiff_eq_zero_of_littleO_inv_log_isolated`,
  `exists_nearCollision_littleO_inv_log`, and `exists_window_pair_reads_mult_subspacing` in
  [SubSpacingLocalInversion.lean](../../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/SquareRootInversion/SubSpacingLocalInversion.lean).
- `GaloisForLFunctions.ZeroConfigurationGeometry.HasRvMLocalCount`,
  `exists_hasRvMLocalCount_zeta`, `rvm_coincide_of_extra_density_rpow`,
  `rvm_coincide_of_extra_density_littleO`, `rvm_subset_carrier_coincide_at_squareRoot_littleO`,
  `rvm_pair_coincide_outside_nearCollisions_above_one_rpow`,
  `rvm_pair_coincide_outside_nearCollisions_above_one`, `rvm_local_inversion_dichotomy`,
  `zeta_coincide_of_extra_density_littleO`, `zeta_coincide_subset_carrier_at_squareRoot_littleO`,
  `zeta_coincide_with_rvm_above_one_littleO`,
  `zeta_isolated_zero_multiplicity_readout_at_squareRoot_rpow`, and
  `zeta_isolated_zero_multiplicity_readout_at_squareRoot_littleO` in
  [ZetaAndRvMCorollaries.lean](../../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/SquareRootInversion/ZetaAndRvMCorollaries.lean).

All three modules pass direct `lake --old env lean` checks with zero warnings, and transitive
`#print axioms` audits depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Literal two-configuration local inversion on `½ < λ ≤ 1` is
  false for arbitrary disjoint simple-zero RvM pairs (`exists_rvm_pair_mimic_disjoint_up_to_one`):
  `simpleHalfLatticeConfig L_T` and `shiftedSimpleHalfLatticeConfig L_T` share all Weil images up to
  aperture `L_T` (`λ = 1`) while maintaining uniform gap `π / log(T/2π)`.
- **Strongest positive survivor:** Uniform polynomial-precision (`T^{−M}`) and `o(1/log T)` local
  inversion holds for `λ > θ/2` (`multDiff_eq_zero_of_subspacing_isolated`), giving `λ > 1` for all
  RvM pairs and `λ > ½` at the square-root threshold for subset-carrier mimics, bounded extra-carrier
  density `< (2λ − 1) RvM`, and exact single-zero `ζ` multiplicity readout.
- **New insight:** Two-window parity splitting halves the aperture demand of the cancelling cluster's
  distinct-point density (`π D / 2`), separating single-carrier visibility (`λ = ½`) from disjoint
  two-carrier comparison (`λ = 1`), while `log(4(1 + m/ε)) ≤ α · 4(1 + m/ε) + log α⁻¹` with
  `k ≍ (log T)²` defeats `windowFloor^{−1}` down to arbitrary polynomial cluster diameters `T^{−M}`.
- **Status:** Unconditionally proved and formalized in Lean 4 across `SquareRootInversion/`.
