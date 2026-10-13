# Single-base lag growth decides RH via Borel uniqueness and zero density

- **ID:** single-base-borel-density
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (reduction proved on paper; open core: Borel-type uniqueness)
- **Source:** JAS goal loop row 193
- **Statement:** For every integer `b ≥ 2`: RH ⟺ `|Φ(m log b)| = O(b^{εm})` for every `ε > 0` (`Φ` the Weil lag function). That is, the single-base sequence grows subexponentially in `m` from both sides.

## Why it would matter
- Zero-side data cannot do this: MUST-1371 and MUST-1373 give positive Wolff configurations with vanishing samples. The corpus single-base receivers therefore carry ZAL or attainment hypotheses (MUST-1365).
- The arithmetic input that excludes Wolff is zero density. Wolff configurations are exact disc decompositions with weights equal to disc areas. By Wesler, every complete disc packing has `Σ r_n = ∞`, i.e. `Σ √c_n = ∞`.
- For ζ, Ingham's density theorem `N(½+δ₀, T) ≪ T^{3(½−δ₀)/(3/2−δ₀)} log⁵T` has exponent `< 1` for every `δ₀ > 0`. Hence `Σ_{Re ρ > ½+δ₀} 1/|γ_ρ| < ∞`, i.e. `Σ √|w_ρ| < ∞`, where `w_ρ = 1/(ρ(1−ρ))`.

## Reduction (paper)
1. Subexponential two-sided growth makes the generating function `A(t) = Σ_m Φ(m log b) t^m` analytic on `|t| < 1` (corpus `differentiableOn_lagGen` for bounded sequences).
2. For `|t| < b^{−Θ}` the generating function is the node series `A = Σ_ρ w_ρ/(1 − t b^{ρ−½})` (corpus `lagGen_eq_nodeSeries`).
3. Fix `δ₀ > 0` and split the zeros at `Re ρ − ½ = δ₀`.
   - The low part `R` is analytic on `|t| < b^{−δ₀}`.
   - So `G = A − R` is analytic there and equals the high series `S = Σ_{δ_ρ > δ₀} w_ρ/(1 − t b^{ρ−½})` near `0`.
4. The high series has poles `p_ρ = b^{−(ρ−½)}` in `b^{−Θ} ≤ |t| < b^{−δ₀}`, with residues `−w_ρ p_ρ` satisfying `Σ |res|^{1/2} < ∞` (Ingham).
5. Borel-type uniqueness would give `S = G` on almost every small circle around a pole that avoids the discs `D(p_n, λ|res_n|^{1/2})`.
6. Contour integration around a pole `p*` of positive weight then gives a contradiction:
   - `∮S = 2πi Σ_{inside} res`, and `∮G = 0`.
   - On a small circle the residues `−w_ρ p_ρ ≈ −p* w_ρ` have nonzero sum, because the weights lie in the sector `|w| ≤ 2 Re w`.
7. Hence no zero has `Re ρ − ½ > δ₀`. Since `δ₀` is arbitrary, RH follows.

## Open core
A Borel-type uniqueness lemma for `Σ A_n/(z − a_n)` with `Σ |A_n|^{1/2} < ∞`: if the series agrees with a function analytic on a larger disc on an open subset, then it agrees on almost every circle avoiding the discs `D(a_n, λ|A_n|^{1/2})`.
- Classical folklore (Borel's monogenic functions) suggests this exponent is sharp (Wolff/Wesler).
- A proof is still needed. Harmonic-measure arguments fail because infinitely many holes can carry large harmonic measure (`Σ 1/log(1/ρ_n) = ∞`).

## Checks
- Consistent with MUST-1374: the chain countermodel has `Σ√c < ∞` but is only one-sided bounded, and the argument needs two-sided subexponential growth.
- Consistent with MUST-1373: Wolff violates `Σ√c < ∞`.

## Verdict (loop row 194): mechanism FALSE (heuristic); parked
- **The open core fails, even for positive weights.**
  - By Newton's theorem, a radial bump about `a` has exactly the moments of `m·δ_a`.
  - So an exact positive decomposition of a radial-about-0 density on the annulus into radial bumps gives a positive configuration with all positive and negative moments zero.
- **Cost per scale.** A scale with residual amplitude `A` and piece scale `ℓ` costs `Σ√c ≍ √A/ℓ`.
  - Plain sampling (`h_a = g(a)`) is second-order accurate: shrinking the scale by `K` gives `A' ≍ A/K²`. That is exactly critical for exponent ½, and explains Wesler's `Σ r = ∞` for disc packings.
  - Positive coefficients with Laplacian (quasi-interpolation) correction are order-`p` accurate. With `p ≥ 3` the cost ratio per step is `< 1`.
  - Hence `Σ√c < ∞`, and indeed `Σ c^q < ∞` for every `q > 0`, with weights `> 0`. Exactness comes from the L¹-convergent residual. The boundary is handled by density vanishing to infinite order and Whitney scales.
- **Consequence.** Weights `≍ 1/γ²` are compatible with counting `≪ T^ε`. Single-base receivers need ZAL even granting any power-saving zero density.
- **Positive survivor.** With finitely many zeros beyond each depth `δ₀`, subexponential single-base growth forces RH (Vandermonde; trivial). The sharp counting threshold between "finite" and `T^ε` is OPEN (Borel/Gonchar-type quasi-analyticity).
- **Lean status.** None. A full paper proof of the density-blind construction needs a positive quasi-interpolation lemma with residual log-smoothness bookkeeping. Recorded as a conjectural theorem, not proved.

## Lean status (Opus loop rows 1142–1143; CANNOT-515 + addendum [L])
- **Complex weights, all moments zero.** `HTGeometry/CircleQuadratureAnnihilatingMeasure`: distinct nodes in `5/4 ≤ |x| ≤ 10` and `Σ|c|^p < ∞` for every `p > 0`, with `Σ c x^m = 0` for every `m ≥ 0`.
  - The node series vanishes on `|t| < 1/10` and has a simple pole at the isolated node `4/5` (`tsum_coef_div_eq_zero`, `norm_tsum_coef_div_ge`).
  - Construction: telescoping circle quadrature with discrete-Fourier weights; Bernoulli gives the radius gain.
- **Sector weights, moments `m ≥ 1` zero.** `HTGeometry/CircleQuadratureSectorWolffMeasure`:
  - each stage is shifted by `(2^k+3)L_k`, which gives `|c| ≤ 2 Re c` and arguments → 0, still with `Σ|c|^p < ∞` for every `p`;
  - the node series is constant near `0` and has a pole at `4/5`;
  - this rigorously refutes the open core even in the sector the card's step 6 uses.
- **Lag lifts.** `RHTower/WeilLagComplexWolffSummable`: `exists_complex_lag_configuration_vanishing_progression` and `exists_sector_lag_configuration_vanishing_progression`. These are locally finite configurations in `½ < Re ρ < 1` with `Φ(mℓ) = 0`.
- **Still paper-only:** exactly positive weights (row 194's Newton + positive quasi-interpolation sketch). The Lean sector result already covers the sign information that the weights `1/(ρ(1−ρ))` actually carry for `|Im ρ| ≥ 1`.

## Lean status update (JAS row 196, MUST-1380)
- The positive-weight counterexample is now formal, by real circle quadrature rather than smooth quasi-interpolation.
  - `HTGeometry.CircleQuadraturePositive.exists_positive_wolff_measure_pSummable`: weights `> 0`, `Σc^p < ∞` for all `p > 0`, moments `m ≥ 1` zero.
  - Lift: `RHTower.exists_positive_lag_configuration_density_blind`: weights of Weil size, `Σ(Im ρ)^{−p} < ∞` for all `p`, every sample `m ≥ 1` zero.
- The positive survivor stands: finite exceptional sets (FOL) suffice.
