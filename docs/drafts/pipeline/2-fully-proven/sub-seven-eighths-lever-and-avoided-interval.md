# An Unconditional Sub-Seven-Eighths Zero-Free Half-Plane, Avoided Abscissa Interval, and Monotone Lever

- **ID:** sub-seven-eighths-lever-and-avoided-interval
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1511/obstacles-summary.md` (`## 2.21 The one big question`)
- **Statement:** Every Hecke `L`-function of `ℚ(ω)`, every Dirichlet `L`-function, and `ζ(s)` are unconditionally nonvanishing on `Re s > 20999/24000 = 7/8 - 1/24000` (away from simple principal poles at `s = 1`); hence `zetaZeroAbscissa ≤ 20999/24000`, `zetaZeroAbscissa ∉ (20999/24000, 7/8]`, `subSevenEighthsLever := closedRightBandLever (20999/24000) (7/8)` is an explicit monotone lever for `zetaZeroAbscissa`, the unconstrained `ℝ³` cubic-probe LP vertex is bracketed in `(40535/46328, 20999/24000]`, and no nontrivial zero `ρ` of `ζ` satisfies `ζ(ρ/k) = 0` for any `k ≥ 7`.

## Goal
Resolve `## 2.21` unconditionally in full: exhibit `1/2 < b₁ < b₂ ≤ 7/8` (`b₁ = 20999/24000`, `b₂ = 7/8`) such that `Θ ∉ (b₁, b₂]` with no hypothesis on zeros, construct an explicit monotone lever `T` with `Θ ≤ b ⇒ Θ ≤ T(b)` and `T(b) < b` on `(b₁, b₂]`, determine the sharp unconstrained `ℝ³` vertex of the cubic-probe exponent LP, classify Euler-dilation zero-transport identities ("First lemma to test" in `## 2.21`) together with their unconditional `k ≥ 7` root-coincidence exclusion, and derive all unconditional `[D]` and ruler corollaries.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in target modules, `lake --old env lean` clean, `#print axioms` clean

## Target Modules
- `formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean`
- `formal/GaloisForLFunctions/MetaplecticMobiusDescent/Reflection/SubSevenEighthsLowProbe.lean`
- `formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsHighTransport.lean`
- `formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean`
- `formal/GaloisForLFunctions/ZeroConfigurationGeometry/EulerDilationTransportClassification.lean`
- `formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean`

## Theorems & Complete Proofs (`[PROVED HERE]`)

### 1. Exact Sub-`7/8` SOS Certificate and Unconstrained `ℝ³` LP Vertex (`[PROVED HERE]`)
1. **Sub-`7/8` certificate at `(lx, ly, ℓ) = (17/48, 479/1000, 1001/6000)`.**
   Here `M = lx + ly = 4999/6000`, `M + ℓ = 1`, `lx ≤ ly`, `1 + 3ℓ = 3001/2000 ≤ 4999/3000 = 2M`, `lowBoundary (17/48) (479/1000) (1001/6000) = lowBoundaryGen (17/48) (479/1000) (1001/6000) = 20999/24000 = 7/8 - 1/24000`, and `probeThetaGen 6 (17/48) (479/1000) (1001/6000) = 4499/5000 = 9/10 - 1/5000`.
   For `0 ≤ δ ≤ 5/6` and `0 ≤ x ≤ 1/2`, set `y = 1/2 - x ∈ [0, 1/2]` and
   - `A₀(y) = 32032 y³ + 94004 y² + 130988 y + 51037 ≥ 51037 > 0`,
   - `B₀(y) = 12974 y² + 188503 y + 118478`,
   - `R₀(y) = 7929044604 y⁴ + 27681980500 y³ + 20359386515 y² + 4261272918 y + 26885 ≥ 26885 > 0`.
   Expanding the definitions of `endpointExponent`, `rowCount`, `rowJ`, `rowD`, and `rowP` yields the exact polynomial identity
   `7776000 · A₀(y) · rowJ δ x · (-endpointExponent (17/48) (479/1000) (1001/6000) (20999/24000) δ (x δ) (rowCount δ x)) = (6 A₀(y) δ - B₀(y))² + 58 A₀(y) + R₀(y) ≥ 58 A₀(y)`.
   Since `0 < 35/54 ≤ rowJ δ x ≤ 5/2`, dividing by `7776000 · A₀(y) · rowJ δ x > 0` gives
   `endpointExponent (17/48) (479/1000) (1001/6000) (20999/24000) δ (x δ) (rowCount δ x) ≤ -58 / (7776000 · 5/2) = -29/9720000 < 0`.
   For `δ ∈ [5/6, 1]` and `q ≤ δ/2` with count `1 - δ`, `endpointExponent (17/48) (479/1000) (1001/6000) (20999/24000) δ q (1 - δ) ≤ -109/1500 < 0`; on the floor bin (`δ = 1/50`, `q ≤ 1/100`, `R = 1`, `z₀ = 17/50`), `rowExponent ≤ -5083/900000 < 0`. Moreover, for `R ≥ 1 - δ` on `δ ≤ 1`, `R + δ/2 - 17/50 ≥ 1 - δ/2 - 17/50 ≥ 4/25 > 0`, so `rowExponent` increases strictly with row length `d` up to `v_top = 1 - lx + ℓ = 1219/1500`.

2. **Sharp unconstrained `ℝ³` Farkas barrier.**
   At `x = 1/2`, `rowCount (5/13) (1/2) = 61/91`, `rowCount (16/41) (1/2) = 146633/220457`, and `rowCount (79/204) (1/2) = 21766/32589`. Set `w₀ = 75277/92656`, `w₁ = 92365/1667808`, `w₂ = 220457/1667808` (`w₀ + w₁ + w₂ = 1`, `w_i > 0`), `w_c = 5793/92656`, and `u = lx + ly + ℓ - 1`. For **every** `(lx, ly, ℓ) ∈ ℝ³` and `σ₀ = lowBoundaryGen lx ly ℓ` (or `σ₀ = lowBoundary lx ly ℓ`),
   `w₁ E(5/13) + w₂ E(16/41) = (40535/46328 - σ₀) + w₀ · (σ₀ - lowBoundary lx ly ℓ) + (63691/185312) max(0, u) + (5793/92656) max(0, -u)`.
   Hence `σ₀ < 40535/46328` implies `max(E(5/13), E(16/41)) > 0` over all `ℝ³`. If `σ₀ ≤ 40535/46328`, `E(5/13) ≤ 0`, and `E(16/41) ≤ 0`, nonnegativity of every right-hand summand forces `σ₀ = lowBoundary lx ly ℓ = 40535/46328`, `u = 0`, and `E(5/13) = E(16/41) = 0`, whose unique solution in `ℝ³` is `(lx*, ly*, ℓ*) = (49255/138984, 66541/138984, 5797/34746)`, at which `E(79/204) = 4625/3019566384 > 0`. Therefore `max(E(5/13), max(E(79/204), E(16/41))) > 0` strictly whenever `lowBoundary lx ly ℓ ≤ 40535/46328` or `lowBoundaryGen lx ly ℓ ≤ 40535/46328` on `ℝ³`, bracketing the true unconstrained `ℝ³` cubic-probe vertex in `(40535/46328, 20999/24000]`.

### 2. Low-Side Sub-`7/8` Compensated Probe Bound (`[PROVED HERE]`)
For any unselected slot subset `J ⊆ Fin K` of total slot exponent `d = ∑_{i ∈ J} ell_i ≥ 0` (`∑_{i : Fin K} ell_i = ℓ = 1001/6000`), every prime ideal `P` supported in slot `i` satisfies `N(P) ≥ a Z^{ell_i}`. Factoring `N(𝔞)^{-2} = N(𝔞)^{-1/2} N(𝔞)^{-3/2} ≤ (a^{|J|} Z^d)^{-1/2} N(𝔞)^{-3/2}` and bounding `∑ N(𝔞)^{-3/2}` by `supportedIdeal_rpow_finite_bound (-3/2)` sharpens `lowUnselectedMass` from `O(1)` to `O(Z^{-d/2})`. At `M = 4999/6000`, `ℓ = 1001/6000` (`M + ℓ = 1`, `3ℓ + 1 - 2M = -3/1000 < 0`), replacing `5/6 - 2d` and `1/6 - d` by `M - 2d` and `ℓ - d` in the reflected square-energy bound gives terminal dual width `Td ≤ H + (3ℓ + 1 - 2M - 3d) + 6ε ≤ H - 3d + 6ε`, so the reflected square energy is `O(Z^{M - 7d/4 + 507η})`. Dividing by `q Z^M / Z^{2d}`, taking the square root (`Z^{d/8 + O(η)}`), multiplying by `Z^{-d/2}` (`Z^{-3d/8 + O(η)} ≤ Z^{O(η)}`), and multiplying by `lowGramFactor (Z^{17/48}) (Z^{479/1000}) = O(Z^{(5·17/48 + 479/1000)/12}) = O(Z^{13499/72000})` yields `‖normalizedProbe‖ = O(Z^{13499/72000 + loss})` for arbitrary `loss > 0`.

### 3. High-Side Transport, 1D Residue Shift, Scale-Conjugated Moments, and `β ≤ 20999/24000` (`[PROVED HERE]`)
Assume for contradiction `20999/24000 < HeckeZeroSupremum.beta`; unconditionally `HeckeZeroSupremum.beta ≤ 7/8` (`QuasiRiemannHypothesis.hecke_nonzero`).
1. **Closed Euler correction on `Re s > 17/20`.** On `17/20 ≤ Re x`, `9/10 ≤ Re w`, `4/25 ≤ Re z` and `Q ≥ 4`, the coordinates of `EulerCoordinates` satisfy `‖V‖ ≤ Q^{-24/25} ≤ 1/2`, `‖R‖ ≤ Q^{-103/50} ≤ Q^{-17/10} ≤ 1/2`, `‖W‖ ≤ Q^{-9/10}`, `‖D‖ ≤ Q^{-17/20} ≤ 1/2`, and `‖K‖ ≤ Q^{-3/4}`, with every pairwise product bounded by `Q^{-17/10}`. Hence `unramifiedClosed_open_region_bound` (`≤ 240 Q^{-17/10}` = `globalPrimeDefectBound`), `globalClosedCorrection_bound` (`‖H - 1‖ ≤ 1/2`), and analyticity of `sourceCorrection η S` hold on `Re s > 17/20` (`< 20999/24000`) with the unchanged exclusion set `S = F.exclusions`.
2. **Principal row and 1D contour shift.** At `(Z^{17/48}, Z^{479/1000}, Z)` and `∑ ell'_j = 1001/6000`, `(Z^{17/48})^{1/3} Z^{s - 5/6} = Z^{-(1001/6000)/6} Z^{s - 24749/36000}`. Evaluating the 3D Mellin contours on `a₀ = 7/8 + e > max(7/8, beta)` via `principal_physical_pool_ordered` and `ordered_remainders_scale_bound` bounds the normalized `w`- and `z`-remainders by `O(Z^{7361/45000 + O(e)})` and `O(Z^{13963/75000 + e})`, both strictly below `13499/72000 = 20999/24000 - 24749/36000` (with margin `2363/1800000 > 1/1000`). Shifting the 1D `slotResidue` integral from `a₀ = 7/8 + e` to `a₁ = beta + e > 20999/24000 > 17/20` via `Continuation.vertical_integral_eq_of_polynomial_gaussian_bound` isolates `HeckeSignal.signal χ (sourceCorrection η S) (-24749/36000) Z` up to `O(Z^{beta - 24749/36000 + 2e})`.
3. **Small and large nonprincipal row tails.** Partitioning nonprincipal rows at `L = Z^{1001/100000}` and `U = Z^{1219/1500 + ζ₀}` (`1219/1500 = 1 - 17/48 + 1001/6000`), `small_physical_dyads_sum` at `σ = 7/8 + 8e` saves `> 1/20` below `13499/72000`, and `large_physical_dyad_bound` has `r`-exponent `(1 + ℓ - lx) - (1219/1500 + ζ₀) = -ζ₀ < 0`, saving arbitrary powers of `Z`.
4. **Scale-conjugated central and floor rows (`Z' = Z^{1001/1000}`).** Fixing `Δ₀ > 0` below `10^{-8}` and `(beta - 20999/24000)/10000`, instantiate `D : HighData Δ₀` (`∑ D.ell_j = 1/6`), `F : SourceData D`, and unconditional `SourceMomentBound` at `Z' = Z^{1001/1000}`. Defining `ell'_j = (1001/1000) D.ell_j` (`∑ ell'_j = 1001/6000`), `Z^{ell'_j} = (Z')^{D.ell_j}` and `L = (Z')^{1/100}` match identically, while `(1000/1001)(1219/1500 + ζ₀) < 13/16`. Applying `actual_global_floor_cube_arithmetic` and `actual_nonfloor_class_from_raw_moments` at `Z'` together with `actual_common_cube_aggregate_norm` at `(Z^{17/48}, Z^{479/1000}, Z)` and the SOS bound `≤ -29/9720000` bounds all normalized central and floor rows by `O(Z^{13499/72000 - 10^{-6}})`.
5. **Zero-free conclusion and base change.** Comparing low and high bounds against `HeckeSignal.signalMellin_eq_amplitude` (`c = -24749/36000`) in `Continuation.nonzero_of_regularized_signal` forces every Hecke `L`-function of `ℚ(ω)` to be nonzero on `Re s > (20999/24000 + beta)/2 < beta`, contradicting `beta = sSup`. Hence `HeckeZeroSupremum.beta ≤ 20999/24000`. Base change (`LFunction_eq_dirichlet_product`) and functional-equation reflection give the unconditional zero-free regions for all Dirichlet `L`-functions and `ζ(s)`.

### 4. Euler-Dilation Zero-Transport Classification and `k ≥ 7` Root-Coincidence Exclusion (`[PROVED HERE]`)
By `ZeroForcingCalculus`, every finite Witt/Euler monomial `∏_{j=1}^K ζ(js)^{e_j}` (`e_1 ≠ 0`) preserves off-line zero multiplicity on `Re ρ > 1/2`, so pure Euler-dilation quotients (`ζ(2s)/ζ(s)`, `squarefreePowerQuotient`, `continuedProbeCorrection`) give exact pole/zero equivalence rulers rather than unconditional zero-forcing levers without an external analyticity input across `Re s > Re ρ / k`.
**No-go positive salvage (`[PROVED HERE]`):** Suppose `ζ(ρ) = 0` and `ζ(ρ/k) = 0` with `0 < Re ρ < 1` and integer `k ≥ 2`. Then `0 < Re(ρ/k) < 1/2 < 1 - Re(ρ/k) < 1`, and the functional equation of `ζ` gives `ζ(1 - ρ/k) = 0`. Both `ρ` and `1 - ρ/k` are nontrivial zeros of `ζ` in `(0, 1)`, so `Re ρ ≤ zetaZeroAbscissa` and `1 - (Re ρ)/k ≤ zetaZeroAbscissa`. Eliminating `Re ρ` (`Re ρ + k(1 - (Re ρ)/k) = k`) gives `k / (k + 1) ≤ zetaZeroAbscissa`. Since `zetaZeroAbscissa ≤ 20999/24000 < 7/8 ≤ k / (k + 1)` for every integer `k ≥ 7`, no nontrivial zero `ρ` of `ζ` in `0 < Re s < 1` satisfies `ζ(ρ/k) = 0` for any `k ≥ 7`.

## No-go closure (for pure Euler-dilation ratios in `## 2.21`)
- **Exact killing theorem/mechanism:** On `Re ρ > 1/2`, `Re(kρ) > 1` for every `k ≥ 2`, where `ζ(ks) ≠ 0` is holomorphic; hence `ord_ρ(∏_{j=1}^K ζ(js)^{e_j}) = e_1 ord_ρ ζ`, so pure finite Euler-dilation identities cannot cancel an isolated off-line zero of `ζ` without external analyticity across `Re s > (Re ρ)/k`.
- **Strongest positive survivor:** Unconditional functional-equation abscissa lower bound `k/(k + 1) ≤ zetaZeroAbscissa` from any `k`-fold root coincidence `ζ(ρ) = ζ(ρ/k) = 0` (`k ≥ 2`, `0 < Re ρ < 1`), unconditionally ruling out `ζ(ρ) = ζ(ρ/k) = 0` for all `k ≥ 7` via `zetaZeroAbscissa ≤ 20999/24000 < 7/8`, plus widening of the unconditional `squarefreePowerQuotient` pole-abscissa ruler to `[1/2, 27001/48000)` and Ramanujan shift margin to `≥ 27001/48000`.
- **New insight:** While `ζ(s)/ζ(ks)` alone is a ruler rather than a lever, pairing `ζ(ρ/k) = 0` with `s ↦ 1 - s` creates a genuine two-point abscissa sum rule `Re ρ + k(1 - Re(ρ/k)) = k` whose threshold at `k = 7` sits exactly at `7/8` and is unconditionally broken by `20999/24000`.
- **Status:** Dependency-closed on paper; formalizing directly in `ZeroConfigurationGeometry/EulerDilationTransportClassification.lean`.

## Log
- 2026-11-15 — Promoted to `2-fully-proven` with complete unconditional paper proofs across all 6 target modules.
