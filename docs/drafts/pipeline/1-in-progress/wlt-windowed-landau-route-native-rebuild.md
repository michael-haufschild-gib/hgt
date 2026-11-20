# Windowed Landau route: native rebuild of the pieces the corpus lacks

- **ID:** wlt-windowed-landau-route
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (external claim, unverified) — rebuilt layer by layer as THEOREM (Lean)
- **Source:** external archive (RH + GRH for Dirichlet characters, Lean v4.33.1); read as text only, never built, never copied
- **Statement:** every layer of the route "one-sided bound for the Cesàro–Chebyshev functional on windows ⇒ zero-free half-plane" is restated and proved natively on the corpus and Mathlib; the first layer that cannot be rebuilt is the validation finding.

## Goal
Validate the claimed proof inside our corpus: no vendoring, default heartbeats, our toolchain. Each
layer is an unconditional theorem `X ⇒ (zero-free statement)`; the unproved input `X` of the
innermost rebuilt layer is the current frontier. RH/GRH are not claimed.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Route (outside in) and status

| # | Layer | Statement | Corpus before | Native module (`WindowedLandauTheory/`) | Status |
|---|---|---|---|---|---|
| L0 | headline reductions | nonvanishing of all Dirichlet `L` on `Re s > 1/2` ⇒ `RiemannHypothesis`, zeros on the line; primitive ⇒ all | pieces (`LFunction_eq_zero_conj_one_sub`, `riemannZeta_ne_zero_of_re_lt_zero`) | NonvanishingRightOfTheCriticalLine | open |
| L1a | Taylor coefficients of a Laplace transform | `(-1)^k Φ^(k)(s)/k! = ∫ g u^k e^{-su}/k!`; kernel mass, Chernoff tails with `k ≍ U` | no | TaylorCoefficientsOfLaplaceTransforms | open |
| L1b | coefficients near a simple pole | Cauchy bound `M/r'^k`; `c/(z-ρ)^{k+1}` main term | Cauchy bounds at 0 only | TaylorCoefficientsNearASimplePole | open |
| L1c | Landau on windows (abstract) | real `g ≤ C e^{θu}` on windows `[U,(1+δ)U]`, Laplace transform meromorphic on `Re > θ` with simple poles, positive real coefficient at real poles ⇒ no pole with `Re > θ` | eventual version only (`abscissa_landau_eq`) | LandauOnWindows | open |
| L1d | logarithmic pole data | entire `P`, `P(1) ≠ 0`: `-(P'/P(s) - s P'/P(1) + k(1-s))/(s(s-1))` analytic off zeros, principal part `m·(1/(ρ(1-ρ)))/(s-ρ)` | residue lemmas (`logDeriv_eventuallyEq_of_factor`) | LogarithmicPoleData | open |
| L1e | Mellin transform of the ramp | `∫_1^∞ Σ_{n≤y} a(n)(y/n-1) y^{-s-1} dy = L(a,s)/(s(s-1))` | Abel form only | TheCesaroVonMangoldtRamp | open |
| L1f | windowed criterion | `G_ζ(y) + Σ w_i Re G_{χ_i}(y) ≤ C y^θ` on windows `[Y, Y^{1+δ}]` ⇒ `ζ`, `L(χ_i)` zero-free on `Re s > θ` | ψ-version, all large x (`re_le_half_add_of_chebyshevError_ge_rpow`) | WindowedCesaroBoundsForceZeroFreeHalfPlanes | open |
| L2 | levels | cyclic level of a primitive character, weights `1`, `1/(3o+1)`; window scale ⇒ zero-free for all primitive characters | no | — | not started |
| L3 | host/chain inequality | `ChainTied` family data on windows ⇒ `Gm ≤ x^{1/2+cε}` on windows (archive: `core_gm`, `level_gm_le_on_family_scales`) | no | — | not started (statement not yet read in full) |
| L4 | existence of tied families | `TopG`, `HostExW`, `VWin` (Selmer-length bound), Green datum | no | — | not started |
| L5 | deep inputs | theta lifts between definite unitary groups, Siegel–Weil/mass, Bessel periods, slope inequality, Galois representations, local Langlands | none | — | not started |

## Approach
- Outer analytic layer (L1) is a localized Landau theorem: Taylor coefficients of the Laplace
  transform at a far-right centre, kernel `u^k e^{-σu}(1 + cos(γu + α)) ≥ 0`, nearest-pole
  dichotomy (non-real pole seen from `σ + iγ`, real pole seen from `σ`).
- Formulation choices: pointwise window bound `g ≤ C e^{θu}` (kernel integrated in full, no
  `e^{ηU}` loss); pole hypotheses only on `Re > θ`; family of entire `P_j` with weights, real part
  handled through `L(χ⁻¹, s̄) = conj L(χ, s)` (`LFunction_inv_conj`).
- After L1: read the archive's `core_gm`/`CoreAtH`/`ChainTied` statements in full and restate L3
  natively; that is where the claimed new mathematics enters.

## Log
- 2026-11-20 — created; archive outer layer read (statement files, window Landau cone of 30 modules).
