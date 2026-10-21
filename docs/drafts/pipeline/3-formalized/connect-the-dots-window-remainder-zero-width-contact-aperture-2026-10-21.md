# Connecting the dots across areas: window remainder, zero width, contact aperture

- **ID:** connect-the-dots-walls-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), three modules
- **Source:** docs/reports/review-2110/walls-ledger.md (walls 1, 4, 12); task "connect the dots of theorems in different parts of the Lean corpus"
- **Statement:** (A) unconditionally `|x| ≤ e^{L/2} + C e^{L/2 − κ√L}` for every window deviation `x` at every large length `L`, hence `c(L) ≤ e^{L/2} + C e^{L/2−κ√L}`, `floor(L) ≥ −e^{L/2} − C e^{L/2−κ√L}`, `c(L)/e^{L/2} − 1 ≤ C e^{−κ√L}`; (M) the zero width `zetaZeroWidth = sup |Re ρ − ½|` satisfies: RH ⟺ width `= 0`; for generic `w` and every `σ ≥ 0`, width `≤ σ` ⟺ `P_{w,v} ≥ −C e^{σv}` eventually; every zero of the de Bruijn–Newman deformation `H_t` has `(Im z)² ≤ max(width² − 2t, 0)`, and `H_t` is real-rooted for `t ≥ width²/2`; (D) every near-top zero `½ + z₀` of `ζ` (data `w, η, V ≥ V₀(w, η, Re z₀)`, no zero deeper than `Re z₀ + 1/V`) makes the restricted Weil ground energy `μ(A) < 0` for every aperture `A ≥ V/2 + w`.

## Goal
Three pairs of theorems that lived in different areas and were never composed:

| # | dots joined | areas | wall | new statement |
|---|---|---|---|---|
| A | PNT with error term `ψ(x) − x = O(x e^{−c√log x})` + polar Schur bound of the window ceiling | RHTower (`ChebyshevPsiErrorInputs`) × BiScaleUncertainty (`PrimeWindowCeilingWidthLaw`, `PrimeWindowCeilingPolarAsymptotics`) | 1 (open unit: the window remainder below `O(e^{L/2})`) | the best unconditional remainder of the window ceiling is of de la Vallée Poussin strength, exactly like the lag envelope `P_v ≥ −|φ(0)| − C e^{v/2 − √v/10}`; the polar weight loses only against power errors (the `1/4 + β/2` of the width law), not against the dlVP error |
| M | lag rate law `re_le_iff_lag_primeWindow_ge_neg_exp` + ground-energy abscissa law + de Bruijn heat contraction `cosTransform_heat_zeros_im_sq_le` + `ξ`/`ζ` zero correspondence | SquareRootThreshold × RHTower (`DeBruijnHeatFlowRealZeros`, `DeBruijnNewmanHalfBound`, `ZetaXiZeroCorrespondence`) | 4 (strip width `1/8` the only unconditional value), 1 | one invariant `zetaZeroWidth` with a prime-side reading (lag rate) and a heat-side reading (de Bruijn–Newman time `≤ width²/2`); de Bruijn's `1/8` is the case width `= ½` |
| D | explicit-lag visibility `one_param_near_top_visible_at_explicit_lag` + Rayleigh bridge `μ(v/2+w)∫|f_v|² ≤ Re W(f_v,f_v)` + antitonicity of `μ` | SquareRootThreshold × ArithmeticCriticalityTheory / RHTower | 12 (no-crossing law for `μ(A)`; the contact aperture) | the contact aperture of a hypothetical near-top zero is `≤ V₀/2 + w`; every certified aperture `μ(A) ≥ 0` is the lower bound `V > 2(A − w)` on the visibility lag of every near-top zero |

Non-circular: no RH input anywhere; all statements closed (the only premises are the parameters
that define which zero, which width, which heat time). Selectivity: (A) is a statement about the
actual prime atoms through `ψ`; (M)/(D) are statements about the actual zero configuration.

## Gates
- [x] 0 → 1 well-posed, source-pure (compositions of unconditional corpus theorems)
- [x] 1 → 2 paper proofs: see "Approach"
- [x] 2 → 3 Lean, all `lake env lean` green, `#print axioms` = `propext, Classical.choice, Quot.sound`, wired:
  - `formal/GaloisForLFunctions/BiScaleUncertainty/PrimeWindowCeilingDeLaValleePoussinRemainder.lean` (umbrella `BiScaleUncertainty.lean`)
  - `formal/GaloisForLFunctions/SquareRootThreshold/LagRateBoundsTheDeBruijnNewmanHeatTime.lean` (umbrella `SquareRootThreshold.lean`)
  - `formal/GaloisForLFunctions/SquareRootThreshold/NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture.lean` (umbrella `SquareRootThreshold.lean`)
- [ ] 3 → 4 not pursued

## Approach
**A.** `RHTower.exists_psi_error_eventually` gives `K, c` with `|ψ(x) − x| ≤ K x e^{−c√log x}` eventually;
Chebyshev's `ψ(x) ≤ (log 4 + 4)x` absorbs small `x` into a constant `B`, so `ψ(e^y) ≤ e^y + K e^y e^{−c√y} + B`
for all `y ≥ 0` (`exists_psi_exp_le_dlvp`). In the polar Schur bound (`polar_schur_le_of_psi_le`) the error at
distance `τ` of a window of length `L` costs `K e^{L/2} e^{−(L−τ)/2} e^{−c√τ}` against the polar weight
`φ = e^{−τ/2} + e^{−(L−τ)/2}`; the key inequality `e^{−(L−τ)/2} e^{−c√τ} ≤ (e^{−c√L/2} + e^{−L/4}) φ`
(`exp_neg_half_mul_exp_neg_sqrt_le`) is proved by cases: `τ ≥ L/4` (error factor `≤ e^{−c√L/2}`) and
`τ < L/4` (`e^{−(L−τ)/2} ≤ e^{−L/4} e^{−τ/2}`). Schur constant
`e^{L/2}(1 + 2K(e^{−c√L/2} + e^{−L/4})) + B + (1+L)²` (`abs_nodeArchEnergy_sub_weilEnergy_le_dlvp`);
the remainder terms are `≤ (4K + 1) e^{L/2 − (c/2)√L}` for large `L`
(`eventually_add_sq_le_exp_half_sub_sqrt`). Ceiling by `csSup_le`, floor by `le_csInf`, nonemptiness
from `eventually_exists_windowDeviation_ge`.

**M.** `zetaZeroWidth := sSup {|Re ρ − ½| : ρ ∈ zetaZeroConfig.carrier}`; bounded by `½` (open strip),
so `|Re ρ − ½| ≤ width` for every zero, and `width ≤ σ ⟺ ∀ρ, Re ρ ≤ ½ + σ` by the reflection
`ρ ↦ 1 − ρ̄` (`zetaZeroWidth_le_iff_re_le`). RH ⟺ width `= 0` via `riemannHypothesis_iff_zetaZeroConfig_onLine`.
Lag reading: compose with `zeta_re_le_iff_lag_primeWindow_ge_neg_exp`. Heat reading: a zero `w` of
`cosTransform riemannKernelReal = Ξ` has `ξ(½ + iw) = 0`, hence `½ + iw` is a nontrivial zero
(`xi_zero_re_mem_open_unit`, `xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial`), so `(Im w)² ≤ width²`;
`cosTransform_heat_zeros_im_sq_le` with `D = width²` gives the heat strip for `t > 0`, and `t = 0` is
`H_0 = Ξ` directly. Real-rootedness for `t ≥ width²/2` since then `max(width² − 2t, 0) = 0`.

**D.** `one_param_near_top_visible_at_explicit_lag` gives `v ∈ [0, V]` with `Re W(f_v, f_v) < 0`;
`ccmRestrictedWeilGroundEnergy_mul_le_re_W_twoBump` gives `μ(v/2 + w)·∫|f_v|² ≤ Re W < 0`, so
`μ(v/2 + w) < 0` (`∫|f_v|² ≥ 0`); `ccmRestrictedWeilGroundEnergy_antitone` carries it to every `A ≥ V/2 + w`.

## Opportunities surveyed and not built (with the reason)
- **Sharp width law for the window ceiling (`θ* = width` instead of `width ≤ θ* ≤ width/2 + 1/4`).**
  The Schur-weight method is pointwise and loses `e^{L/4}` at the window midpoint against power errors;
  the sharp bound needs the `L²` operator norm of the truncated error convolution, i.e. a Perron/explicit
  formula for `Σ_{n≤x} Λ(n) n^{−1/2−iξ}` uniform in `ξ` with the zeros summed with their decay. Not an
  assembly of existing theorems; a new analytic development.
- **Ground-energy rate law in the converse direction (`width ≤ σ ⟹ μ(A) ≥ −C e^{2σA}`).** The corpus has
  floor ⟹ width (`re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`) and the attained-top decay
  `μ₀(B) ≤ −c e^{2ΘB}/B³` (`ConstrainedWeilPolarGroundDecay`). The missing direction is a bound uniform
  over all tests of support `[−A, A]`, which the zero-side expansion gives only against the log-weighted
  (archimedean) energy, not against `‖f‖²`; the lag family avoids this because its test is fixed.
- **Rank-two pole correction of the polar ground-energy floor** (`μ₀ ≥ 1/20` through `(log 2 + 1/50)/2`
  on the codimension-two polar-constrained space, to an all-profile floor past `log 2/2`). The Schur
  complement needs `μ₀ · Ẑ(g_±) ≥ ‖Ẑ(·, g_±)‖²` for pole-moment generators `g_±`; the cross term is the
  archimedean operator applied to `g_±`, of size `≈ 2‖g‖`, against `μ₀ Ẑ(g) ≈ (1/20)(1/5000)‖g‖²`. Not
  available by assembly; this is the WP3 lane's territory in any case.
- **Walls 16/17: the dual-norm statistics `Λ_p(c')` read the signs the parity pair hides.** True in
  principle (the residue masses mod `2` of the half-damping parity pair differ in sign), but the
  `DualNormOfTheCrossScaleFunctional` objects and the `ParityPairAtHalfDamping` weights are built on
  different rows (large-scale row vs. damped weight); a faithful bridge needs the Gram of the parity pair
  itself. Recorded as a candidate.
- **Walls 14/3: `S(T)` unbounded + the local zero-count ceiling ⟹ windows with excess `B` zeros.** This
  confirms clustering rather than excluding it; no help against wall 3.

## What the three statements do not give
A: the gap to RH is unchanged (RH is `c(L) ≤ e^{L/2} + O(L)`; `e^{L/2−κ√L}` is `O(e^{θL})` for no `θ < ½`).
M: the heat time is bounded by the width, not conversely; nothing moves the width. D: the bound
`V₀/2 + w` on the contact aperture is far beyond every certified aperture (`V₀ ≥ 32/δ₀`); it is the
ground-energy transcription of the visibility law, vacuous under RH.

## Log
- 2026-10-21 — created in 3-formalized; three modules compiled (`lake env lean`), oleans built single-threaded (`lake --old env lean -j 1 -o … -i …`), axioms standard for all 15 declarations checked, umbrella imports appended. Bridge olean `GroundEnergyAbscissaAndLagGridAttainmentBridge` was missing and was built the same way.
- 2026-10-21 — per user rule (no unproven premises), the one-directional "rate ⟹ heat time" corollaries with a lag-floor or ground-energy-floor premise were removed from module M; the closed width theorems and the lag iff carry the content.
