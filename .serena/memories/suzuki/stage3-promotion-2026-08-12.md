# Suzuki stage-2 → 3 promotion session (2026-08-12)

Goal: promote every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki/`
(24 remained at session start; ledger = `_promotion/LEDGER.md` in that folder, count now 82/103).

## Promoted this session

`suzuki-gamma-weighted-tail-coercivity` — the section-4 weak-domain upgrade is now fully formal,
no Fourier anywhere. Card + certificate live in `3-formalized/new_scientific_knowledge/suzuki/`.

New Lean (all `[propext, Classical.choice, Quot.sound]`, wired into umbrellas):

- `HTGeometry/CompactKernelL2Convolution.lean` — g⋆V for compactly supported kernels vs L² profiles:
  deriv on kernel (bridged to mathlib `HasCompactSupport.hasDerivAt_convolution_left` via
  `lineConvolution_eq_convolution`), sup/Lipschitz bounds, L², L¹+L² translate moduli, support shift.
- `HTGeometry/GammaJumpL2Bound.lean` — L² scale majorant ν of the shifted second difference;
  `‖R_σP‖₂ ≤ ∫kν` by weighted CS + Tonelli in ℝ≥0∞ (`lintegral_sq_gammaScaleIntegral_le`,
  `integrable_sq_gammaScaleIntegral`); replaces continuous Minkowski AND the paper's Fourier step.
- `HTGeometry/L1FromWeightedL2.lean` — P, xP ∈ L² ⇒ P ∈ L¹ (Cauchy-kernel AM-GM).
- `HTGeometry/MollifierTestPairing.lean` — ∫(g⋆V)φ = ∫V ψ_g (one Fubini), IBP ψ_{ρ'} = −ψ_ρ[φ'],
  uniform modulus bound.
- `HTGeometry/SmoothCompactL2Dense.lean` — `smoothCompactSubmodule` of `Lp ℝ 2`, dense via
  mathlib `Lp.dense_hasCompactSupport_contDiff`.
- `RHTower/SuzukiGammaMollifiedEquation.lean` — `suzukiMollifier` family (scaled bump),
  `SuzukiGammaTestedEquation` (equation (5) tested), jump transpose lemmas, the jump Fubini
  `integral_mul_shiftedGammaJump_comp_sub`, and `suzukiGamma_mollified_equation` = (18) pointwise.
- `RHTower/SuzukiGammaWeakDomainUpgrade.lean` — U_ε property package, (20) mass identities,
  `suzukiGamma_uniform_energy_bound`, capstone `suzukiGamma_weakDomain_upgrade` (card's (6):
  U ∈ L²) and `suzukiGamma_profile_H1`.

## Traps confirmed this session (beyond the hubs)

- `.abs` on AEStronglyMeasurable → `Exists.abs`; route via continuity or Measurable.
- `integral_add/sub/neg` via `rw` fails against `Integrable.add/.sub/.neg`-produced Pi-operation
  types; bind integrability with explicitly-typed `have`s and use TERM-MODE calc steps.
- `filter_upwards`/`integral_congr_ae` goals are un-beta-reduced: always `show` the reduced form.
- `ContDiff.differentiable` now wants `n ≠ 0`; `1 ≤ ∞` needs `(by exact_mod_cast le_top)`;
  `ContDiffBump.contDiff_normed (n := ⊤)` with `unfold bumpMollifier` first.
- `AEStronglyMeasurable.integral_prod_left'` doesn't exist — swap via
  `Measure.measurePreserving_swap` then `.integral_prod_right'`.
- Big-context `nlinarith`/`linarith` can hit deterministic timeouts — extract closing arithmetic
  into tiny top-level lemmas (`sq_energy_close`, `sq_add_three_le`).
- `mul_le_mul_left'` deprecated → `mul_le_mul_right` (alias of new-name mul_le_mul_right).
- pow_le_pow_left → `pow_le_pow_left₀`; `integrableOn_const` gone → `continuousOn_const.integrableOn_compact`;
  `setIntegral_const` yields `μ.real s • c`, use `measureReal_def`.
- L2 inner: `MeasureTheory.L2.inner_def` + `RCLike.inner_apply, starRingEnd_apply, star_trivial`
  (+ `ring` — orientation flips).
- ℝ≥0∞ route beats Bochner bookkeeping: `enorm_integral_le_lintegral_enorm` holds unconditionally,
  `ofReal` never ⊤, so finiteness is free; transfer back via the Young-module toReal pattern.

## Next

Remaining 23 cards in section B of the ledger. The ledger's `EV` section lists shared named
infrastructure targets (Paley–Wiener strip translation, physical chart, Carleman kernel, ℓ²(Z^d)
+ Borel–Cantelli, valuation convolution/Neumann/Plancherel, unbounded multiplier a_a(D),
Hilbert-valued oscillatory Gamma, Matveev/Baker). Read each card's own `## Lean` section first —
four past promotions were already finished ("free promotions").
