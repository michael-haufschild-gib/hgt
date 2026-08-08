# Exterior branch of the constrained-prolate card: closed (2026-08-09)

Card: `docs/drafts/pipeline/2-fully-proven/nad/constrained-prolate-continuous-polar-charge-law.md`.
All modules wired into `GaloisForLFunctions/RHTower.lean`; both umbrellas build green; every
declaration axiom-clean.

## Headline

`RHTower.ExteriorDunsterPrimitive.norm_integral_exterior_dunster_le` has **no analytic
hypotheses** — only `0 ≤ s ≤ 1/2`, `c > 0`, `|eps| = 1`, `X ≥ 2`.  It states

    ‖∫_2^X xiAmplitude s t · (√t)⁻¹ · exp(i·eps·c·xiEndpointPhase s t) dt‖ ≤ 21 / c

uniformly in the endpoint `X`.  `(48)`, `(49)`, `(50)` are all proved theorems here.

## What the corpus ALREADY owned (checked before building — do not rebuild)

`CCMFirstRowStationaryPhase.lean` (namespace `GaloisForLFunctions.RHTower`):
`xiSpeed s t = √((t²−s)/(t²−1))`, `xiCompSpeed`, `xiEndpointPhase = ∫_1^x xiSpeed`,
`integral_xiCompSpeed = √(x²−1)`, `xiSpeed_le_xiCompSpeed`, **`xiEndpointPhase_bounds`**
(`√(1−s)√(x²−1) ≤ ξ ≤ √(x²−1)`), `hasDerivAt_xiEndpointPhase`, `hasDerivAt_xiSpeed`,
`continuousOn_xiSpeed`, `xiSpeedDeriv`, **`xiAmplitude`** (= Dunster's `(39)`) and
**`xiAmplitude_le`** (`A ≤ 2^{1/4}x^{-1/2}` — the amplitude half of `(48)`, already done).
`CCMFirstRowVanDerCorputBlocks.lean`: **`one_le_xiSpeed`** (first half of `(49)`), `xiSpeedDeriv_eq`.
`CCMRadialProlateDefect.lean`: `phaseLogDefect = ξ'/ξ − x/(x²−1)`,
**`abs_phaseLogDefect_le_far`** (`≤ x/(x²−1)`), `continuousOn_phaseLogDefect`, `nfWeight`.
`ProlateDunsterComparisonBridge.lean`: **`xiAmplitudeDeriv`**, `hasDerivAt_xiAmplitude`.
`CCMFirstRowEnvelopeTail.lean`: `continuousOn_xiAmplitude`, `continuousOn_xiEndpointPhase`.
`CCMFirstRowDunsterModel.lean`: `xiSpeed_pos`, `hasDerivAt_xiSpeedDeriv`, `xiEndpointPhase_le_of_le`.

## What I built

- `RHTower/OscillatoryDecayPrimitive.lean` (namespace **`RHTower`**, root) —
  `integral_inv_sq_le`, `norm_integral_cexp_le_of_decay`, `norm_integral_cexp_le_of_profile`.
- `RHTower/ExteriorProfileBounds.lean` (root `RHTower`) — `hasDerivAt_inv_sqrt`, `exteriorWeight`,
  `norm_exteriorProfile_le`, `norm_deriv_exteriorProfile_le`, `norm_integral_exterior_le`.
- `RHTower/XiReciprocalSpeed.lean` (`GaloisForLFunctions.RHTower`) — `hasDerivAt_inv_xiSpeed`,
  **`abs_deriv_inv_xiSpeed_le`** (`|(1/ξ')'| ≤ x^{-2}`, constant **one**) = second half of `(49)`.
- `RHTower/ExteriorXiPrimitive.lean` — `xiInvSpeedDeriv`, `continuousOn_xiInvSpeedDeriv`,
  `norm_integral_exterior_xiPhase_le` (phase side hypothesis-free).
- `RHTower/XiAmplitudeDecay.lean` — `sqrt_sqrt_two_le_two`, `abs_xiAmplitude_le_four`,
  **`abs_xiAmplitudeDeriv_le`** (`|A'| ≤ 4x^{-3/2}`) = derivative half of `(48)`.
- `RHTower/ExteriorDunsterPrimitive.lean` — `continuousOn_xiAmplitudeDeriv`,
  **`norm_integral_exterior_dunster_le`**.

## Namespace trap

The corpus uses **two** namespaces: root `RHTower` (VanDerCorput, ProlateWronskian, …) and
`GaloisForLFunctions.RHTower` (xiSpeed, Bessel, …).  Cross-reference with `_root_.RHTower.foo`.

## Still open on this card

- `(48)` *as an identity* — that `U_(n,λ)` equals the two-branch sum with these amplitudes.  The
  estimates on the terms are done; the expansion itself is not.
- `(47)`: needs the endpoint normalization `(37)`–`(38)`.
- The `h₀,h₄` spectral-occupancy gate (untouched; simplicity settles degeneracy, not occupancy).
- `(18)`, `(32)` promotion; true even ground/gap comparison; locally uniform determinant
  convergence to Xi; the true cofinal Weil floor.

## Traps

- `abs_add` is `abs_add_le`; `le_or_lt` is `le_or_gt`; `Real.pi_lt_315` does not exist
  (use `Real.pi_le_four`); `Complex.ofReal_mul_im` does not exist.
- After `field_simp`, `√x·√x` appears as `√x ^ 2`; close with `rw [Real.sq_sqrt hx.le]`
  (often *without* a following `ring` — check for "No goals").
- `lake env lean` reads imports' oleans: `lake build` a new module before a dependent file sees it.
