# Suzuki critical aperture quarter-shift current — formalized core certificate

## Status

`[LEAN-PROVED CORE] [UNCONDITIONAL] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`

## Paper source

`./suzuki-critical-aperture-quarter-shift-current.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/SuzukiCriticalApertureQuarterShiftCurrent.lean`

## Formal theorem surface

- `suzukiCriticalApertureBoundaryAtom_succ`: actual Gamma-boundary/innovation atom has exact fixed
  quarter-shift depth ratio.
- `norm_suzukiCriticalApertureDepthRatio_lt_one`: positive aperture makes ratio strictly
  contractive.
- `suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow`: exact geometric depth law.
- `summable_suzukiCriticalApertureBoundaryAtom`: valuation-depth current is summable.
- `tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent`: exact source resolvent `T_0/(1-rho)`.

## Scientific result

Critical Gamma boundary is not a standalone Hilbert vector, but actual source pairing with
true-aperture innovation completes exactly as contractive quarter-shift resolvent.  This supplies
first corpus-native power-scale critical mechanism and fixes Gamma/aperture subchannel of marked
Weil--Robin frontier.

Absolute completion over primes is paper-proved and remains Lean gate; certificate claims exact
per-prime depth core only.  RH is not claimed proved.

## Verification

- Direct Lean check passed.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or RH premise.
- Forbidden-token scan: clean.
- Final targeted build passed:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (`9450/9450`).
- Repository lint reached module but remains red on six unrelated concurrent unreachable modules.

## Prime completion (added)

`formal/GaloisForLFunctions/RHTower/SuzukiCriticalAperturePrimeCurrent.lean` closes the remaining
analytic gate.  It defines the closed per-prime current

```text
suzukiCriticalApertureQuarterShiftCurrent h a t p = ∑' e, T_e(h,a,t;p)
```

and the cofinal current `suzukiCriticalApertureCofinalCurrent h a t`, and proves unconditionally,
for every `h>0`, `a>0` and every real height `t`:

```text
norm_suzukiCriticalApertureBoundaryAtom_zero_le        ‖T_0‖ ≤ (h√h)⁻¹ √(log p) p^(-5/4)
norm_suzukiCriticalApertureDepthRatio_le_quarter       ‖rho‖ ≤ exp(-(log 2)/4)
norm_suzukiCriticalApertureDepthResolvent_le           ‖(1-rho)⁻¹‖ ≤ (1-exp(-(log 2)/4))⁻¹
norm_suzukiCriticalApertureQuarterShiftCurrent_le      ‖C(p)‖ ≤ K_h √(log p) p^(-5/4)
sqrt_log_le_two_mul_rpow                               √(log x) ≤ 2 x^(1/8), x ≥ 1
norm_suzukiCriticalApertureQuarterShiftCurrent_le_rpow ‖C(p)‖ ≤ 2K_h p^(-9/8)
summable_norm_suzukiCriticalApertureQuarterShiftCurrent
summable_suzukiCriticalApertureQuarterShiftCurrent
hasSum_suzukiCriticalApertureCofinalCurrent
norm_suzukiCriticalApertureCofinalCurrent_le
```

`hasSum_...` is the exhaustion-independence claim of the paper card.  Axiom audit of all eleven
declarations: `propext`, `Classical.choice`, `Quot.sound` only.
