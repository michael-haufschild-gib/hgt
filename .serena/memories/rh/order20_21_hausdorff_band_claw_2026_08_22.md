# Endpoint-calibrated Hausdorff order-20 band and order-21 mixed claw (2026-08-22)

## Formalized results
- `formal/GaloisForLFunctions/RHTower/PrimeArchOrderTwentyHausdorffSourceBand.lean` proves unconditional scaled endpoint Hausdorff nonnegativity for every `k ≤ 19`, `r ≤ 57`, using twentieth-power positivity and opposite-phase complement. It defines the exact tail carrier and proves its equivalence to `riemannHypothesis`.
- `formal/GaloisForLFunctions/RHTower/PrimeArchOrderTwentyOneMixedHausdorffClaw.lean` proves a stronger mixed claw on the unresolved pure order-21 row: `k = 20`, `22 ≤ r ≤ 57`.

## Residual geometry used by mixed claw
For any order-21 residual Xi zero-copy reciprocal-square atom `z`:
- `1/3000 < |z.im|`.
- `1/182 < z.re`.
- `1/130 < |(1/4 - z).im| / (1/4 - z).re`.
Together with cubic arctan lower bound and the residual 21st-power sector, 22 endpoint-complement factors force nonnegative real part.

## Exact remaining RH-equivalent tail
`PrimeArchEndpointOrderTwentyOneMixedClawTailNonnegative` quantifies only:
- `20 < k`, or
- `57 < r`, or
- `k = 20 ∧ r < 22`.
Its nonnegativity is equivalent to RH. Thus the corpus does not prove or refute RH; it isolates the remaining carrier exactly.

## Verification
Both modules compile with this toolchain. `#print axioms` for the residual bounds, atom/source claw, and RH-equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` appears in either module. Global lint was blocked by unrelated concurrently changing unreachable modules and stale generated indexes.
