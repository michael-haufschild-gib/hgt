# Cold Malgrange alternation through order 15 (2026-08-25)

Extended `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallSexticMalgrangePositiveOrientation.lean` with an unconditional finite-range theorem.

For every `5 ≤ n ≤ 14`, proved `normalizedPrimeArchMoment n - normalizedPrimeArchMoment 0^(n+1)/2^n < 0`. Consequently `(-1)^(n+1)` times the real scalar all-order cold Malgrange target is positive, determining alternating orientations for jet orders 6 through 15.

Core reusable estimates: `xiShiftAbsoluteTail_le_schwarzPairRadius` gives `A_(s+k) ≤ (231/9769)^k A_s`; `abs_normalizedPrimeArchMoment_add_le_schwarzPairRadius_mul_xiShiftAbsoluteMass` transfers this to centered moments. At `s=1`, sector/source bounds give `A_1 < (42/41)(17/200000)`. Exact rational separation closes every index 5..14 against the source floor `m0 > 1/25`.

New declarations: `xiShiftAbsoluteTail_le_schwarzPairRadius`, `abs_normalizedPrimeArchMoment_add_le_schwarzPairRadius_mul_xiShiftAbsoluteMass`, `normalizedPrimeArchMoment_sub_firstJetScale_neg_of_five_le_of_le_fourteen`, `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_five_le_of_le_fourteen`.

Card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-finite-range-malgrange-alternation.md`.

Targeted direct module check passed cleanly; four new declarations use only `[propext, Classical.choice, Quot.sound]`. No umbrella build or lint sweep. Range ends at n=14; no extrapolation beyond.