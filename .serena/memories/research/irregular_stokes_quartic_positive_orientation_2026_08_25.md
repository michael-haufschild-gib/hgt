# Fourth cold Malgrange orientation formalized (2026-08-25)

Applied existing all-order irregular-RH cold-wall law to next open datum, without editing read-only frontier map.

## New result
Let `u_j = thetaCuspNormalizedEvenMoment j`, `m_j = normalizedPrimeArchMoment j`.
Order-seven recurrence:
`m3 = -u4/5040 + u1*u3/180 + u2^2/144 - u1^2*u2/12 + u1^4/8`.
Thus
`m3 - m0^4/8 = (-u4 + 28u1u3 + 35u2^2 - 420u1^2u2)/5040 < 0`.
Existing cold all-order Malgrange law at n=3 has exact real scalar target
`-3*(m3-m0^4/8)>0`: fourth cold Malgrange orientation is positive.

Proof uses strict factorial-normalized theta moment contraction `u2 < 6u1^2` and Stieltjes log-convexity `u3^2 <= u2*u4`. Multiplying polynomial by positive `u2` and completing square:
`u2 P <= -(u3-14u1u2)^2 + 35u2^3 -224u1^2u2^2 <0`.

## Files
- New Lean module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuarticMalgrangePositiveOrientation.lean`
- Supporting theorem added to prior module: `thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq`
- Stage3 card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-quartic-malgrange-positive-orientation.md`
- Umbrella import added, no umbrella build.
- Frontier map untouched.

## Verification
Direct Lean check passed. Direct .olean emission passed. Axiom audit of four created public theorems: only `propext`, `Classical.choice`, `Quot.sound`.
A targeted Lake dependency build for ColdAllOrder unexpectedly expanded into a 13k-job replay and was terminated; do not repeat. No Lean processes remained.
