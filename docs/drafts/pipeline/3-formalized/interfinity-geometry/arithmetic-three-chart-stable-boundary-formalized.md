# Arithmetic three-chart stable boundary — formalized

- **ID:** `arithmetic-three-chart-stable-boundary-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `arithmetic-three-chart-stable-boundary.md`
- **Umbrella import:** `GaloisForLFunctions.RHTower`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/RHTower/ArithmeticMixedRateStableQuotient.lean` | the prime-depth cochain slice, the mixed rate functional, and the stable quotient `≃ₗ ℝ` |
| `formal/GaloisForLFunctions/RHTower/ArithmeticThreeChartStableBoundary.lean` | the three chart witnesses and the boundary identity |

## Audited declarations

Namespace `RHTower`.

- `tendsto_mixedRatio_of_base` — the mixed rate is independent of the base prime;
- `mixedRate_surjective`, `mixedRateQuotientEquiv` — the stable-primitive quotient of the radial
  slice is linearly isomorphic to `ℝ`, with the mixed rate as the isomorphism;
- `subsingleton_radialSlice_ordinaryH` — the ordinary quotient is trivial, so the whole invariant
  lives in the stable refinement;
- `arithmetic_three_chart_identity` — the three-chart identity relating the mass, clock and
  triangle witnesses to `1 − 2 Re s`;
- `mixedRateQuotientEquiv_sourceChartClass_reflection` — the reflection antisymmetry;
- `mixedRateQuotientEquiv_sourceChartClass_eq_zero_iff` and `sourceChartClass_eq_zero_iff` — the
  class vanishes exactly on the critical line `Re s = 1/2`.

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.RHTower
```

## Boundary

`Nat.Primes` carries no order instance in this toolchain, so the cofinal prime limit is taken along
`Filter.comap (↑·) atTop`, which is `NeBot` by an explicit instance.  The statement proved is the
card's boundary identity; it is a re-encoding of the critical line, not a proof of RH.
