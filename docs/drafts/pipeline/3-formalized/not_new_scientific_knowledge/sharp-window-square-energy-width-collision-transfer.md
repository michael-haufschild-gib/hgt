# Sharp-window and square-energy width-collision transfer

- **ID:** `sharp-window-square-energy-width-collision-transfer`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (Lean) / NOT NEW SCIENTIFIC KNOWLEDGE`
- **Statement:** a Chebyshev error exponent transfers unconditionally to both the pointwise sharp
  dyadic window spectrum and the square-aperture positive-excess-square abscissa; either resulting
  upper spectrum recovers the corresponding Xi half-plane width.

## Formal module

```text
formal/GaloisForLFunctions/RHTower/
  CCMSharpPrimeWindowSquareEnergyWidthCollision.lean
```

Umbrella:

```text
formal/GaloisForLFunctions/RHTower.lean
```

## Formalized chain

For

```text
ChebyshevErrorPowerSpectrum alpha :=
  forall epsilon>0,
  exists C>=0,
  forall x>=1,
    |psi(x)-x| <= C x^(1/2+alpha+epsilon),
```

Lean proves:

```text
ChebyshevErrorPowerSpectrum alpha
  -> DyadicWeightedPrimeWindowPowerUpper alpha 2
  -> XiZeroHalfPlaneBound alpha,
```

and independently

```text
ChebyshevErrorPowerSpectrum alpha
  -> abscissa(square positive-excess squared) <= 1+4alpha
  -> XiZeroHalfPlaneBound alpha.
```

When `XiRightZeroCopy` is nonempty and the Chebyshev spectrum is supplied at intrinsic width,
Lean proves exact equality

```text
abscissa(square positive-excess squared)
  = 1+4*xiRightTransverseSup.
```

At `alpha=0`,

```text
DyadicWeightedPrimeWindowPowerUpper 0 N
  <-> DyadicWeightedPrimeWindowSubpowerUpper N,
```

and the Chebyshev spectrum implies RH through the square-energy endpoint.

## Main declarations

- `ChebyshevErrorPowerSpectrum`
- `dyadicCriticalMellinErrorIncrement_abs_le_of_chebyshevErrorPower`
- `squarePrimeWindowCenteredDeviation_eq_errorIncrement`
- `squarePrimeWindowPositiveExcess_le_errorIncrement_abs`
- `squarePrimeWindowPositiveExcessSquare_coefficient_norm_le`
- `squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum`
- `DyadicWeightedPrimeWindowPowerUpper`
- `dyadicWeightedPrimeWindowPowerUpper_zero_iff_subpowerUpper`
- `dyadicWeightedPrimeWindowPowerUpper_of_chebyshevErrorPowerSpectrum`
- `xiZeroHalfPlaneBound_of_dyadicWeightedPrimeWindowPowerUpper`
- `xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum`
- `squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth`
- `riemannHypothesis_of_chebyshevErrorPowerSpectrum_zero`

## Scope and ownership

All declarations are unconditional Lean theorems: analytic estimates appear as ordinary theorem
hypotheses, never axioms. The classical generalized von Koch implication

```text
XiZeroHalfPlaneBound alpha -> ChebyshevErrorPowerSpectrum alpha
```

is paper-proved and externally owned, but not present in the Lean library. Therefore this card
certifies every new downstream transfer and reverse-width result, not a fictitious assumption-free
formal proof of generalized von Koch or RH.

Paper proofs:

- `../../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/sharp-dyadic-prime-window-zero-width-collision.md`
- `../../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/square-aperture-positive-excess-zero-width-collision.md`

## Gates

- [x] direct `lake env lean` check
- [x] module wired into umbrella
- [x] no computation
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] targeted
  `lake build GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergyWidthCollision`
- [x] `#print axioms` audit: `[propext, Classical.choice, Quot.sound]`
- [x] formal lint recognizes module as umbrella-reachable; repository-wide lint remains red only
  for five unrelated unreachable modules

## Log

- 2026-08-01 — Abel, pointwise, square-energy, abscissa, and reverse-width chain formalized.
- 2026-08-01 — direct check, targeted module build, umbrella wiring, and axiom audit pass.
