# Sharp prime--Gamma RH spectrum

- **ID:** `sharp-prime-gamma-rh-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-only horizontal Xi-divisor spectrum
- **Scientific status:** `[PROVED] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY NEEDS AUDIT] [NOT AN RH PROOF]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum`

## Statement

For a fixed width `L > 0`, define the explicit arithmetic sample

```text
g_L(n)
  = -2 * rectangularPrimeAutocorrelationSum(L, log(n)/2)
    + Re(normalizedRectangularBottomArchContribution(L, log(n)/2)).
```

The prime sum is finite, supported on prime powers at most `n`, and the second term is the
absolutely convergent completed Gamma integral.  For every cutoff `N` such that

```text
n >= N  =>  1 <= n and L <= log(n)/2,
```

the following hold unconditionally.

1. `g_L(n)` is exactly the sharp rectangular Xi-Weil sample on the whole retained tail.
2. RH is equivalent to `g_L(n) >= 0` for every `n >= N`.
3. For each `alpha >= 0`, every Xi zero satisfies
   `Re(rho) <= 1/2 + alpha` exactly when the negative tail `g^-_(L,N)` is summable at every
   Dirichlet abscissa `1 + alpha + epsilon`, `epsilon > 0`.
4. The absolute-convergence abscissa of `g^-_(L,N)` is `-infinity` under RH and exactly
   `1 + xiRightTransverseSup` under false RH.
5. Consequently RH is equivalent to this abscissa being `-infinity`, and also equivalent to it
   being at most one.

This is an exact RH criterion and horizontal-divisor tomography theorem.  It is not an RH proof:
the theorem does not establish tail nonnegativity or the critical abscissa bound.

## Positive carrier form

The obstruction has a positive formulation.  A successful Connes/Weil realization is forced to
carry a positive majorant of the explicit source negative mass whose abscissa is at most
`1 + alpha`; at `alpha = 0` this proves RH.  Under false RH the required aggregate payment is
exactly `1 + xiRightTransverseSup`.

## Principal declarations

```text
xiRectangularPrimeGammaLogCoefficient
xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
xiRectangularPrimeGammaTailCoefficient_eq_weilTail_re
xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart
riemannHypothesis_iff_primeGammaLogCoefficient_tail_nonneg
xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove
ccmPrimeGammaSourceDivisorEnergySpectrum_capstone
riemannHypothesis_iff_ccmPrimeGammaSourceDivisorEnergyEndpoint
xiRectangularPrimeGammaTailNegativePart_abscissa_dichotomy
riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_eq_bot
riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one
```

## Proof architecture

1. Apply the complete sharp rectangular Guinand--Weil formula at `a = log(n)/2`.
2. Take real parts to identify the explicit prime--Gamma coefficient with the actual Weil sample.
3. Use fixed-window cofinal completeness to turn eventual source nonnegativity into RH.
4. Transport the exact negative-energy and abscissa spectra through pointwise coefficient
   equality.
5. Translate the zero endpoint by functional-equation symmetry.

## Gates

- [x] complete sharp prime--Gamma identity proved in Lean
- [x] source coefficient contains no zero or target-divisor data
- [x] pointwise source/observable equality proved in Lean
- [x] exact RH tail-sign criterion proved in Lean
- [x] quantitative half-plane energy spectrum proved in Lean
- [x] unconditional abscissa dichotomy proved in Lean
- [x] exact module build green
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] incorporated into manuscript and claim trace
- [ ] primary-literature novelty audit of the complete sharp boundary theorem and fixed-width
  arithmetic sampling consequence
- [ ] independent specialist audit of analytic normalizations and the prose/Lean definition map
- [ ] proof of one critical source estimate
- [ ] RH
