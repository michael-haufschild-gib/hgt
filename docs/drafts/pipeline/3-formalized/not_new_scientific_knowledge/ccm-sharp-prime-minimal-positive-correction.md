# Sharp-prime minimal positive-correction law

- **ID:** `ccm-sharp-prime-minimal-positive-correction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / Connes--CCM positive-carrier optimization
- **Scientific status:** `[PROVED] [FORMALIZED] [STRUCTURAL BRIDGE] [NOT AN RH PROOF]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.CCMSharpPrimeWindowMinimalPositiveCorrection`

## Theorem

Let

```text
c(n) = 4(1 - 1/sqrt(2)) sqrt(n) - 2 W(n),
W(n) = sum_{n/2 < k <= n} Lambda(k)/sqrt(k),
E(n) = (W(n) - 2(1 - 1/sqrt(2))sqrt(n))_+.
```

Call `a : N -> R` an admissible positive correction when

```text
a(n) >= 0,
c(n) + a(n) >= 0
```

for every `n`. Then the canonical negative channel

```text
c^-(n) = 2 E(n)
```

is admissible and is the least admissible correction in pointwise order. Hence every
admissible `a` satisfies

```text
c^-(n) <= a(n),
sigma_abs(c^-) <= sigma_abs(a).
```

For every extended-real threshold `x`,

```text
there exists an admissible a with sigma_abs(a) <= x
iff
sigma_abs(c^-) <= x.
```

Thus auxiliary positive channels do not reduce the analytic cost of correcting the signed
sharp-prime source.

The canonical correction also has the unconditional square-root ceiling

```text
sigma_abs(c^-) <= 3/2.
```

Hence the feasible correction spectrum is always nonempty at `3/2`.  Under false RH this combines
with the forced-divergence spectrum to give the sharp unconditional interval

```text
1 + xiRightTransverseSup <= sigma_abs(c^-) <= 3/2.
```

## Quantitative Xi consequence

For `alpha >= 0`, any admissible correction satisfying

```text
sigma_abs(a) <= 1 + alpha
```

forces every Xi zero to satisfy

```text
Re(rho) <= 1/2 + alpha.
```

At `alpha = 0`, the same bound proves RH. Critical all-epsilon Dirichlet summability of any
admissible correction also proves RH.

Conversely, under false RH, every admissible correction fails absolute Dirichlet summability at
every real abscissa `1+alpha` with

```text
0 <= alpha < xiRightTransverseSup.
```

Thus the complete positive-correction architecture is forced to retain the actual transverse
divisor exponent.

## Principal declarations

```text
dyadicSharpPrimeSourceNegativePart_isLeastPositiveCorrection
exists_dyadicSharpPositiveCorrection_abscissa_le_iff
dyadicSharpPrimeSourceNegativePart_abscissa_le_three_halves
exists_dyadicSharpPositiveCorrection_abscissa_le_three_halves
exists_dyadicSharpPositiveCorrectionEnergy_iff_negativePartEnergy
xiZeroHalfPlaneBound_of_dyadicSharpPositiveCorrection_abscissa
not_dyadicSharpPositiveCorrection_summable_below_transverseSup_of_not_rh
transverseSup_le_dyadicSharpPrimeSourceNegativePart_abscissa_of_not_rh
dyadicSharpPrimeSourceNegativePart_abscissa_interval_of_not_rh
riemannHypothesis_of_dyadicSharpPositiveCorrection_abscissa_le_one
dyadicSharpPrimePositiveCorrectionAbscissaSpectrum_capstone
```

## Boundary

The theorem proves optimality inside the cone of coefficientwise nonnegative corrections. It
does not establish that the canonical correction has abscissa at most one. That estimate is the
remaining RH-bearing arithmetic input. The least-element argument is elementary order theory;
its significance is the exact identification `c^- = 2E` and its connection to the formalized
Landau/Xi transfer, so the result is classified as structural bridge infrastructure rather than
independent new scientific knowledge.

## Gates

- [x] exact negative-part/positive-excess identity
- [x] canonical correction admissible
- [x] pointwise least-correction theorem
- [x] abscissa minimality
- [x] exact feasible-abscissa sublevel law
- [x] unconditional `3/2` correction ceiling
- [x] quantitative Xi half-plane transfer
- [x] false-RH forced divergence spectrum
- [x] false-RH correction-abscissa interval
- [x] critical-abscissa RH corollary
- [x] unconditional Lean proof
- [ ] prove the critical arithmetic abscissa bound
- [ ] RH
