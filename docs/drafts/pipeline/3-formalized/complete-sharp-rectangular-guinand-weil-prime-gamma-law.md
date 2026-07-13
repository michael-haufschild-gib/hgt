# Complete sharp rectangular Guinand--Weil prime--Gamma law

- **ID:** `complete-sharp-rectangular-guinand-weil-prime-gamma-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / exact explicit formula at piecewise-linear regularity
- **Scientific status:** `[PROVED] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY NEEDS AUDIT] [NOT AN RH PROOF]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula`

## Statement

Let `h_(L,a)` be the symmetric union of two length-`L` sharp intervals at aperture `a`, let
`R_(L,a)` be its autocorrelation, and let `Q_L(a)` be the complete multiplicity-counted Xi
polarization of its bilateral transform.  For `0 <= L <= a`,

```text
Q_L(a)
  = -2 * sum_{2 <= n <= exp(2a)} Lambda(n)/sqrt(n) * R_(L,a)(log n)
    + A_infinity(L,a),
```

where `A_infinity(L,a)` is the explicit absolutely convergent logarithmic derivative integral of
the completed archimedean factor on `Re(s)=3/2`.

No smoothing hypothesis, limiting smooth test family, finite spectral cutoff, unproved
sum--integral exchange, or simple-zero assumption occurs.  The identity is proved directly at
the sharp piecewise-linear regularity.

## Positive carrier consequence

After subtracting the Gamma integral and restoring the elementary polar square, the full spectral
value is exactly the finite prime--polar source:

```text
correctedXiWeilValue(L,a) = rectangularPrimePolarSourceCoefficient(L,a).
```

At `a = log(N)/2`, the autocorrelation splits into a fixed tent and one moving multiplicative
window supported in `N*exp(-2L) < n < N`.  Thus the complete divisor observable and the finite
arithmetic source are joined at the same cofinal aperture used by the RH energy spectrum.

## Proof architecture

1. Factor `XiC` on every closed symmetric depth-one rectangle and apply the weighted argument
   principle with analytic multiplicity.
2. Exhaust the complete copied Xi divisor by symmetric rectangles.
3. Prove absolute convergence of the bottom Xi logarithmic-derivative integral.
4. Select arbitrarily large zero-avoiding vertical edges whose resolvent integral is arbitrarily
   small; no zero-separation conjecture is used.
5. Split the bottom edge into the von Mangoldt and completed Gamma factors.
6. Evaluate the prime edge by exact Fourier inversion of the tilted sharp autocorrelation; compact
   support makes the prime-power sum finite.

## Principal declarations

```text
rectIntegral_rectangularLogDeriv_symmetric_eq_xiZeroCopy_sum
tendsto_symmetric_xiZeroCopy_rectangular_sum_atTop
tendsto_normalizedRectangularTruncatedBottomXiContribution_atTop
exists_large_integral_rectangular_mul_logDeriv_XiC_norm_lt
xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution
xiWeilPolarization_rectangular_eq_prime_add_arch
rectangularCorrectedXiWeilValue_eq_primePolarSource
rectangularPrimeAutocorrelationSum_logAperture
```

## Literature boundary

The finite Galerkin dictionary of Groskin, arXiv:2607.02828, identifies each truncated quadratic
value with a finite zero sum and controls an omitted archimedean tail.  The present theorem instead
removes the spectral rectangle and proves the complete sharp prime--Gamma identity itself.  The
classical Guinand--Weil formula is the parent mechanism, but its standard smooth test hypotheses do
not by themselves supply this exact sharp boundary theorem.  A line-by-line primary-literature
audit is still required before promotion from candidate-new to audited-new scientific knowledge.

## Gates

- [x] 0 -> 1: source-pure sharp profile and exact contour plan
- [x] 1 -> 2: complete paper proof with all limits exposed
- [x] 2 -> 3: exact Lean module build green
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] incorporated into the publication manuscript and claim trace
- [ ] primary-literature novelty audit at sharp piecewise-linear regularity
- [ ] independent specialist referee audit of the contour and Fourier normalizations
- [ ] 3 -> 4: promote after novelty audit and referee revisions
- [ ] RH
