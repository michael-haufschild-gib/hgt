# The sharp dyadic prime window is a corrected full Xi-Weil slope

- **ID:** `rectangular-xi-bottom-slope-dyadic-window-law`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / RH PROOF-BURDEN REDUCTION (Lean)
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Exact bottom-edge value

Let `B_Xi(L,a)` be the normalized absolutely convergent bottom-edge integral of the squared
rectangular transform against `XiC'/XiC`, and let `B_infinity(L,a)` be the corresponding
archimedean logarithmic-derivative integral.  Define

```text
V(L,a)=Re(B_Xi(L,a)-B_infinity(L,a))+2*P(L,a)^2,
```

where `P` is the elementary even polar feature.  Lean proves unconditionally

```text
V(L,a)=rectangularPrimePolarSourceCoefficient(L,a)       (0<=L<=a).
```

The proof uses the honest Euler-line Dirichlet series for `-zeta'/zeta`, sharp Fourier inversion
at piecewise-linear autocorrelation regularity, and an integrable Gamma majorant.  There is no
test-regularity interface, continuation hypothesis, zero-location hypothesis, or project axiom.

## Exact slope readout

Put `L_0=log(2)/2`, `a_n=log(n)/2`, and deform

```text
(L,a)=(L_0+t,(log(n)+t)/2).
```

This keeps the two-edge centre `a-L/2` fixed while opening the width.  If `D_+V(n)` denotes the
right derivative at `t=0`, Lean proves

```text
D_+V(n)
 = b_0
   +4*(1-1/sqrt(2))*sqrt(n)
   +4*(sqrt(2)-1)/sqrt(n)
   -2*W_closed(n),

b_0=8*(exp(log(2)/4)-exp(-log(2)/4)),
W_closed(n)=sum_(n/2<=k<=n) Lambda(k)/sqrt(k).
```

Since the requested half-open value `W(n)` satisfies `W(n)<=W_closed(n)`, the single value-slope
lower bound

```text
b_0+4*(sqrt(2)-1)/sqrt(n)-2*C_epsilon*n^epsilon <= D_+V(n)
```

implies exactly

```text
W(n)<=2*(1-1/sqrt(2))*sqrt(n)+C_epsilon*n^epsilon.
```

At this intermediate stage the arithmetic inequality is a lower bound for a literal corrected Xi
bottom-edge derivative.  No constant is lost; the closed-shell discrepancy is a nonnegative
endpoint atom.  The next section eliminates this intermediate contour value.

## Full spectral identification

Lean now also proves the missing infinite symmetric-contour passage.  The right vertical edge is
split into a finite near spectrum controlled by an integrated Cauchy cancellation and an
inverse-square summable far spectrum.  The resulting exact-multiplicity bound is

```text
O(R^(-1/2))*sum_q |p_q|^(-3/2) + O(R^(-1))*sum_q |p_q|^(-2),
```

and therefore vanishes on cofinal divisor-avoiding radii.  Absolute far-spectrum control plus
finiteness of the near spectrum justifies the sum--integral exchange.  Symmetric residue
exhaustion and bottom-edge convergence then give, unconditionally,

```text
xiWeilPolarization(T_(L,a),T_(L,a)) = B_Xi(L,a).
```

Consequently the corrected *full spectral value*

```text
Qcorr(L,a)=Re(xiWeilPolarization(T,T)-B_infinity(L,a))+2*P(L,a)^2
```

equals `rectangularPrimePolarSourceCoefficient(L,a)`, and its diagonal right derivative is the
same sharp dyadic shell displayed above.  The contour is no longer part of the remaining RH
burden.

## Lean implementation

```text
GaloisForLFunctions.RHTower.XiGuinandWeilRectangularArchimedean
  integrable_rectangularBottomArchIntegrand

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomEdge
  integrable_rectangularBottomXiLogDerivIntegrand
  normalizedRectangularBottomXiContribution_eq_prime_add_arch

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomSlope
  rectangularCorrectedBottomXiValue_eq_primePolarSource
  dyadicPrimePolarSourceDiagonalRightSlope_eq_closedShell
  hasDerivWithinAt_dyadicCorrectedBottomXiValue_diagonal_logSample
  dyadicWeightedPrimeWindow_upper_of_correctedBottomXiSlope_lower

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalResolvent
  exists_large_integral_rectangular_mul_logDeriv_XiC_norm_lt
  integral_tsum_xiRectangularVerticalRawTerm_eq_tsum_integral

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula
  xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution
  rectangularCorrectedXiWeilValue_eq_primePolarSource
  hasDerivWithinAt_dyadicCorrectedXiWeilValue_diagonal_logSample
  dyadicWeightedPrimeWindow_upper_of_correctedXiWeilSlope_lower
```

The focused build is green.  `#print axioms` for all capstone declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The formal lint gate passes.

## Remaining RH burden

The relation closes the prime/Gamma/bottom-edge identification, the full symmetric spectral
passage, and the transfer to the target dyadic window.  It does not supply the lower bound for the
corrected full Xi-Weil diagonal derivative.  The remaining sign/size statement is RH-bearing:
prove its one-sided all-epsilon subpower lower estimate.  Equivalently, control the
Gamma--polar correction strongly enough to transfer RH nonnegativity of the raw Weil value to
this derivative.

## Gates

- [x] sharp Fourier inversion at rectangular autocorrelation regularity
- [x] absolute integrability of the Gamma bottom edge
- [x] exact normalized Xi bottom-edge prime/Gamma splitting
- [x] corrected bottom edge equals the finite prime--polar source
- [x] corrected-bottom diagonal derivative reads the closed dyadic shell
- [x] direct corrected-slope-to-requested-window theorem
- [x] integrated near-spectrum Cauchy cancellation
- [x] inverse-square far-spectrum domination and sum--integral exchange
- [x] cofinal divisor-avoiding vertical-edge vanishing
- [x] infinite symmetric-contour and residue exhaustion
- [x] full sharp rectangular Guinand--Weil identity
- [x] corrected full Xi-Weil slope reads the dyadic shell
- [x] focused build, axiom audit, and formal lint
- [ ] unconditional one-sided subpower lower bound for the spectral slope
- [ ] RH
